module

public import Kraken.BitVecArith
public import Kraken.Mem
public import Kraken.Separation
public import Kraken.SeparationMem
public meta import Lean.Elab.Tactic
public meta import Lean.Meta.Tactic.AC
public meta import Lean.Meta.Tactic.Grind
public meta import Lean.Elab.Tactic.Omega

public meta section

open Lean Elab Tactic Meta

namespace Kraken.Tactic

private partial def denoteClauses (predType : Expr) : List Expr → MetaM Expr
  | [] => withLocalDeclD `m predType.bindingDomain! fun m => do
      let body ← mkAppM ``Std.ExtHashMap.emp #[m]
      mkLambdaFVars #[m] body (etaReduce := true)
  | [p] => return p
  | p :: ps => do
    let rest ← denoteClauses predType ps
    mkAppM ``Std.ExtHashMap.sep #[p, rest]

private partial def reduceProjectionApp (e : Expr) : MetaM Expr := do
  let e ← withConfig (fun c => { c with zetaDelta := false }) (whnfCore e.headBeta)
  let some declName := e.getAppFn.constName? | return e
  let some info ← getProjectionFnInfo? declName | return e
  if info.fromClass then
    unless declName == ``HasDataMem.dmem || declName == ``HasDataMem.withDmem do
      return e
    let some unfolded ← withTransparency .instances (unfoldProjInst? e) | return e
    return ← reduceProjectionApp unfolded.headBeta
  let args := e.getAppArgs
  if h : info.numParams < args.size then
    let major ← reduceProjectionApp args[info.numParams]
    let e := mkAppN e.getAppFn (args.set info.numParams major)
    let some unfolded ← unfoldDefinition? e | return e
    let some fn ← reduceProj? unfolded.getAppFn | return e
    reduceProjectionApp (mkAppN fn unfolded.getAppArgs)
  else
    return e

inductive SepTree where
  | emp (e : Expr)
  | sep (e : Expr) (p q : SepTree)
  | atom (e : Expr)

def SepTree.toExpr : SepTree → Expr
  | .emp e | .sep e _ _ | .atom e => e

def SepTree.numClauses : SepTree → Nat
  | .emp _ => 0
  | .sep _ p q => p.numClauses + q.numClauses
  | .atom _ => 1

def SepTree.clauses : SepTree → List Expr
  | .emp _ => []
  | .sep _ p q => p.clauses ++ q.clauses
  | .atom e => [e]

partial def parseSepTree (e : Expr) : MetaM SepTree := do
  let e ← reduceProjectionApp (← instantiateMVars e)
  if e.getAppFn.constName? == some ``Std.ExtHashMap.emp then
    return .emp e
  if e.getAppFn.constName? == some ``Std.ExtHashMap.sep then
    let args := e.getAppArgs
    let p ← parseSepTree args[args.size - 2]!
    let q ← parseSepTree args[args.size - 1]!
    return .sep e p q
  return .atom e

private inductive LeafExtract where
  | single (a : Expr) (h : Expr)
  | split (a : Expr) (rem : Expr) (h : Expr)

private partial def extractSepTreeAux (t : SepTree) (targetIdx : Nat)
    (atLeaf : Expr → MetaM LeafExtract) : MetaM (Option LeafExtract) := do
  match t with
  | .emp _ => return none
  | .atom e =>
    if targetIdx == 0 then
      return some (← atLeaf e)
    else
      return none
  | .sep _ p q =>
    let pCount := p.numClauses
    if targetIdx < pCount then
      let some res ← extractSepTreeAux p targetIdx atLeaf | return none
      match res with
      | .single a hp =>
        let h ← mkAppM ``Std.ExtHashMap.sep_extract_head #[q.toExpr, hp]
        return some (.split a q.toExpr h)
      | .split a p' hp =>
        let rem ← mkAppM ``Std.ExtHashMap.sep #[p', q.toExpr]
        let h ← mkAppM ``Std.ExtHashMap.sep_extract_left #[q.toExpr, hp]
        return some (.split a rem h)
    else
      let some res ← extractSepTreeAux q (targetIdx - pCount) atLeaf | return none
      match res with
      | .single a hq =>
        let h ← mkAppM ``Std.ExtHashMap.sep_extract_tail #[p.toExpr, hq]
        return some (.split a p.toExpr h)
      | .split a q' hq =>
        let rem ← mkAppM ``Std.ExtHashMap.sep #[p.toExpr, q']
        let h ← mkAppM ``Std.ExtHashMap.sep_extract_right #[p.toExpr, hq]
        return some (.split a rem h)

/--
Extracts (or splits and extracts) the leaf at `targetIdx` from `t` along the binary tree path
in $O(\text{depth})$ steps without calling `denoteClauses`, `rebuildSepTree`, or
`AC.rewriteUnnormalizedRefl`. Returns `(extractedClause, frameExpr, eqProof)` where
`eqProof : t.toExpr = extractedClause ⋆ frameExpr`.
-/
private def extractSepTree (t : SepTree) (targetIdx : Nat)
    (atLeaf : Expr → MetaM LeafExtract) : MetaM (Option (Expr × Expr × Expr)) := do
  let some res ← extractSepTreeAux t targetIdx atLeaf | return none
  match res with
  | .split a frame h => return some (a, frame, h)
  | .single a h =>
    let h' ← mkAppM ``Std.ExtHashMap.sep_extract_here #[h]
    let eqType ← inferType h'
    let frame := eqType.appArg!.appArg!
    return some (a, frame, h')

/--
Rebuilds a separation predicate from its parsed `SepTree` while replacing each
atomic leaf, from left to right, with the next entry in `clauses`.
Each entry in `clauses` pairs a canonical replacement expression `c` with an
optional equality proof `eqProof? : c = origLeaf`; these equality proofs are
lifted through `Std.ExtHashMap.sep` via congruence.
If a leaf was a naked metavariable assigned during cancellation, recursively
parses and rebuilds its assigned value.
-/
private partial def rebuildSepTree (t : SepTree) (clauses : List (Expr × Option Expr)) :
    MetaM (Option (Expr × Option Expr × List (Expr × Option Expr))) := do
  match t with
  | .emp e => return some (e, none, clauses)
  | .sep _ p q =>
    let some (p', hp?, clauses) ← rebuildSepTree p clauses | return none
    let some (q', hq?, clauses) ← rebuildSepTree q clauses | return none
    let sep' ← mkAppM ``Std.ExtHashMap.sep #[p', q']
    let hSep? ← match hp?, hq? with
      | none, none => pure none
      | some hp, none =>
        let h1 ← mkCongrArg sep'.appFn!.appFn! hp
        some <$> mkCongrFun h1 q'
      | none, some hq =>
        some <$> mkCongrArg sep'.appFn! hq
      | some hp, some hq =>
        let h1 ← mkCongrArg sep'.appFn!.appFn! hp
        some <$> mkCongr h1 hq
    return some (sep', hSep?, clauses)
  | .atom e =>
    if let .mvar mvarId := e then
      if ← mvarId.isAssigned then
        return ← rebuildSepTree (← parseSepTree e) clauses
    match clauses with
    | (c, eqProof?) :: rest => return some (← instantiateMVars c, eqProof?, rest)
    | [] => return none

private def shouldNotUnfoldInMatchClosed (fn : Expr) : Bool :=
  match fn.constName? with
  | some n =>
    n == ``Int.toBytes || n == ``Int.ofBytes ||
    n == ``Nat.toBytes || n == ``Nat.ofBytes ||
    (`BitVec).isPrefixOf n || (`List).isPrefixOf n ||
    (`HAdd).isPrefixOf n || (`Add).isPrefixOf n ||
    (`HSub).isPrefixOf n || (`Sub).isPrefixOf n ||
    (`HAppend).isPrefixOf n || (`Append).isPrefixOf n
  | none => false

-- fuel: bound definitional unfolding to avoid expensive general reduction.
private partial def matchClosed (lhs rhs : Expr) (fuel : Nat := 2) : MetaM Bool := do
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  if lhs == rhs then return true
  if lhs.isMVar || rhs.isMVar then return ← isDefEq lhs rhs
  let lhs ← reduceProjectionApp lhs
  let rhs ← reduceProjectionApp rhs
  if lhs == rhs then return true
  if !lhs.hasFVar && !rhs.hasFVar && !lhs.hasExprMVar && !rhs.hasExprMVar then
    return ← isDefEq lhs rhs
  if lhs.isFVar then
    if let some val ← lhs.fvarId!.getValue? then
      return ← matchClosed val rhs fuel
  if rhs.isFVar then
    if let some val ← rhs.fvarId!.getValue? then
      return ← matchClosed lhs val fuel
  if lhs.getAppFn == rhs.getAppFn then
    let lhsArgs := lhs.getAppArgs
    let rhsArgs := rhs.getAppArgs
    unless lhsArgs.size == rhsArgs.size do return false
    for lhsArg in lhsArgs, rhsArg in rhsArgs do
      unless ← matchClosed lhsArg rhsArg fuel do return false
    return true
  if fuel == 0 then
    return false
  unless shouldNotUnfoldInMatchClosed lhs.getAppFn do
    if let some lhs ← unfoldDefinition? lhs then
      if ← matchClosed lhs rhs (fuel - 1) then return true
  unless shouldNotUnfoldInMatchClosed rhs.getAppFn do
    if let some rhs ← unfoldDefinition? rhs then
      if ← matchClosed lhs rhs (fuel - 1) then return true
  return false

private def matchAtom (lhs rhs : Expr) : MetaM Bool := do
  if lhs.hasExprMVar || rhs.hasExprMVar then
    commitWhen (matchClosed lhs rhs)
  else
    matchClosed lhs rhs

def extractAtBytesAndAddr? (clause : Expr) : MetaM (Option (Expr × Expr)) := do
  let clause ← instantiateMVars clause
  unless clause.isAppOfArity ``Eq 2 do return none
  let rhs ← reduceProjectionApp clause.appArg!
  if rhs.isAppOfArity ``List.At 3 then
    return some (← reduceProjectionApp rhs.appFn!.appArg!, ← reduceProjectionApp rhs.appArg!)
  if rhs.isAppOfArity ``UInt64.At 3 then
    let v ← reduceProjectionApp rhs.appFn!.appArg!
    return some (← mkAppM ``UInt64.toBytes #[v], ← reduceProjectionApp rhs.appArg!)
  if rhs.isAppOfArity ``UInt32.At 3 then
    let v ← reduceProjectionApp rhs.appFn!.appArg!
    return some (← mkAppM ``UInt32.toBytes #[v], ← reduceProjectionApp rhs.appArg!)
  if rhs.isAppOfArity ``UInt16.At 3 then
    let v ← reduceProjectionApp rhs.appFn!.appArg!
    return some (← mkAppM ``UInt16.toBytes #[v], ← reduceProjectionApp rhs.appArg!)
  if rhs.isAppOfArity ``UInt8.At 3 then
    let v ← reduceProjectionApp rhs.appFn!.appArg!
    return some (← mkAppM ``UInt8.toBytes #[v], ← reduceProjectionApp rhs.appArg!)
  return none

private def isCalleeSavedEqType (t : Expr) : Bool :=
  match t.consumeMData.getAppFn'.constName? with
  | some n => (`Reg64s.CalleeSavedEq).isSuffixOf n
  | none => false

/-- Simp lemmas normalising byte-list lengths (`List.length_drop`, `Int.toBytes_length`, …). -/
def lengthSimpLemmas : List Name :=
  [``List.length_drop, ``List.length_take, ``List.length_append, ``List.length_replicate,
   ``List.length_cons, ``List.length_nil, ``List.length_map, ``List.length_reverse,
   ``Int.toBytes_length, ``Nat.toBytes_length, ``UInt8.toBytes_length, ``UInt16.toBytes_length,
   ``UInt32.toBytes_length, ``UInt64.toBytes_length]

/-- The lemmas `simp only` always includes (`eq_self`, `iff_self`), so that goals reduced to
`a = a` are closed. -/
def simpOnlyBuiltinThms (s : SimpTheorems) : MetaM SimpTheorems := do
  let mut s := s
  for n in Lean.Elab.Tactic.simpOnlyBuiltins do
    s ← s.addConst n
  return s

/-- Is `t` a linear-arithmetic proposition over `Nat`/`Int` (an (in)equality, possibly a
conjunction of them) that `omega` could decide? -/
partial def isArithProp (t : Expr) : MetaM Bool := do
  let t := t.consumeMData
  if t.isAppOfArity ``And 2 then
    return (← isArithProp (t.getArg! 0)) && (← isArithProp (t.getArg! 1))
  if t.isAppOfArity ``Not 1 then return ← isArithProp (t.getArg! 0)
  let isNatInt (ty : Expr) : MetaM Bool := do
    let ty ← whnfR ty
    return ty.isConstOf ``Nat || ty.isConstOf ``Int
  if let some (ty, _, _) := t.eq? then return ← isNatInt ty
  if t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4 || t.isAppOfArity ``GE.ge 4 ||
      t.isAppOfArity ``GT.gt 4 || t.isAppOfArity ``Ne 3 then
    return ← isNatInt (t.getArg! 0)
  return false

/-- Try to close an arithmetic side goal (typically a byte-length condition such as
`(List.drop 8 bs).length = 8` or `k ≤ bs.length`) by normalising lengths with
`lengthSimpLemmas` and running `omega` on the result with the hypotheses of the context.
Much cheaper than `grind`, and complete for the linear length arithmetic `kstep` generates. -/
def solveArithGoal (g : MVarId) : MetaM Bool := g.withContext do
  -- `commitWhen`: leave the metavariable context untouched unless the goal was closed.
  commitWhen do
    try
      let simpThms ← lengthSimpLemmas.foldlM (fun (s : SimpTheorems) n => s.addConst n) {}
      let simpThms ← simpOnlyBuiltinThms simpThms
      let ctx ← Simp.mkContext {} (simpTheorems := #[simpThms]) (congrTheorems := ← getSimpCongrTheorems)
      let (r, _) ← simpGoal g ctx (simprocs := #[← Simp.getSimprocs])
      let some (_, g) := r | return true
      let some g ← g.falseOrByContra | return true
      g.withContext do
        let hyps := (← getLocalHyps).toList
        Lean.Elab.Tactic.Omega.omega hyps g {}
      return true
    catch _ => return false

/-- `some true` if `prop` holds by `solveArithGoal`, `some false` if its negation does, `none`
otherwise. Used to avoid expensive `grind` calls on side goals that are simply false. -/
def decideArithProp (prop : Expr) : MetaM (Option Bool) := withoutModifyingState do
  let g ← mkFreshExprMVar prop
  if ← solveArithGoal g.mvarId! then return some true
  let gNot ← mkFreshExprMVar (mkNot prop)
  if ← solveArithGoal gNot.mvarId! then return some false
  return none

initialize registerTraceClass `Kraken.sep

/-- Normalise a goal `lhs = rhs` of `BitVec` sums: right-associate and fold literal offsets
(`a + 16#64 + 8#64 ↦ a + 24#64`). Returns `none` if the goal was closed, else the new goal. -/
def normBitVecEqGoal (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let thms ← ([``BitVec.add_assoc] : List Name).foldlM (fun (s : SimpTheorems) n => s.addConst n) {}
  let thms ← thms.addConst ``BitVec.ofNat_add (inv := true)
  let thms ← simpOnlyBuiltinThms thms
  let ctx ← Simp.mkContext {} (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simpGoal g ctx (simprocs := #[← Simp.getSimprocs])
  return r.map (·.2)

/-- Prove an equality of `BitVec` sums by right-associating and folding literals
(`a + 16#64 + 8#64 = a + 24#64`). -/
def proveBitVecEqByNorm (g : MVarId) : MetaM Bool := g.withContext do
  commitWhen do
    try
      return (← normBitVecEqGoal g).isNone
    catch _ => return false

/-- `base + offset` decomposition of a normalised `BitVec` sum (`offset := 0` if absent). -/
private def bvBaseOffset? (e : Expr) : Option (Expr × Nat) :=
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let b := e.getArg! 4
    let o := e.getArg! 5
    if o.isAppOfArity ``BitVec.ofNat 2 then
      match (o.getArg! 1).nat? with
      | some n => some (b, n)
      | none => some (e, 0)
    else some (e, 0)
  else some (e, 0)

/-- Decide an equality of `BitVec 64` address sums: `some true` if it holds after normalisation,
`some false` if both sides are the same base with different literal offsets, `none` otherwise. -/
def decideBitVecAddEq (prop : Expr) : MetaM (Option Bool) := withoutModifyingState do
  let some (ty, _, _) := prop.consumeMData.eq? | return none
  unless (← whnfR ty).isAppOfArity ``BitVec 1 do return none
  let g ← mkFreshExprMVar prop
  try
    let some g' ← normBitVecEqGoal g.mvarId! | return some true
    let t ← instantiateMVars (← g'.getType)
    let some (_, lhs, rhs) := t.consumeMData.eq? | return none
    let some (b₁, o₁) := bvBaseOffset? lhs | return none
    let some (b₂, o₂) := bvBaseOffset? rhs | return none
    if b₁ == b₂ && o₁ < 2 ^ 64 && o₂ < 2 ^ 64 && o₁ != o₂ then return some false
    return none
  catch _ => return none

/-- Find a hypothesis proving `prop` up to definitional equality (lets, `abbrev`s), or, for
`prop = ¬ (b = true)` / `¬ (b = false)`, a hypothesis `b' = false` / `b' = true` with `b ≡ b'`. -/
def assumptionModBool (prop : Expr) : MetaM (Option Expr) :=
  -- let-bound intermediate values of the symbolic state must be unfolded
  withConfig (fun c => { c with zetaDelta := true }) do
  let prop ← instantiateMVars prop
  let isBoolEq (t : Expr) : Option (Expr × Expr) :=
    match t.consumeMData.eq? with
    | some (ty, lhs, rhs) => if ty.isConstOf ``Bool then some (lhs, rhs) else none
    | none => none
  let negated? : Option (Expr × Bool) :=
    match prop.consumeMData.not? with
    | some inner =>
      match isBoolEq inner with
      | some (b, v) =>
        if v.isConstOf ``Bool.true then some (b, true)
        else if v.isConstOf ``Bool.false then some (b, false) else none
      | none => none
    | none => none
  let defEq (a b : Expr) : MetaM Bool :=
    tryCatchRuntimeEx (withReducibleAndInstances (isDefEq a b) <||> isDefEq a b) (fun _ => pure false)
  let propHead := prop.consumeMData.getAppFn
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let t ← instantiateMVars decl.type
    if t.hasExprMVar then continue
    -- same head symbol (`Eq`, `Not`, …): cheap filter before definitional unfolding
    if t.consumeMData.getAppFn == propHead then
      if ← defEq t prop then
        return some decl.toExpr
    if let some (b, v) := negated? then
      if let some (b', v') := isBoolEq t then
        if v && v'.isConstOf ``Bool.false && (← defEq b b') then
          return some (← mkExpectedTypeHint (← mkAppM ``ne_true_of_eq_false #[decl.toExpr]) prop)
        if !v && v'.isConstOf ``Bool.true && (← defEq b b') then
          return some (← mkExpectedTypeHint (← mkAppM ``ne_false_of_eq_true #[decl.toExpr]) prop)
  return none

/-- Reduce `match` applications and structure projections whose discriminant is a constructor
application, everywhere in `e` (including implicit and instance arguments, which the `Sym`
simplifiers do not visit). The result is definitionally equal to `e`. -/
private def getStructureCtor? (major : Expr) : MetaM Name := do
  let ty ← whnfD (← inferType major)
  let .const tyName _ := ty.getAppFn | return .anonymous
  let some info := getStructureInfo? (← getEnv) tyName | return .anonymous
  let _ := info
  return (getStructureCtor (← getEnv) tyName).name

def reduceStuckMatchers (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    if let .const fn _ := e.getAppFn then
      if (← getMatcherInfo? fn).isSome then
        if let .reduced e' ← reduceMatcher? e then return .visit e'
      else if e.isApp then
        -- structure (not class) projections of constructor applications
        if let some info ← getProjectionFnInfo? fn then
          if !info.fromClass && e.getAppNumArgs > info.numParams then
            let major := e.getArg! info.numParams
            if (← whnfCore major).isAppOf (← getStructureCtor? major) then
              if let some e' ← Meta.unfoldDefinition? e then
                let e'' ← whnfCore e'
                unless e''.isProj do return .visit e''
    else if e.isProj then
      let e' ← whnfCore e
      unless e'.isProj do return .visit e'
    return .continue)

/-- Lemmas of the `BitVec`/`UInt64` normal form `kstep` leaves its symbolic state in (also used
by `kfinish`). -/
def normalFormLemmas : List Name :=
  [``BitVec.shiftLeft_zero, ``BitVec.zero_shiftLeft, ``BitVec.add_zero, ``BitVec.zero_add,
   ``BitVec.or_zero, ``BitVec.zero_or, ``BitVec.xor_self, ``BitVec.setWidth_eq,
   ``UInt64.toNat_toBitVec, ``UInt64.toBitVec_ofBitVec, ``UInt64.ofBitVec_toBitVec,
   ``Int64.ofBitVec_toBitVec, ``Nat.sub_zero, ``Nat.add_zero, ``Nat.zero_add,
   -- ground `if`s (conditions are decided, see `simpNormalForm`)
   ``ite_true, ``ite_false, ``dite_true, ``dite_false,
   -- `ubfm`/`lsr #k`: `setWidth w (extractLsb' 0 m (x >>> k)) = x >>> k` for `w ≤ m + k`
   ``BitVec.setWidth_extractLsb'_ushiftRight]

/-- Heads of the closed `Nat` arithmetic that `reduceNatGround` folds. -/
private def natGroundHeads : List Name :=
  [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``HPow.hPow,
   ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.pow, ``Nat.succ]

/-- Fold closed `Nat` arithmetic on literals (`64 - 1`, `63 + 1`) into a *raw* literal — the
convention of the `Sym` simplifier's ground evaluation; the standard `Nat.reduceSub` & co. would
produce `OfNat` numerals, which `Sym` does not fold any further. The result is definitionally
equal to the input (kernel `Nat` literal arithmetic). -/
def reduceNatGround : Simp.Simproc := fun e => do
  let .const fn _ := e.getAppFn | return .continue
  unless natGroundHeads.contains fn do return .continue
  if e.hasFVar || e.hasMVar then return .continue
  let some n ← (Meta.evalNat e).run | return .continue
  return .done { expr := mkRawNatLit n }

/-- Bring a (small) term into the normal form with the standard simplifier, which, unlike the
`Sym` simplifier, matches raw natural-number literals against `OfNat` numerals. Closed conditions
(`1 ≤ 63`, `(1 == 0) = true`) are decided so that ground `if`s disappear, and closed `Nat`
arithmetic is folded to raw literals (`reduceNatGround`). Returns the new term and a proof of
equality if anything changed. -/
def simpNormalForm (e : Expr) : MetaM (Option (Expr × Expr)) := do
  tryCatchRuntimeEx
    (do
      let thms ← normalFormLemmas.foldlM (fun (s : SimpTheorems) n => do
        if (← getEnv).contains n then s.addConst n else pure s) {}
      -- no standard simprocs: they would introduce `OfNat` numerals, while the `Sym` simplifier
      -- works with the raw literals produced by its ground evaluation
      let ctx ← Simp.mkContext { decide := true } (simpTheorems := #[thms])
        (congrTheorems := ← getSimpCongrTheorems)
      let methods := Simp.mkDefaultMethodsCore #[]
      let methods := { methods with
        post := fun e => do
          match ← reduceNatGround e with
          | .done r => return .done r
          | _ => methods.post e }
      let (r, _) ← Simp.main e ctx (methods := methods)
      if r.expr == e then return none
      let prf ← r.getProof
      return some (r.expr, prf))
    (fun _ => return none)

/-- Number of nodes of `e`, saturating at `cap + 1`; binders count as "too big". -/
private def exprSizeCapped (e : Expr) (cap : Nat) : Nat :=
  go e cap
where
  go (e : Expr) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => cap + 1
    | fuel + 1 =>
      match e with
      | .app f a => go f fuel + go a fuel
      | .mdata _ e => go e fuel
      | .proj _ _ e => 1 + go e fuel
      | .lam .. | .forallE .. | .letE .. => cap + 1
      | _ => 1

/-- Is `e` an "atomic" value worth inlining wherever its `let` is referenced: a literal, a local
variable, a closed term of at most `maxSize` nodes (an immediate such as `BitVec.ofInt 64 1`), or a
structure projection of a local variable (a register read such as `X4.toBitVec`)? -/
def isAtomicValue (e : Expr) (maxSize : Nat := 8) : MetaM Bool := do
  if e.isFVar || e.nat?.isSome || e.rawNatLit?.isSome then return true
  if e.hasMVar then return false
  if !e.hasFVar then return exprSizeCapped e maxSize ≤ maxSize
  if let .const fn _ := e.getAppFn then
    if let some info ← getProjectionFnInfo? fn then
      if !info.fromClass && e.getAppNumArgs == info.numParams + 1 then
        return (e.getArg! info.numParams).isFVar
  return false

/-- Replace `let`-bound local variables with atomic values (`isAtomicValue`) by their values, so
that instruction residues become self-contained (`X4.toBitVec <<< 63 ||| …` instead of
`val1 <<< (64 - lsb) ||| …`) and their ground conditions and shift amounts can be decided and
folded. The result is definitionally equal to `e` (zeta-delta). -/
partial def inlineAtomicLets (e : Expr) : MetaM Expr := do
  let lctx ← getLCtx
  let mut subst : Std.HashMap FVarId Expr := {}
  for fvarId in (collectFVars {} e).fvarIds do
    if let some (.ldecl (value := v) ..) := lctx.find? fvarId then
      -- values may refer to earlier atomic lets themselves
      let v' ← inlineAtomicLets v
      if ← isAtomicValue v' then
        subst := subst.insert fvarId v'
  if subst.isEmpty then return e
  return e.replace fun
    | .fvar id => subst[id]?
    | _ => none

/-- Is `ty` a machine-word-like type (`BitVec _`, `UInt*`, `Int*`, `Nat`, `Int`, `Bool`) whose
values are worth normalising eagerly? -/
def isWordType (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  if ty.isAppOf ``BitVec then return true
  if let .const n _ := ty.getAppFn then
    return [``UInt64, ``UInt32, ``UInt16, ``UInt8, ``Int64, ``Int32, ``Int16, ``Int8, ``Nat, ``Int,
      ``Bool].contains n
  return false

inductive SimpWithHypsResult where
  | closed
  | refuted
  | goal (g : MVarId)

/-- Simplify the goal using the equational hypotheses of the context as rewrite rules (plus
`Bool`/`decide` normalisation). Reports whether the goal was closed, reduced to `False`, or
replaced by a simplified goal. -/
def simpWithHyps (g : MVarId) : MetaM SimpWithHypsResult := g.withContext do
  tryCatchRuntimeEx (do
    let mut thms : SimpTheorems := {}
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      let t ← instantiateMVars decl.type
      if t.hasExprMVar then continue
      if t.consumeMData.isAppOfArity ``Eq 3 || t.consumeMData.isAppOfArity ``Ne 3 ||
          t.consumeMData.isAppOfArity ``Not 1 then
        thms ← thms.add (.fvar decl.fvarId) #[] decl.toExpr
    for n in [``bne_self_eq_false, ``beq_self_eq_true, ``Bool.false_eq_true, ``Bool.true_eq_false,
        ``Bool.not_false, ``Bool.not_true, ``decide_eq_true_eq, ``bne_iff_ne, ``beq_iff_eq,
        ``ne_eq, ``not_true_eq_false, ``not_false_eq_true] do
      if (← getEnv).contains n then thms ← thms.addConst n
    thms ← simpOnlyBuiltinThms thms
    let ctx ← Simp.mkContext {} (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
    let (r, _) ← simpGoal g ctx (simprocs := #[← Simp.getSimprocs])
    match r with
    | none => return .closed
    | some (_, g') =>
      if (← instantiateMVars (← g'.getType)).consumeMData.isConstOf ``False then
        return .refuted
      return .goal g')
    (fun _ => return .goal g)

def provePropGoal (prop : Expr) : MetaM (Option Expr) :=
  commitWhenSomeNoEx? do
    let prop ← instantiateMVars prop
    -- Cheap path: address equalities of `BitVec` sums.
    match ← decideBitVecAddEq prop with
    | some true =>
      let goal ← mkFreshExprMVar prop
      if ← proveBitVecEqByNorm goal.mvarId! then
        trace[Kraken.sep] "provePropGoal by BitVec normalisation: {prop}"
        return some (← instantiateMVars goal)
    | some false =>
      trace[Kraken.sep] "provePropGoal refuted by BitVec normalisation: {prop}"
      return none
    | none => pure ()
    -- Cheap path: linear length arithmetic (and no `grind` on refutable side conditions).
    if ← isArithProp prop then
      match ← decideArithProp prop with
      | some true =>
        let goal ← mkFreshExprMVar prop
        if ← solveArithGoal goal.mvarId! then
          trace[Kraken.sep] "provePropGoal by omega: {prop}"
          return some (← instantiateMVars goal)
      | some false =>
        trace[Kraken.sep] "provePropGoal refuted by omega: {prop}"
        return none
      | none => pure ()
    trace[Kraken.sep] "provePropGoal by grind: {prop}"
    let hasBytesInProp :=
      (prop.find? (fun e => e.isConstOf ``Int.ofBytes || e.isConstOf ``Int.toBytes)).isSome
    let goal ← mkFreshExprMVar prop
    let mut toClear : Array FVarId := #[]
    for localDecl? in (← getLCtx).decls do
      if let some localDecl := localDecl? then
        if localDecl.hasValue ||
           (localDecl.type.find? (·.isConstOf ``Std.ExtHashMap)).isSome ||
           isCalleeSavedEqType localDecl.type ||
           (!hasBytesInProp && (localDecl.type.find? (fun e => e.isConstOf ``Int.ofBytes || e.isConstOf ``Int.toBytes)).isSome) then
          toClear := toClear.push localDecl.fvarId
    let goalId ← goal.mvarId!.tryClearMany toClear
    let params ← Lean.Meta.Grind.mkDefaultParams {}
    let res ← Lean.Meta.Grind.main goalId params
    if res.hasFailed then return none
    unless ← goal.mvarId!.isAssigned do return none
    return some (← instantiateMVars goal)

private def provePropEq (lhs rhs : Expr) : MetaM (Option Expr) := do
  unless ← commitWhen (isDefEq (← inferType lhs) (← inferType rhs)) do return none
  provePropGoal (← mkEq lhs rhs)

private def matchPropAt (lhs rhs : Expr) : MetaM (Option Expr) := do
  let some (bs₁, addr₁) ← extractAtBytesAndAddr? lhs | return none
  let some (bs₂, addr₂) ← extractAtBytesAndAddr? rhs | return none
  if ← matchClosed addr₁ addr₂ then
    let some hBs ← provePropEq bs₁ bs₂ | return none
    let fn ← withLocalDeclD `bs (← inferType bs₁) fun bs => do
      let atExpr ← mkAppM ``List.At #[bs, addr₁]
      let eqExpr ← mkAppM ``Eq #[atExpr]
      mkLambdaFVars #[bs] eqExpr
    return some (← mkCongrArg fn hBs)
  if ← matchClosed bs₁ bs₂ then
    let some hAddr ← provePropEq addr₁ addr₂ | return none
    let fn ← withLocalDeclD `a (← inferType addr₁) fun a => do
      let atExpr ← mkAppM ``List.At #[bs₁, a]
      let eqExpr ← mkAppM ``Eq #[atExpr]
      mkLambdaFVars #[a] eqExpr
    return some (← mkCongrArg fn hAddr)
  let some hAddr ← provePropEq addr₁ addr₂ | return none
  let some hBs ← provePropEq bs₁ bs₂ | return none
  let fnBs ← withLocalDeclD `bs (← inferType bs₁) fun bs => do
    let atExpr ← mkAppM ``List.At #[bs, addr₁]
    let eqExpr ← mkAppM ``Eq #[atExpr]
    mkLambdaFVars #[bs] eqExpr
  let h1 ← mkCongrArg fnBs hBs
  let fnAddr ← withLocalDeclD `a (← inferType addr₁) fun a => do
    let atExpr ← mkAppM ``List.At #[bs₂, a]
    let eqExpr ← mkAppM ``Eq #[atExpr]
    mkLambdaFVars #[a] eqExpr
  let h2 ← mkCongrArg fnAddr hAddr
  return some (← mkEqTrans h1 h2)

private def isNakedMVar : Expr → Bool
  | .mvar _ => true
  | _ => false

private inductive ClauseSlot where
  | unmatched (e : Expr)
  | matched (c : Expr) (eqProof? : Option Expr := none)
  deriving Inhabited

private abbrev ClauseSlots := Array ClauseSlot

private def unmatchedIndices (slots : ClauseSlots) : List (Nat × Expr) := Id.run do
  let mut res := []
  for h : i in [0:slots.size] do
    if let .unmatched e := slots[i] then
      res := res ++ [(i, e)]
  return res

private def instantiateSlotMVars (slots : ClauseSlots) : MetaM ClauseSlots :=
  slots.mapM fun
    | .unmatched e => return .unmatched (← instantiateMVars e)
    | .matched c eqProof? => return .matched (← instantiateMVars c) eqProof?

private def extractCanonical (slots : ClauseSlots) :
    Option (List (Expr × Option Expr)) := Id.run do
  let mut res := []
  for s in slots do
    match s with
    | .unmatched _ => return none
    | .matched c eqProof? => res := res ++ [(c, eqProof?)]
  return some res

private def spliceAt (slots : ClauseSlots) (idx : Nat) (replacement : List Expr) :
    List (Expr × Option Expr) := Id.run do
  let mut res := []
  for h : i in [0:slots.size] do
    if i == idx then
      res := res ++ replacement.map (·, none)
    else if let .matched c eqProof? := slots[i] then
      res := res ++ [(c, eqProof?)]
  return res

private def tryAssignNakedSlot (predType : Expr) (lhs rhs : ClauseSlots) :
    MetaM (Option (List (Expr × Option Expr) × List (Expr × Option Expr))) := do
  match unmatchedIndices lhs, unmatchedIndices rhs with
  | [(i, .mvar mvarId)], remRhsPairs =>
    let remRhs := remRhsPairs.map Prod.snd
    unless ← isDefEq (.mvar mvarId) (← denoteClauses predType remRhs) do return none
    let rhs' := rhs.map fun | .unmatched r => .matched r none | .matched c eq? => .matched c eq?
    let some rhsCan := extractCanonical rhs' | return none
    let lhsCan := spliceAt lhs i remRhs
    return some (lhsCan, rhsCan)
  | remLhsPairs, [(j, .mvar mvarId)] =>
    let remLhs := remLhsPairs.map Prod.snd
    unless ← isDefEq (.mvar mvarId) (← denoteClauses predType remLhs) do return none
    let lhs' := lhs.map fun | .unmatched l => .matched l none | .matched c eq? => .matched c eq?
    let some lhsCan := extractCanonical lhs' | return none
    let rhsCan := spliceAt rhs j remLhs
    return some (lhsCan, rhsCan)
  | _, _ => return none

-- Greedily cancel closed clauses in a single pass while recording their canonical alignment.
private def cancelClosedSlots (lhs rhs : ClauseSlots) : MetaM (ClauseSlots × ClauseSlots) := do
  let mut lhs := lhs
  let mut rhs := rhs
  for i in [0:lhs.size] do
    if let .unmatched l := lhs[i]! then
      if !l.hasExprMVar then
        let mut matchedIdx? : Option Nat := none
        for j in [0:rhs.size] do
          if matchedIdx?.isNone then
            if let .unmatched r := rhs[j]! then
              if !r.hasExprMVar then
                if ← matchClosed l r then
                  matchedIdx? := some j
        if let some j := matchedIdx? then
          lhs := lhs.set! i (.matched l)
          rhs := rhs.set! j (.matched l)
  return (lhs, rhs)

-- Match remaining closed `At` clauses whose addresses or byte values are propositionally equal.
private def cancelPropAtSlots (lhs rhs : ClauseSlots) : MetaM (ClauseSlots × ClauseSlots) := do
  let mut lhs := lhs
  let mut rhs := rhs
  for i in [0:lhs.size] do
    if let .unmatched l := lhs[i]! then
      if !l.hasExprMVar then
        let mut matched? : Option (Nat × Expr) := none
        for j in [0:rhs.size] do
          if matched?.isNone then
            if let .unmatched r := rhs[j]! then
              if !r.hasExprMVar then
                if let some eqPrf ← matchPropAt l r then
                  matched? := some (j, eqPrf)
        if let some (j, eqPrf) := matched? then
          lhs := lhs.set! i (.matched l none)
          rhs := rhs.set! j (.matched l (some eqPrf))
  return (lhs, rhs)

private partial def cancelAndAlign (predType : Expr) (lhs rhs : ClauseSlots) :
    MetaM (Option (List (Expr × Option Expr) × List (Expr × Option Expr))) := do
  let (lhs, rhs) ← cancelClosedSlots lhs rhs
  if let (some lhsCan, some rhsCan) := (extractCanonical lhs, extractCanonical rhs) then
    return some (lhsCan, rhsCan)
  for i in [0:lhs.size] do
    if let .unmatched l := lhs[i]! then
      for j in [0:rhs.size] do
        if let .unmatched r := rhs[j]! then
          if (l.hasExprMVar || r.hasExprMVar) && !isNakedMVar l && !isNakedMVar r then
            let res? ← commitWhenSomeNoEx? do
              unless ← matchAtom l r do return none
              let c ← instantiateMVars l
              let lhs' ← instantiateSlotMVars (lhs.set! i (.matched c))
              let rhs' ← instantiateSlotMVars (rhs.set! j (.matched c))
              cancelAndAlign predType lhs' rhs'
            if res?.isSome then return res?
  let (lhs, rhs) ← cancelPropAtSlots lhs rhs
  if let (some lhsCan, some rhsCan) := (extractCanonical lhs, extractCanonical rhs) then
    return some (lhsCan, rhsCan)
  tryAssignNakedSlot predType lhs rhs

private def extractListAppendArgs? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``HAppend.hAppend 6 then
    let args := e.getAppArgs
    some (args[4]!, args[5]!)
  else if e.isAppOfArity ``List.append 3 then
    let args := e.getAppArgs
    some (args[1]!, args[2]!)
  else
    none

private def inferKnownByteLength? (bs : Expr) : MetaM (Option (Expr × Expr)) := do
  let bs ← instantiateMVars bs
  if bs.isAppOfArity ``Int.toBytes 2 then
    let n := bs.appFn!.appArg!
    let v := bs.appArg!
    return some (n, ← mkAppM ``Int.toBytes_length #[n, v])
  if bs.isAppOfArity ``Nat.toBytes 2 then
    let n := bs.appFn!.appArg!
    let v := bs.appArg!
    return some (n, ← mkAppM ``Nat.toBytes_length #[n, v])
  for localDecl? in (← getLCtx).decls.toArray.reverse do
    if let some localDecl := localDecl? then
      let t ← instantiateMVars localDecl.type
      if t.isAppOfArity ``Eq 3 then
        let lhs := t.appFn!.appArg!
        let rhs := t.appArg!
        if lhs.isAppOfArity ``List.length 2 && lhs.appArg! == bs then
          return some (rhs, localDecl.toExpr)
  return none

private partial def expandAppendsInSepExpr (e : Expr) (fuel : Nat := 4) : MetaM (Expr × Option Expr) := do
  if fuel == 0 then
    return (e, none)
  let e ← reduceProjectionApp (← instantiateMVars e)
  if e.getAppFn.constName? == some ``Std.ExtHashMap.sep then
    let args := e.getAppArgs
    let p := args[args.size - 2]!
    let q := args[args.size - 1]!
    let (p', hp?) ← expandAppendsInSepExpr p fuel
    let (q', hq?) ← expandAppendsInSepExpr q fuel
    if hp?.isNone && hq?.isNone then
      return (e, none)
    let sep' ← mkAppM ``Std.ExtHashMap.sep #[p', q']
    let hSep? ← match hp?, hq? with
      | none, none => pure none
      | some hp, none =>
        let h1 ← mkCongrArg sep'.appFn!.appFn! hp
        some <$> mkCongrFun h1 q'
      | none, some hq =>
        some <$> mkCongrArg sep'.appFn! hq
      | some hp, some hq =>
        let h1 ← mkCongrArg sep'.appFn!.appFn! hp
        some <$> mkCongr h1 hq
    return (sep', hSep?)
  let some (bs, a) ← extractAtBytesAndAddr? e | return (e, none)
  if bs.hasExprMVar || a.hasExprMVar then
    return (e, none)
  let some (bs1, bs2) := extractListAppendArgs? bs | return (e, none)
  let splitRes? ← commitWhenSomeNoEx? do
    let len1? ← inferKnownByteLength? bs1
    let len2? ← inferKnownByteLength? bs2
    let hSplit ← match len1?, len2? with
      | some (n1, hN1), some (n2, hN2) =>
        let splitFn ← mkAppM ``Mem.At_append_sep_len2 #[bs1, bs2, n1, n2, a, hN1, hN2]
        let lenBoundType := (← inferType splitFn).bindingDomain!
        let some hLen ← provePropGoal lenBoundType | return none
        pure (mkApp splitFn hLen)
      | some (n1, hN1), none =>
        let splitFn ← mkAppM ``Mem.At_append_sep_len #[bs1, bs2, n1, a, hN1]
        let lenBoundType := (← inferType splitFn).bindingDomain!
        let some hLen ← provePropGoal lenBoundType | return none
        pure (mkApp splitFn hLen)
      | none, _ =>
        let splitFn ← mkAppM ``Mem.At_append_sep #[bs1, bs2, a]
        let lenBoundType := (← inferType splitFn).bindingDomain!
        let some hLen ← provePropGoal lenBoundType | return none
        pure (mkApp splitFn hLen)
    let actualLhs := (← inferType hSplit).appFn!.appArg!
    if e == actualLhs then
      return some hSplit
    else
      return some (← mkExpectedTypeHint hSplit (← mkEq e (← inferType hSplit).appArg!))
  let some hSplit := splitRes? | return (e, none)
  let splitRhs := (← inferType hSplit).appArg!
  let (splitRhs', hMore?) ← expandAppendsInSepExpr splitRhs (fuel - 1)
  let hTotal ← match hMore? with
    | none => pure hSplit
    | some hMore => mkEqTrans hSplit hMore
  return (splitRhs', some hTotal)

private def collectTakeTargets (clauses : List Expr) : MetaM (Array (Expr × Expr)) := do
  let mut res := #[]
  for clause in clauses do
    if let some (bsExpr, _) ← extractAtBytesAndAddr? clause then
      if bsExpr.isAppOfArity ``List.take 3 then
        let k := bsExpr.appFn!.appArg!
        let bs' := bsExpr.appArg!
        unless res.any (fun (b, n) => b == bs' && n == k) do
          res := res.push (bs', k)
  return res

private partial def expandSlicesInSepExpr (e : Expr) (takeTargets : Array (Expr × Expr))
    (fuel : Nat := 4) : MetaM (Expr × Option Expr) := do
  if fuel == 0 || takeTargets.isEmpty then
    return (e, none)
  let e ← reduceProjectionApp (← instantiateMVars e)
  if e.getAppFn.constName? == some ``Std.ExtHashMap.sep then
    let args := e.getAppArgs
    let p := args[args.size - 2]!
    let q := args[args.size - 1]!
    let (p', hp?) ← expandSlicesInSepExpr p takeTargets fuel
    let (q', hq?) ← expandSlicesInSepExpr q takeTargets fuel
    if hp?.isNone && hq?.isNone then
      return (e, none)
    let sep' ← mkAppM ``Std.ExtHashMap.sep #[p', q']
    let hSep? ← match hp?, hq? with
      | none, none => pure none
      | some hp, none =>
        let h1 ← mkCongrArg sep'.appFn!.appFn! hp
        some <$> mkCongrFun h1 q'
      | none, some hq =>
        some <$> mkCongrArg sep'.appFn! hq
      | some hp, some hq =>
        let h1 ← mkCongrArg sep'.appFn!.appFn! hp
        some <$> mkCongr h1 hq
    return (sep', hSep?)
  let some (bs, a) ← extractAtBytesAndAddr? e | return (e, none)
  if bs.hasExprMVar || a.hasExprMVar then
    return (e, none)
  for (bs', k) in takeTargets do
    let matchRes? ← commitWhenSomeNoEx? do
      let (bsTarget, hBs?) ←
        if ← matchClosed bs bs' then
          pure (bs, none)
        else if bs.isAppOfArity ``List.drop 3 && bs'.isAppOfArity ``List.drop 3 then
          let some hBs ← provePropEq bs bs' | return none
          pure (bs', some hBs)
        else
          return none
      let splitFn ← mkAppM ``Mem.At_take_drop_sep #[bsTarget, k, a]
      let splitFnType ← inferType splitFn
      let kType := splitFnType.bindingDomain!
      let lenBoundType := splitFnType.bindingBody!.bindingDomain!
      let some hK ← provePropGoal kType | return none
      let some hLen ← provePropGoal lenBoundType | return none
      let hSplit := mkApp2 splitFn hK hLen
      let hSplit ← match hBs? with
        | none =>
          let actualLhs := (← inferType hSplit).appFn!.appArg!
          if e == actualLhs then
            pure hSplit
          else
            mkExpectedTypeHint hSplit (← mkEq e (← inferType hSplit).appArg!)
        | some hBs =>
          let fn ← withLocalDeclD `x (← inferType bs) fun x => do
            let atE ← mkAppM ``List.At #[x, a]
            let eqE ← mkAppM ``Eq #[atE]
            mkLambdaFVars #[x] eqE
          let hCongr ← mkCongrArg fn hBs
          mkEqTrans hCongr hSplit
      return some hSplit
    if let some hSplit := matchRes? then
      let splitRhs := (← inferType hSplit).appArg!
      let (splitRhs', hMore?) ← expandSlicesInSepExpr splitRhs takeTargets (fuel - 1)
      let hTotal ← match hMore? with
        | none => pure hSplit
        | some hMore => mkEqTrans hSplit hMore
      return (splitRhs', some hTotal)
  return (e, none)

private def solveSepEqCore (lhs rhs : Expr) : MetaM (Option Expr) :=
  commitWhenSomeNoEx? do
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    if lhs == rhs then
      return some (← mkEqRefl lhs)
    let predType ← inferType lhs
    let lhsTree ← parseSepTree lhs
    let rhsTree ← parseSepTree rhs
    let lhsSlots := lhsTree.clauses.toArray.map ClauseSlot.unmatched
    let rhsSlots := rhsTree.clauses.toArray.map ClauseSlot.unmatched
    if !lhs.hasExprMVar && !rhs.hasExprMVar && lhsSlots.size != rhsSlots.size then
      return none
    let some (lhsCan, rhsCan) ← cancelAndAlign predType lhsSlots rhsSlots | return none
    let some (lhs', _, []) ← rebuildSepTree lhsTree lhsCan | return none
    let some (rhs', rhsEq?, []) ← rebuildSepTree rhsTree rhsCan | return none
    let acProof ← mkFreshExprMVar (← mkEq lhs' rhs')
    Lean.Meta.AC.rewriteUnnormalizedRefl acProof.mvarId!
    let acProof ← instantiateMVars acProof
    match rhsEq? with
    | some rhsEq => return some (← mkEqTrans acProof rhsEq)
    | none => return some acProof

private def chainOptEq (h1? h2? : Option Expr) : MetaM (Option Expr) := do
  match h1?, h2? with
  | none, none => return none
  | some h1, none => return some h1
  | none, some h2 => return some h2
  | some h1, some h2 => return some (← mkEqTrans h1 h2)

private def solveSepEq (lhs rhs : Expr) : MetaM (Option Expr) := do
  if let some prf ← solveSepEqCore lhs rhs then
    return some prf
  commitWhenSomeNoEx? do
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    let (lhs1, hLhs1?) ← expandAppendsInSepExpr lhs
    let (rhs1, hRhs1?) ← expandAppendsInSepExpr rhs
    let lhsTree ← parseSepTree lhs1
    let rhsTree ← parseSepTree rhs1
    let rhsTakes ← collectTakeTargets rhsTree.clauses
    let lhsTakes ← collectTakeTargets lhsTree.clauses
    let (lhs2, hLhs2?) ← expandSlicesInSepExpr lhs1 rhsTakes
    let (rhs2, hRhs2?) ← expandSlicesInSepExpr rhs1 lhsTakes
    let hLhs? ← chainOptEq hLhs1? hLhs2?
    let hRhs? ← chainOptEq hRhs1? hRhs2?
    if hLhs?.isNone && hRhs?.isNone then
      return none
    let some hMid ← solveSepEqCore lhs2 rhs2 | return none
    let hMid ← match hLhs? with
      | some hLhs => mkEqTrans hLhs hMid
      | none => pure hMid
    let hMid ← match hRhs? with
      | some hRhs => mkEqTrans hMid (← mkEqSymm hRhs)
      | none => pure hMid
    return some hMid

private def solveFromHypothesis (target : Expr) (localDecl : LocalDecl) : MetaM (Option Expr) := do
  let hypType ← reduceProjectionApp (← instantiateMVars localDecl.type)
  unless target.isApp && hypType.isApp do return none
  let targetFn := target.appFn!
  let targetArg := target.appArg!
  let hypFn := hypType.appFn!
  let hypArg := hypType.appArg!
  unless ← matchAtom (← reduceProjectionApp targetArg) (← reduceProjectionApp hypArg) do
    return none
  let some hSeps ← solveSepEq hypFn targetFn | return none
  let hFunEq ← mkAppM ``congrFun #[hSeps, hypArg]
  return some (← mkAppM ``Eq.mp #[hFunEq, localDecl.toExpr])

structure SepAtCandidate where
  hyp : Expr
  hypArg : Expr
  hypTree : SepTree
  clause : Expr
  clauseIdx : Nat
  bs : Expr
  addr : Expr

/--
Given a separation-logic subgoal `P m` of the form `(Eq (?bs.At ?addr') ⋆ ?R) s.dmem`,
searches the local context from newest to oldest for hypotheses of the form `Q m'`
where `m'` matches `m`, parses `Q` once into a `SepTree`, and returns all `At` clause
candidates along with their pre-parsed hypothesis tree so `solveSepAtCandidate` can
close the goal directly without re-scanning or re-matching.
-/
def findSepAtCandidates (starGoal : MVarId) : MetaM (Array SepAtCandidate) := starGoal.withContext do
  let target ← reduceProjectionApp (← instantiateMVars (← starGoal.getType))
  unless target.isApp do return #[]
  let targetArg ← reduceProjectionApp target.appArg!
  let mut cands := #[]
  for localDecl? in (← getLCtx).decls.toArray.reverse do
    if let some localDecl := localDecl? then
      let hypType ← reduceProjectionApp (← instantiateMVars localDecl.type)
      if hypType.isApp then
        let hypFn := hypType.appFn!
        let hypArg := hypType.appArg!
        if ← matchAtom targetArg (← reduceProjectionApp hypArg) then
          let hypTree ← parseSepTree hypFn
          let clauses := hypTree.clauses
          for h : idx in [0:clauses.length] do
            let clause := clauses[idx]
            if let some (bs, addr) ← extractAtBytesAndAddr? clause then
              cands := cands.push {
                hyp := localDecl.toExpr
                hypArg
                hypTree
                clause
                clauseIdx := idx
                bs
                addr
              }
  return cands

/--
Directly solves a `starGoal` of the form `(Eq (?bs.At ?addr') ⋆ ?R) s.dmem` using a
pre-matched `SepAtCandidate` by extracting (or splitting and extracting via `leafSplit?`)
the target leaf along the binary tree path in $O(\text{depth})$ steps without calling
`denoteClauses`, `rebuildSepTree`, or `AC.rewriteUnnormalizedRefl`.
-/
def solveSepAtCandidate (starGoal : MVarId) (cand : SepAtCandidate)
    (leafSplit? : Option Expr := none) : MetaM Bool :=
  starGoal.withContext do
    withConfig (fun config => { config with assignSyntheticOpaque := true }) do
      let res? ← commitWhenSomeNoEx? do
        let target ← reduceProjectionApp (← instantiateMVars (← starGoal.getType))
        unless target.isApp do return none
        let targetFn := target.appFn!
        let sepArgs := targetFn.getAppArgs
        unless sepArgs.size >= 2 do return none
        let atClause := sepArgs[sepArgs.size - 2]!
        let rMVar := sepArgs[sepArgs.size - 1]!
        unless atClause.isAppOfArity ``Eq 2 do return none
        let atExpr := atClause.appArg!
        unless atExpr.isAppOfArity ``List.At 3 do return none
        let bsMVar := atExpr.appFn!.appArg!
        let addrMVar := atExpr.appArg!
        let hSeps ← match leafSplit? with
          | none =>
            unless ← isDefEq addrMVar cand.addr do return none
            unless ← isDefEq bsMVar cand.bs do return none
            let atClause ← instantiateMVars atClause
            let hRefl ← mkEqRefl atClause
            let hLeaf ←
              if cand.clause == atClause then
                pure hRefl
              else
                mkExpectedTypeHint hRefl (← mkEq cand.clause atClause)
            let some (_, frameExpr, hSeps) ←
              extractSepTree cand.hypTree cand.clauseIdx (fun _ => return .single atClause hLeaf)
              | return none
            unless ← isDefEq rMVar frameExpr do return none
            pure hSeps
          | some hSplit =>
            let splitEqType ← instantiateMVars (← inferType hSplit)
            unless splitEqType.isAppOfArity ``Eq 3 do return none
            let splitRhs := splitEqType.appArg!
            let splitRhsArgs := splitRhs.getAppArgs
            unless splitRhsArgs.size >= 2 do return none
            let extractedClause := splitRhsArgs[splitRhsArgs.size - 2]!
            let remainderClause := splitRhsArgs[splitRhsArgs.size - 1]!
            let some (splitBs, splitAddr) ← extractAtBytesAndAddr? extractedClause | return none
            unless ← isDefEq addrMVar splitAddr do return none
            unless ← isDefEq bsMVar splitBs do return none
            let atClause ← instantiateMVars atClause
            let hSplit ←
              if cand.clause == splitEqType.appFn!.appArg! && extractedClause == atClause then
                pure hSplit
              else
                let expectedSplit ← mkEq cand.clause (← mkAppM ``Std.ExtHashMap.sep #[atClause, remainderClause])
                mkExpectedTypeHint hSplit expectedSplit
            let some (_, frameExpr, hSeps) ←
              extractSepTree cand.hypTree cand.clauseIdx
                (fun _ => return .split atClause remainderClause hSplit)
              | return none
            unless ← isDefEq rMVar frameExpr do return none
            pure hSeps
        let hFunEq ← mkAppM ``congrFun #[hSeps, cand.hypArg]
        let proof ← mkAppM ``Eq.mp #[hFunEq, cand.hyp]
        starGoal.assign proof
        return some ()
      return res?.isSome

def ecancelGoal (goal : MVarId) : MetaM Bool := goal.withContext do
  let target ← reduceProjectionApp (← instantiateMVars (← goal.getType))
  -- Existential witnesses introduced by tactics are synthetic-opaque goals;
  -- `ecancel` intentionally instantiates them as part of cancellation.
  withConfig (fun config => { config with assignSyntheticOpaque := true }) do
    if target.isAppOfArity ``Eq 3 then
      let args := target.getAppArgs
      if let some proof ← solveSepEq args[1]! args[2]! then
        goal.assign proof
        return true
    for localDecl? in (← getLCtx).decls.toArray.reverse do
      if let some localDecl := localDecl? then
        if let some proof ← solveFromHypothesis target localDecl then
          goal.assign proof
          return true
    return false

syntax (name := ecancel) "ecancel" : tactic

@[tactic ecancel]
def evalEcancel : Tactic :=
  fun _stx : Syntax => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let solved ← ecancelGoal goal
  unless solved do
    throwError "ecancel: could not automatically solve goal {target}"
  replaceMainGoal []
end Kraken.Tactic
