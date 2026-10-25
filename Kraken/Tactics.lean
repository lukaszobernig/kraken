module

/-
Common Kraken Proof Tactics.

Core tactics and theorems for stepping through Kraken assembly proofs.
-/

public import Kraken.Attribute
public import Kraken.Layout
public import Kraken.OmniSemantics
import Kraken.Separation
public import Kraken.SeparationMem
public import Kraken.SeparationTactics
public import Kraken.ToBytes

public section

@[simp, grind =]
theorem BitVec.extractLsb'_self {w : Nat} (x : BitVec w) : x.extractLsb' 0 w = x := by
  simp

@[simp, ksimp]
theorem Int64.add_sub_cancel' (a b : Int64) : a + (b - a) = b := by
  grind

attribute [grind =]
  BitVec.ofInt_natCast
  BitVec.ofNat_add
  Int.natCast_shiftLeft
  List.length_append
  List.length_take
  List.length_drop
  List.take_of_length_le
  List.take_replicate
  List.drop_replicate

attribute [ksimp]
  Int64.ofBitVec_toBitVec
  BitVec.add_zero
  BitVec.zero_add
  BitVec.extractLsb'_self
  BitVec.ofInt_add
  BitVec.ofInt_mul
  BitVec.ofInt_natCast
  BitVec.ofInt_ofNat
  BitVec.ofInt_toInt
  BitVec.ofNat_add
  BitVec.ofNat_mul
  BitVec.ofNat_toNat
  BitVec.ofNat_uInt64ToNat
  BitVec.setWidth_eq
  BitVec.ofInt_ofBytes_toBytes_8
  BitVec.ofInt_ofBytes_toBytes_16
  BitVec.ofInt_ofBytes_toBytes_32
  BitVec.ofInt_ofBytes_toBytes_64
  BitVec.ofInt_ofBytes_uInt8ToBytes
  BitVec.ofInt_ofBytes_uInt16ToBytes
  BitVec.ofInt_ofBytes_uInt32ToBytes
  BitVec.ofInt_ofBytes_uInt64ToBytes
  Int.add_zero
  Int.natCast_shiftLeft
  Int.toBytes_length
  Int.toBytes_zero
  Int64.toInt_neg
  Nat.shiftRight_zero
  Nat.sub_zero
  Nat.toBytes_length
  UInt8.toBytes_length
  UInt16.toBytes_length
  UInt32.toBytes_length
  UInt64.toBytes_length
  UInt64.ofBitVec_add
  UInt64.ofBitVec_ofNat
  UInt64.ofBitVec_sub
  UInt64.ofBitVec_toBitVec
  UInt64.sub_add_cancel
  UInt64.toBitVec_ofNat
  UInt64.toBitVec_sub
  UInt64.toNat_toBitVec

end

public meta section

open Lean Meta Elab Tactic Kraken

/-- Discharge program address and label offset equalities for program(s) `ps`. -/
elab "kaddr" ps:ident+ : tactic => withMainContext do
  let solved ← withReducible do
    try (← getMainGoal).refl; pure true catch _ => pure false
  if solved then return
  evalTactic (← `(tactic| (try simp only [Kraken.Executable.addrOf_zero, Kraken.Executable.startAddr_apply, Kraken.Layout.start_shift])))
  if (← getUnsolvedGoals).isEmpty then return
  let goal ← getMainGoal
  let cleanGoal ← goal.withContext do
    let mut toClear : Array FVarId := #[]
    for localDecl? in (← getLCtx).decls do
      if let some localDecl := localDecl? then
        if localDecl.hasValue ||
           localDecl.type.getAppFn.isConstOf ``Std.ExtHashMap.sep ||
           localDecl.type.isAppOf ``Std.ExtHashMap then
          toClear := toClear.push localDecl.fvarId
    goal.tryClearMany toClear
  replaceMainGoal [cleanGoal]
  let target ← instantiateMVars (← getMainTarget)
  let extraDeclsRef ← IO.mkRef (#[] : Array Ident)
  target.forEach fun e => do
    if e.isAppOfArity ``List.length 2 then
      if let .const declName _ := e.appArg! then
        let extraDecls ← extraDeclsRef.get
        unless extraDecls.any (·.getId == declName) do
          extraDeclsRef.set (extraDecls.push (mkIdent declName))
  let extraDecls ← extraDeclsRef.get
  for p in ps ++ extraDecls do
    evalTactic (← `(tactic| (try delta $p)))
  evalTactic (← `(tactic|
    ((try simp [Kraken.Executable.addrOf_zero, Kraken.Layout.apply, Kraken.Executable.addrOf,
                Kraken.Executable.sizeBefore, Kraken.Executable.withAddresses,
                Executable.labels, Kraken.Executable.labels, Kraken.Executable.label,
                Labels.label, ArchDirective.label?,
                List.mapIdx_cons, List.mapIdx_nil, Int64.ofNat_add, Int64.add_assoc]);
     (try grind))))

private partial def extractDirectiveListElems (e : Expr) : MetaM (Array Expr) := do
  let mut cur := e
  let mut acc := #[]
  while true do
    if cur.isAppOfArity ``List.cons 3 then
      acc := acc.push (cur.getArg! 1)
      cur := cur.getArg! 2
    else if cur.isAppOfArity ``List.nil 1 then
      return acc
    else if let some unfolded ← unfoldDefinition? cur then
      cur := unfolded
    else
      throwError "kprologue: expected program to unfold to a literal list of directives"
  return acc

private def findLabelIdx (progIdent : Ident) (lbl : String) : TacticM Nat := do
  let declName ← resolveGlobalConstNoOverload progIdent
  let info ← getConstInfo declName
  let some val := info.value? | throwErrorAt progIdent "kprologue: `{declName}` has no value"
  let elems ← extractDirectiveListElems val
  for h : i in [0:elems.size] do
    let d := elems[i]
    if d.getAppFn.constName?.map (·.getString!) == some "label" &&
       d.getAppArgs.back? == some (mkStrLit lbl) then
      return i
  throwErrorAt progIdent "kprologue: label {repr lbl} not found in `{declName}`"

private def resolveDirectivePos (progIdent : Ident) (stx : TSyntax `term) :
    TacticM (TSyntax `term × Option Nat) := do
  if let some lbl := stx.raw.isStrLit? then
    let idx ← findLabelIdx progIdent lbl
    return (Syntax.mkNumLit (toString idx), some idx)
  else if let some idx := stx.raw.isNatLit? then
    return (stx, some idx)
  else
    return (stx, none)

/-- Set up a straight-line proof for `p` (optionally from `at <idx|"label">`, running `take <n>`
directives or `to <idx|"label">`, and destructuring `with s` where `status` and `dmem` are named
`flags` and `mem`). -/
syntax (name := kprologue) "kprologue" ident ("at" term)? ("take" term)? ("to" term)? ("with" ident)? : tactic

private def kprologueBinderName (field : Lean.Name) : Lean.Name :=
  if field == `status then `flags
  else if field == `dmem then `mem
  else field

private partial def mkAndSplitPat (e : Expr) : TacticM (TSyntax `rcasesPat) := do
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then
    let p1 ← mkAndSplitPat (e.getArg! 0)
    let p2 ← mkAndSplitPat (e.getArg! 1)
    `(rcasesPat| ⟨$p1, $p2⟩)
  else if e.isConstOf ``True then
    `(rcasesPat| -)
  else
    `(rcasesPat| _)

elab_rules : tactic
  | `(tactic| kprologue $p:ident $[at $kRaw?]? $[take $nRaw?]? $[to $toRaw?]? $[with $s?]?) => withMainContext do
      let targetInit := (← instantiateMVars (← getMainTarget)).consumeMData
      if targetInit.getAppFn'.constName? == some ``CtEventually then
        evalTactic (← `(tactic| unfold CtEventually))
      let targetEx := (← instantiateMVars (← getMainTarget)).consumeMData
      if targetEx.getAppFn'.constName? == some ``Exists then
        evalTactic (← `(tactic| (refine ⟨?_, ?_⟩; rotate_left)))
      let target0 := (← instantiateMVars (← getMainTarget)).consumeMData
      if target0.getAppFn'.constName? == some ``Kraken.Executable.Spec ||
         target0.getAppFn'.constName? == some ``Kraken.Executable.ExecSpec then
        evalTactic (← `(tactic| dsimp only [Kraken.Executable.Spec, Kraken.Executable.ExecSpec]))
      let target1 := (← instantiateMVars (← getMainTarget)).consumeMData
      if let .forallE _ reqType _ _ := target1 then
        let pat ← mkAndSplitPat reqType
        evalTactic (← `(tactic| rintro $pat:rcasesPat))
      evalTactic (← `(tactic| (try dsimp only [Kraken.Executable.startAddr_apply])))
      let curTarget := (← instantiateMVars (← getMainTarget)).consumeMData
      let isTraced := curTarget.getAppFn'.constName? == some ``TracedEventually
      let isTracedAccum := curTarget.isAppOfArity ``Eventually 4 &&
        (curTarget.getArg! 1).consumeMData.getAppFn'.constName? == some ``step1Traced
      let sliceThm := mkIdent (if isTraced then ``step1_cps_slice_traced else if isTracedAccum then ``step1_cps_slice_accum else ``step1_cps_slice)
      let atThm := mkIdent (if isTraced then ``step1_cps_at_traced else if isTracedAccum then ``step1_cps_at_accum else ``step1_cps_at)
      let cpsThm := mkIdent (if isTraced then ``step1_cps_traced else ``step1_cps)
      let (k?, startIdx?) ← match kRaw? with
        | some kRaw =>
          let (kTerm, idx?) ← resolveDirectivePos p kRaw
          pure (some kTerm, idx?)
        | none => pure (none, some 0)
      let n? ← match nRaw?, toRaw? with
        | some nRaw, none => pure (some nRaw)
        | none, some toRaw =>
          let (_, endIdx?) ← resolveDirectivePos p toRaw
          let (some startIdx, some endIdx) := (startIdx?, endIdx?)
            | throwErrorAt toRaw "kprologue: `to` requires statically known start and end positions"
          if endIdx < startIdx then
            throwErrorAt toRaw "kprologue: target position ({endIdx}) precedes start position ({startIdx})"
          pure (some (Syntax.mkNumLit (toString (endIdx - startIdx))))
        | none, none => pure none
        | some _, some toRaw => throwErrorAt toRaw "kprologue: cannot specify both `take` and `to`"
      match s? with
      | none =>
        match k?, n? with
        | some k, some n =>
          evalTactic (← `(tactic|
            (refine $sliceThm $k $n _ (by kaddr $p) ?_
             conv =>
               arg 2
               rw [Kraken.Executable.program_apply_slice]
               (try delta $p)
               simp only [Kraken.Layout.apply, List.mapIdx_cons, List.mapIdx_nil,
                          List.drop_succ_cons, List.drop_zero, List.drop_nil,
                          List.take_succ_cons, List.take_zero, List.take_nil,
                          Nat.add_zero, Nat.zero_add, Nat.reduceAdd])))
        | none, some n =>
          evalTactic (← `(tactic|
            (refine $sliceThm 0 $n _ (by kaddr $p) ?_
             conv =>
               arg 2
               rw [Kraken.Executable.program_apply_slice]
               (try delta $p)
               simp only [Kraken.Layout.apply, List.mapIdx_cons, List.mapIdx_nil,
                          List.drop_succ_cons, List.drop_zero, List.drop_nil,
                          List.take_succ_cons, List.take_zero, List.take_nil,
                          Nat.add_zero, Nat.zero_add, Nat.reduceAdd])))
        | some k, none =>
          evalTactic (← `(tactic|
            (refine $atThm $k _ (by kaddr $p) ?_
             conv =>
               arg 2
               rw [Kraken.Executable.program_apply_drop]
               (try delta $p)
               simp only [Kraken.Layout.apply, List.mapIdx_cons, List.mapIdx_nil,
                          List.drop_succ_cons, List.drop_zero, List.drop_nil,
                          Nat.add_zero, Nat.zero_add, Nat.reduceAdd])))
        | none, none =>
          let isEventually := isTraced || isTracedAccum || (← whnfR (← instantiateMVars (← getMainTarget))).getAppFn'.constName? == some ``Eventually
          if isEventually then
            evalTactic (← `(tactic|
              (apply $cpsThm
               (try
                 conv =>
                   arg 1
                   ext
                   ext
                   arg 2
                   simp)
               conv =>
                 arg 2
                 (try delta $p)
                 rw [Executable.directivesFromStart]
                 simp only [Kraken.Layout.apply, List.mapIdx_cons, List.mapIdx_nil,
                            Nat.add_zero, Nat.zero_add, Nat.reduceAdd])))
          else
            evalTactic (← `(tactic|
              ((try unfold Kraken.Executable.Exec Kraken.Executable.ExecTraced)
               conv =>
                 arg 2
                 (try rw [Kraken.Executable.program_apply])
                 (try delta $p)
                 (try rw [Executable.directivesFromStart])
                 simp only [Kraken.Layout.apply, Kraken.Executable.startAddr_apply,
                            List.mapIdx_cons, List.mapIdx_nil,
                            Nat.add_zero, Nat.zero_add, Nat.reduceAdd])))
      | some s =>
        let env ← getEnv
        let state ← Term.elabTerm s none
        let stateType ← whnf (← inferType state)
        let some stateName := stateType.getAppFn.constName?
          | throwErrorAt s "kprologue: expected a state with a structure type"
        let some _ := getStructureInfo? env stateName
          | throwErrorAt s "kprologue: `{stateName}` is not a structure"

        let stateFields := getStructureFields env stateName
        let some regsInfo := getFieldInfo? env stateName `regs
          | throwErrorAt s "kprologue: `{stateName}` has no `regs` field"
        let regs ← mkAppM regsInfo.projFn #[state]
        let regsType ← whnf (← inferType regs)
        let some regsName := regsType.getAppFn.constName?
          | throwErrorAt s "kprologue: `{stateName}.regs` does not have a structure type"
        let some _ := getStructureInfo? env regsName
          | throwErrorAt s "kprologue: `{stateName}.regs` is not a structure"

        let regFields := getStructureFields env regsName
        let stateBinderNames :=
          (stateFields.filter (· != `regs)).map kprologueBinderName
        let binderNames := regFields ++ stateBinderNames

        let mut seen : NameSet := {}
        let mut duplicateNames := #[]
        for name in binderNames do
          if seen.contains name then
            unless duplicateNames.contains name do
              duplicateNames := duplicateNames.push name
          else
            seen := seen.insert name
        unless duplicateNames.isEmpty do
          let names := String.intercalate ", " (duplicateNames.toList.map (·.toString))
          throwErrorAt s "kprologue: duplicate local names: {names}"

        let lctx ← getLCtx
        let collisions := binderNames.filter fun name =>
          (lctx.findFromUserName? name).isSome
        unless collisions.isEmpty do
          let names := String.intercalate ", " (collisions.toList.map (·.toString))
          throwErrorAt s
            "kprologue: refusing to shadow existing locals: {names}"

        -- These binders must remain visible after the tactic, so give them no macro scopes.
        let regPats ← regFields.mapM fun field =>
          let id := mkIdentFrom s field
          `(rcasesPat| $id:ident)
        let regsPat ← `(rcasesPat| ⟨$[$regPats],*⟩)
        let statePats ← stateFields.mapM fun field =>
          if field == `regs then
            pure regsPat
          else
            let id := mkIdentFrom s (kprologueBinderName field)
            `(rcasesPat| $id:ident)
        let statePat ← `(rcasesPat| ⟨$[$statePats],*⟩)

        match k?, n? with
        | some k, some n =>
          evalTactic (← `(tactic|
            (refine $sliceThm (prog := $p) $k $n _ (s := $s) (by kaddr $p) ?_
             let ss := $s
             change (Kraken.Effects.All _ (@Directives.interp _ _ _ (Kraken.Executable.labels _) _ ss _ _))
             obtain $statePat:rcasesPat := $s
             (try dsimp only at *)
             conv =>
               arg 2
               rw [Kraken.Executable.program_apply_slice]
               (try delta $p)
               simp only [Kraken.Layout.apply, List.mapIdx_cons, List.mapIdx_nil,
                          List.drop_succ_cons, List.drop_zero, List.drop_nil,
                          List.take_succ_cons, List.take_zero, List.take_nil,
                          Nat.add_zero, Nat.zero_add, Nat.reduceAdd])))
        | none, some n =>
          evalTactic (← `(tactic|
            (refine $sliceThm (prog := $p) 0 $n _ (s := $s) (by kaddr $p) ?_
             let ss := $s
             change (Kraken.Effects.All _ (@Directives.interp _ _ _ (Kraken.Executable.labels _) _ ss _ _))
             obtain $statePat:rcasesPat := $s
             (try dsimp only at *)
             conv =>
               arg 2
               rw [Kraken.Executable.program_apply_slice]
               (try delta $p)
               simp only [Kraken.Layout.apply, List.mapIdx_cons, List.mapIdx_nil,
                          List.drop_succ_cons, List.drop_zero, List.drop_nil,
                          List.take_succ_cons, List.take_zero, List.take_nil,
                          Nat.add_zero, Nat.zero_add, Nat.reduceAdd])))
        | some k, none =>
          evalTactic (← `(tactic|
            (refine $atThm (prog := $p) $k _ (s := $s) (by kaddr $p) ?_
             let ss := $s
             change (Kraken.Effects.All _ (@Directives.interp _ _ _ (Kraken.Executable.labels _) _ ss _ _))
             obtain $statePat:rcasesPat := $s
             (try dsimp only at *)
             conv =>
               arg 2
               rw [Kraken.Executable.program_apply_drop]
               (try delta $p)
               simp only [Kraken.Layout.apply, List.mapIdx_cons, List.mapIdx_nil,
                          List.drop_succ_cons, List.drop_zero, List.drop_nil,
                          Nat.add_zero, Nat.zero_add, Nat.reduceAdd])))
        | none, none =>
          let isEventually := isTraced || isTracedAccum || (← whnfR (← instantiateMVars (← getMainTarget))).getAppFn'.constName? == some ``Eventually
          if isEventually then
            evalTactic (← `(tactic|
              (apply $cpsThm
               let ss := $s
               change (Kraken.Effects.All _ (@Directives.interp _ _ _ (Kraken.Executable.labels _) _ ss _ _))
               obtain $statePat:rcasesPat := $s
               (try dsimp only at *)
               (try
                 conv =>
                   arg 1
                   ext
                   ext
                   arg 2
                   simp)
               conv =>
                 arg 2
                 (try delta $p)
                 rw [Executable.directivesFromStart]
                 simp only [Kraken.Layout.apply, List.mapIdx_cons, List.mapIdx_nil,
                            Nat.add_zero, Nat.zero_add, Nat.reduceAdd])))
          else
            evalTactic (← `(tactic|
              ((try unfold Kraken.Executable.Exec Kraken.Executable.ExecTraced)
               let ss := $s
               change (Kraken.Effects.All _ (@Directives.interp _ _ _ _ _ ss _ _))
               obtain $statePat:rcasesPat := $s
               (try dsimp only at *)
               conv =>
                 arg 2
                 (try rw [Kraken.Executable.program_apply])
                 (try delta $p)
                 (try rw [Executable.directivesFromStart])
                 simp only [Kraken.Layout.apply, Kraken.Executable.startAddr_apply,
                            List.mapIdx_cons, List.mapIdx_nil,
                            Nat.add_zero, Nat.zero_add, Nat.reduceAdd])))

/-- Pack curried secret universal quantifiers after `s₀` into a single tuple so that
    `tailrec_loop_cps_traced` can be applied directly to a `Spec (trace := some tr)` goal. -/
elab "kpack_secrets" : tactic => do
  evalTactic (← `(tactic|
    (simp only [Kraken.Executable.Spec, forall_prod_curry]
     rw [exists_forall_unpack_first]
     dsimp only)))

/-- Peel a leading `CtEventually` or `∃ tr, ...` trace witness (deferring unification to `kdone`)
    and introduce universal / precondition binders with `rintro`. -/
elab "kintro" pats:(colGt rcasesPat)* : tactic =>
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    if target.getAppFn'.constName? == some ``CtEventually then
      evalTactic (← `(tactic| unfold CtEventually))
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    if target.getAppFn'.constName? == some ``Exists then
      evalTactic (← `(tactic| (refine ⟨?_, ?_⟩; rotate_left)))
    unless pats.isEmpty do
      evalTactic (← `(tactic| rintro $[$pats:rcasesPat]*))
    evalTactic (← `(tactic| (try dsimp only at *)))

private def unifyTraceWitness (trExpected trActual : Expr) : TacticM Unit := do
  let savedDepth := (← getMCtx).depth
  let ok ← withAssignableSyntheticOpaque do
    if trExpected.getAppFn.isMVar then
      let decl ← trExpected.getAppFn.mvarId!.getDecl
      modifyMCtx fun mctx => { mctx with depth := decl.depth }
    try
      isDefEq trExpected trActual
    finally
      modifyMCtx fun mctx => { mctx with depth := savedDepth }
  unless ok do
    throwError "kdone: leakage trace depends on secret state and cannot unify with public trace:\n  expected: {trExpected}\n  actual:   {trActual}"
  pruneSolvedGoals

/-- Finish a stepped `TracedEventually`, `ExecTraced`, or `Eventually` goal, unifying any
    synthetic-opaque trace witness metavariable with the accumulated concrete leakage trace. -/
elab "kdone" : tactic =>
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    if target.isAppOfArity ``Eventually 4 then
      let postArg := (target.getArg! 2).consumeMData
      let stateArg := (target.getArg! 3).consumeMData
      if postArg.isAppOfArity ``TracedGoal 3 && stateArg.isAppOfArity ``Prod.mk 4 then
        let trExpected := (← instantiateMVars (postArg.getArg! 2)).consumeMData
        let trActual := (← instantiateMVars (stateArg.getArg! 3)).consumeMData
        unifyTraceWitness trExpected trActual
        evalTactic (← `(tactic| apply TracedEventually.done))
      else
        evalTactic (← `(tactic| apply Eventually.done))
    else if target.isAppOfArity ``TracedGoal 4 then
      let stateArg := (target.getArg! 3).consumeMData
      if stateArg.isAppOfArity ``Prod.mk 4 then
        let trExpected := (← instantiateMVars (target.getArg! 2)).consumeMData
        let trActual := (← instantiateMVars (stateArg.getArg! 3)).consumeMData
        unifyTraceWitness trExpected trActual
        evalTactic (← `(tactic| apply TracedGoal.done))
      else
        evalTactic (← `(tactic| apply TracedGoal.done))
    else
      evalTactic (← `(tactic| apply Eventually.done))

--------------------------------------------------------------------------------

open Sym Sym.DSimp

partial def peelLambdaLets (f : Expr) (args : Array Expr) (fvars : Array Expr) (k : Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  -- (fun y => let x = e1 in e2) () ~~> let x = e1 in (fun y => e2) ()
  match f with
  | .lam binderName binderType body binderInfo =>
    match body with
    | .letE letName letType letVal letBody _ =>
      if !letType.hasLooseBVar 0 && !letVal.hasLooseBVar 0 then
        withLetDecl letName letType letVal fun fvarLet => do
          -- substitute open variable x for 0 in e2, shifting all other variables by 1
          let instBody : Expr := letBody.instantiate1 fvarLet
          -- meaning we can close in DeBruijn directly
          let newLambda := .lam binderName binderType instBody binderInfo
          -- and add our open variable to the list of variables to be folded over
          peelLambdaLets newLambda args (fvars.push fvarLet) k
      else
        k (mkAppN f args) fvars
    | _ => k (mkAppN f args) fvars
  | _ => k (mkAppN f args) fvars

partial def peelLets (e : Expr) (fvars : Array Expr) (k : Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  match e with
  | .letE name type val body _ =>
    withLetDecl name type val fun fvar =>
      peelLets (body.instantiate1 fvar) (fvars.push fvar) k
  | _ =>
    if e.isApp && e.getAppFn.isLambda then
      peelLambdaLets e.getAppFn e.getAppArgs fvars k
    else
      k e fvars

partial def peelArgsLets (args : Array Expr) (i : Nat) (peeled : Array Expr) (fvars : Array Expr) (k : Array Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  if h : i < args.size then
    let arg := args[i]
    peelLets arg fvars fun arg' fvars' =>
      peelArgsLets args (i + 1) (peeled.push arg') fvars' k
  else
    k peeled fvars

def kdeltaBetaOnly (targets: List Name) (maxInstrCount : Option (IO.Ref Nat)) : DSimproc := fun e => do
  -- This focuses on application nodes.
  unless e.isApp && targets.any e.getAppFn'.isConstOf do return .rfl

  let f := e.getAppFn'
  let args := e.getAppArgs

  -- In order to unblock reduction, Meta.unfoldDefinition will happily inline
  -- away let-bindings to make e.g. a constructor appear as an argument to a
  -- match recursor. We intervene ahead of time, and hoist the lets that appear in
  -- argument position, which we know for a fact happens quite a bunch in our
  -- semantics. Concretely: `f (let x = ... in arg)` => `let x = ... in f arg`.
  peelArgsLets args 0 #[] #[] fun (args : Array Expr) (fvars : Array Expr) => do

    if f.isConstOf ``Kraken.Effects.All && args.back!.isApp && args.back!.getAppFn'.isConstOf ``Directives.interp then
      -- We optionally track how many times we've hit Directives.interp -- this tracks how
      -- many instructions we've stepped through.
      if (← maxInstrCount.mapM (·.get)) = .some 0 then
        return .rfl
      maxInstrCount.forM (fun r => r.modify (· - 1))

      -- Finding a node of the form `Effects.All ... (Directives.interp ...)`
      -- means that we are ready to step through. We manually force reduction of
      -- Directives.interp (since it is *not* is our list of targets), then let
      -- everything simplify until we're called again.
      let some argLast ← Meta.unfoldDefinition? args.back! true | throwError "can't unfold Directives.interp"
      let e := mkAppN f (args.set! (args.size - 1) argLast)
      let e' ← shareCommon e
      let e'' ← mkLetFVars fvars e'
      return .step e''
      -- TODO: we could here have a post := in the simproc that forces the
      -- result to be .step ... (done := true) to prevent the next unrolling of
      -- Directives.interp from being applied. This would essentially allow
      -- implementing a kstep1 tactic (and leave it to done := false to keep
      -- stepping until something blocks).

      -- Essentially this behavior allows us to keep reducing and stepping,
      -- until we have no steps left to apply and YET the goal has landed us
      -- back on something that is neither Effects.All ... (Directives.interp
      -- ...), nor Effects.All ... (require_exec_access ...), handled in the
      -- case below.
    else
      -- Application, *sans* the let-bindings in the arguments.
      let e_rebuilt := mkAppN f args
      -- Remember that `Meta.unfoldDefinition` is "smart" and wants to see the whole
      -- application node `f ...` before deciding whether it's worth doing a step of
      -- delta and replacing `f` with its definition.
      if let some e' ← Meta.unfoldDefinition? e_rebuilt true then
        /- let step := (← get).numSteps -/
        /- logInfo m!"deltaBetaOnly {step}: {e_rebuilt}\nunfolds to:{e'}" -/
        let e' ← shareCommon e'
        let e'' ← betaRevS e'.getAppFn e'.getAppRevArgs
        let e'' ← mkLetFVars fvars e''
        /- logInfo m!"deltaBetaOnly {step}: {e}\nunfolds to:{e'}\nreduces to: {e''}" -/
        return .step e''
      else if fvars.size > 0 then
        -- Can't reduce application, but we should at least hoist the lets!
        let e ← mkLetFVars fvars e_rebuilt
        return .step e
      else
        -- Really nothing to do here.
        return .rfl

def gimmickId (p: Prop): Prop := p

theorem gimmick {p: Prop} (h: gimmickId p): p := by
  simp [gimmickId] at h
  assumption

theorem gimmickInv {p: Prop} (h: p): gimmickId p := by
  simp [gimmickId]
  assumption

-- Enable with `set_option trace.Kraken.kstep true`.
initialize registerTraceClass `Kraken.kstep

-- Debugging the reduction steps: to easily have a marker that tells us when we've hit the top-level
-- term, we assume prior to running `kstep`, the user does `apply gimmick`. (This also avoids having
-- to reason about whether we're at the top-level term or not -- we never are.)
def klog : DSimproc := fun e => do
  -- Trace every top-level term to show the various states of the dsimp
  -- call.
  let s := (← get).numSteps
  /- if s = 789 then -/
  /-   return .rfl (done := true) -/
  if e.isApp && e.getAppFn'.isConstOf ``gimmickId then
    trace[Kraken.kstep] "step {s} visiting\n{e.getAppRevArgs[0]!}"
  return .rfl

structure KStepConfig where
  debug := false
declare_term_config_elab elabKStepConfig KStepConfig

syntax (name := symKStep) "kstep" optConfig (ppSpace num)? : grind

def kdsimpMatch: DSimproc := fun e => do
  if e.hasLooseBVars then return .rfl
  if e.isAppOfArity ``ite 5 then
    let c := e.getArg! 1
    if !c.hasFVar && !c.hasLooseBVars then
      let inst ← whnf (e.getArg! 2)
      if inst.isAppOfArity ``Decidable.isTrue 2 then
        return .step (← share (e.getArg! 3))
      if inst.isAppOfArity ``Decidable.isFalse 2 then
        return .step (← share (e.getArg! 4))
  let some e' ← reduceRecMatcher? e | return .rfl
  -- Iota-reduction may expose kernel `Expr.proj` terms via struct-eta,
  -- which the structural simplifier cannot consume directly.
  let e'' ← Sym.foldProjs e'
  if isSameExpr e e'' then
    return .rfl
  else
    return .step (← share e'')

def kbeta: DSimproc := fun e => do
  unless e.isApp do return .rfl
  let f := e.getAppFn
  if f.isHeadBetaTargetFn false then
    let e' ← betaRevS f e.getAppRevArgs
    /- let step := (← get).numSteps -/
    /- logInfo m!"kbeta {step}: {e}\nreduces to\n{e'}" -/
    return .step e'
  else
    return .rfl

def kdsimpProj : DSimproc := fun e => do
  if e.hasLooseBVars then return .rfl
  let f := e.getAppFn
  let .const declName _ := f | return .rfl
  let some projInfo ← getProjectionFnInfo? declName | return .rfl
  let reduceProjCont? (e? : Option Expr) : DSimpM Result := do
    match e? with
    | none   => return .rfl
    | some e =>
      match (← reduceProj? e.getAppFn) with
      | some f => return .step (← share (mkAppN f e.getAppArgs))
      | none   => return .rfl
  if projInfo.fromClass then
    unless e.getAppNumArgs > projInfo.numParams do
      return .rfl
    let major := e.getArg! projInfo.numParams
    unless (← isConstructorApp major) do
      return .rfl
    if backward.whnf.reducibleClassField.get (← getOptions) then
      let some e' ← unfoldDefinition? e (ignoreTransparency := true) | return .rfl
      return .step (← share e')
    else
      reduceProjCont? (← unfoldDefinition? e (ignoreTransparency := true))
  else
    reduceProjCont? (← unfoldDefinition? e)

def kLiftLets : DSimproc := fun e => do
  -- We only lift lets to the top-level (which is always an application of
  -- Effects.all)
  unless e.isApp && e.getAppFn'.isConstOf ``Kraken.Effects.All do return .rfl

  let (es, st) ← ExtractLets.extract #[e] |>.run {} |>.run' {} |>.run { givenNames := [] }
  unless st.decls.size > 0 do return .rfl

  let e' := Meta.ExtractLets.mkLetDecls st.decls es[0]!
  let e' ← Sym.share e'
  /- logInfo m!"liftLets produces {e'}" -/
  return .step e'

-- FIXME: a copy-paste of the Lean implementation since it's marked as private
def rwTarget (goal: Grind.Goal) (symm : Bool) (term : Expr) : Grind.GrindTacticM (Grind.Goal × List Grind.Goal) := do
  goal.withContext do
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let r ← Term.withSynthesize do
      let heq := term
      /-
      The target is in `sym` normal form (e.g., reducible constants have been unfolded), but the
      given equation is not. We unfold reducible constants in its statement so that `kabstract`
      key-matching can find occurrences of the lhs in the target, and the rhs requires less
      normalization after the rewrite.
      -/
      let heqType ← instantiateMVars (← inferType heq)
      let heqType' ← Sym.unfoldReducible heqType
      let heq ← if isSameExpr heqType heqType' then pure heq else mkExpectedTypeHint heq heqType'
      goal.mvarId.rewrite (← instantiateMVars (← goal.mvarId.getType)) heq symm
    let mctx ← getMCtx
    let mvarIds := r.mvarIds.filter fun mvarId => (mctx.getDecl mvarId |>.index) >= mvarCounterSaved
    let eNew ← Grind.liftSymM <| Sym.preprocessExpr r.eNew
    let mvarId ← goal.mvarId.replaceTargetEq eNew r.eqProof
    let mvarIds ← mvarIds.filterM fun mvarId => return !(← mvarId.isAssigned)
    let sideGoals ← mvarIds.mapM fun mvarId => do
      let target ← mvarId.getType
      let targetInst ← instantiateMVars target
      let target' ← Grind.liftSymM <| Sym.preprocessExpr targetInst
      if isSameExpr target target' then
        -- The metavariable was created by `forallMetaTelescopeReducing` with kind `.natural`;
        -- prevent it from being assigned by unification in later steps.
        mvarId.setKind .syntheticOpaque
        return { goal with mvarId }
      else
        let mvarId ← mvarId.replaceTargetDefEq target'
        return { goal with mvarId }
    pure ({ goal with mvarId }, sideGoals)

@[grind_tactic symKStep]
partial def evalSymKStep : Grind.GrindTactic :=
  fun stx : Syntax => do
  let cfg := stx[1]
  let config ← elabKStepConfig cfg
  let maxSteps? : Option Nat := if stx[2].isNone then none else some stx[2][0].toNat
  -- A `sym` tactic operates over a pair of the grind state and an MVarId. To avoid scope mistakes,
  -- we only ever use `goal` and never let-bind mvarId.
  let goal : Grind.Goal ← Grind.getMainGoal

  let gimmickRule ← mkBackwardRuleFromDecl ``gimmick
  let insertGimmick (goal: Grind.Goal): Grind.GrindTacticM Grind.Goal := do
    let .goals [mvarId] ← Grind.liftGrindM (gimmickRule.apply goal.mvarId) | failure
    pure { goal with mvarId }

  let gimmickRule ← mkBackwardRuleFromDecl ``gimmickInv
  let removeGimmick (goal: Grind.Goal): Grind.GrindTacticM Grind.Goal := do
    let mvarId ← Grind.liftGrindM (do
      let .goals [mvarId] ← gimmickRule.apply goal.mvarId | failure
      pure mvarId
    )
    pure { goal with mvarId }

  -- Apply the debug gimmick. We actually *do* expect the goal to be in this form (see comment in
  -- kdeltaBetaOnly).
  let goal ← insertGimmick goal

  let env ← getEnv

  let declsForDSimp := (kstepExtension.getState env).toList
  let maxInstrCount ← maxSteps?.mapM (IO.mkRef ·)
  let kdsimpDecls := kdeltaBetaOnly declsForDSimp maxInstrCount
  let dsimpCore := evalGround >> kdsimpDecls >> kdsimpMatch >> kdsimpProj >> kbeta
  let dsimpPre := if ← isTracingEnabledFor `Kraken.kstep then klog >> dsimpCore else dsimpCore

  -- https://lean-lang.org/doc/api/Lean/Meta/Sym/Simp/SimpM.html
  -- note the "contextual ite handling" --> are we doing this?
  let simpTheorems ← ksimpExt.getTheorems
  let simpMethods: Sym.Simp.Methods := { post := Sym.Simp.evalGround >> simpTheorems.rewrite }

  let specLemmas := (kspecExtension.getState env).toList
  let specTree: DiscrTree Name ← specLemmas.foldlM (fun specTree name => do
    -- NOTE: hardcoding left-to-right order, for now
    let (pat, _) ← mkEqPatternFromDecl name
    pure (insertPattern specTree pat name)
  ) {}

  let preprocessGoalIfNeeded (goal : Grind.Goal) : Grind.GrindTacticM Grind.Goal := do
    let target ← goal.mvarId.getType
    unless target.hasExprMVar do return goal
    let targetInst ← instantiateMVars target
    if isSameExpr target targetInst then return goal
    let target' ← Grind.liftSymM (Sym.preprocessExpr targetInst)
    let mvarId ← goal.mvarId.replaceTargetDefEq target'
    return { goal with mvarId }

  -- TODO: remove once we have lift_lets
  let introsIf (goal: Grind.Goal): Grind.GrindTacticM Grind.Goal := do
    let goalT ← instantiateMVars (← goal.mvarId.getType)
    let_expr gimmickId inner := goalT | return goal
    let inner := inner.consumeMData
    unless inner.isLet || inner.isForall do return goal
    let goal ← removeGimmick goal
    let goal ← match ← Grind.liftGrindM (goal.intros #[]) with
      | Grind.IntrosResult.failed => pure goal
      | .goal _ goal => pure goal
    pure (← insertGimmick goal)

  -- MAIN LOOP
  let rec go (goal: Grind.Goal): Grind.GrindTacticM (Grind.Goal × List Grind.Goal) := do
    let goal ← goal.withContext (preprocessGoalIfNeeded goal)
    -- STEP 1: dsimp
    let goal ← goal.withContext do
      let mvarId ← goal.mvarId.replaceTargetDefEq (← Grind.liftGrindM $
        Sym.dsimp
          (config := { maxSteps := 1000000 })
          (methods := { pre := dsimpPre })
          (← goal.mvarId.getType))
      introsIf ({ goal with mvarId })

    goal.withContext do
    if config.debug then
      let _ ← goal.mvarId.getType
      logInfo m!"MAIN LOOP, after step 1: {goal.mvarId}"

    -- STEP 2: simp
    let (keepGoingSimp, goal) ← Grind.liftGrindM $ do
      let simpResult ← Sym.simpGoal goal.mvarId simpMethods
      match simpResult with
      | .noProgress => pure (false, goal)
      | .goal mvarId => pure (true, { goal with mvarId })
      | .closed => throwError "unexpected"
    if config.debug then
      let t ← instantiateMVars (← goal.mvarId.getType)
      logInfo m!"MAIN LOOP, after step 2: {t}"

    -- STEP 3: spec lemmas
    let effectsAll ← do
      let goalT ← goal.mvarId.getType
      let_expr gimmickId goalT' := goalT | throwError "missing gimmick"
      let goalT' ← instantiateMVars goalT'
      let rec getEffectsAll (e : Expr) : Option Expr :=
        match e with
        | .letE _ _ _ body _ => getEffectsAll body
        | .mdata _ e => getEffectsAll e
        | _ =>
          if e.isAppOfArity ``Kraken.Effects.All 3 then
            some e
          else
            none
      -- No more Effects.All in the goal -- return to the user (we might be done,
      -- or realistically, we might need to debug).
      let some effectsAll := getEffectsAll goalT' | return (goal, [])
      pure effectsAll

    let mctx ← getMCtx
    let m := Sym.getMatch mctx specTree effectsAll
    let specMatches := if m.isEmpty then Sym.getMatch mctx specTree effectsAll.appArg! else m

    let rec expandLets (e : Expr) : MetaM Expr := do
      let e ← if e.hasExprMVar then instantiateMVars e else pure e
      match e with
      | .fvar fvarId =>
        if let some localDecl ← fvarId.findDecl? then
          if let some val := localDecl.value? then
            return ← expandLets val
        return e
      | .letE _ _ v b _ =>
        let v' ← expandLets v
        expandLets (b.instantiate1 v')
      | .app f a =>
        return e.updateApp! (← expandLets f) (← expandLets a)
      | .mdata _ b =>
        expandLets b
      | .proj _ _ s =>
        return e.updateProj! (← expandLets s)
      | _ => return e

    let (keepGoingSpec, goal) ←
      match specMatches with
      | #[ thmName ] =>
        trace[Kraken.kstep] "Found a spec lemma: {thmName}"
        let (goal, subGoals) ← rwTarget goal false (mkConst thmName)
        trace[Kraken.kstep] "{subGoals.length} subgoals generated"

        -- Found a spec lemma, which will generate subgoals; subgoals (if not solved
        -- already!) are solved via ecancel, ksimp, exact, refl, or grind.
        let solveIfNotAlready : Grind.Goal → Grind.GrindTacticM (Bool × Grind.Goal) := fun subGoal => do
          -- Already solved this subgoal; skip
          if ← subGoal.mvarId.isAssigned then
            return (false, subGoal)

          let subGoal ← subGoal.mvarId.withContext (preprocessGoalIfNeeded subGoal)
          let t ← subGoal.mvarId.getType
          unless ← subGoal.mvarId.withContext (isProp t) do
            return (false, subGoal)

          -- Try ecancel on separation-logic goals
          if t.getAppFn.isConstOf ``Std.ExtHashMap.sep then
            if ← Kraken.Tactic.ecancelGoal subGoal.mvarId then
              trace[Kraken.kstep] "Solved by ecancel: {t}"
              return (true, subGoal)

          -- Try simp with @[ksimp]
          let subGoal ← do
            let simpResult ← Grind.liftGrindM (Sym.simpGoal subGoal.mvarId simpMethods)
            match simpResult with
            | .noProgress => pure subGoal
            | .goal mvarId => pure { subGoal with mvarId }
            | .closed => pure subGoal
          if ← subGoal.mvarId.isAssigned then
            trace[Kraken.kstep] "Solved by ksimp: {t}"
            return (true, subGoal)

          -- Solvable with exact; we made progress
          if ← withReducible subGoal.mvarId.assumptionCore then
            let t ← instantiateMVars (← subGoal.mvarId.getType)
            let .some e ← getExprMVarAssignment? subGoal.mvarId | throwError "oh noes"
            trace[Kraken.kstep] "Solved by exact: {t} by {e}"
            return (true, subGoal)

          let clearSepAndLets (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
            let mut toClear : Array FVarId := #[]
            for localDecl? in (← getLCtx).decls do
              if let some localDecl := localDecl? then
                if localDecl.hasValue ||
                   localDecl.type.getAppFn.isConstOf ``Std.ExtHashMap.sep ||
                   localDecl.type.isAppOf ``Std.ExtHashMap then
                  toClear := toClear.push localDecl.fvarId
            mvarId.tryClearMany toClear

          let t ← instantiateMVars (← subGoal.mvarId.getType)
          if !t.hasExprMVar then
            -- Solvable with refl, maybe.
            try
              subGoal.mvarId.refl
              trace[Kraken.kstep] "Solved by refl: {t}"
              return (true, subGoal)
            catch _ => pure ()

            -- Try solving with grind, roll back state otherwise (we don't want to
            -- return the failed Grind state).
            let saved ← Grind.saveState
            try
              let cleanMVarId ← clearSepAndLets subGoal.mvarId
              let g ← Grind.liftGrindM (Grind.mkGoal cleanMVarId)
              let g ← Grind.liftGrindM g.internalizeAll
              match ← Grind.liftGrindM g.grind with
              | .closed =>
                  trace[Kraken.kstep] "Solved by grind: {t}"
                  return (true, subGoal)
              | .failed _ =>
                  trace[Kraken.kstep] "NOT solved by grind: {t}"
                  saved.restore
                  return (false, subGoal)
            catch _ =>
              saved.restore
              return (false, subGoal)
          return (false, subGoal)

        -- For this reason, we try to be intentional about the order in which we solve subgoals:
        -- solving the ⋆ separation logic predicate first allows making sensible decisions about
        -- metavariables, rather than picking any random hypothesis in the context
        let starGoal ← subGoals.findM? (fun (g : Grind.Goal) => do
          let t ← instantiateMVars (← g.mvarId.getType)
          if t.getAppFn.isConstOf ``Std.ExtHashMap.sep then
            trace[Kraken.kstep] "Found sep goal: {t}"
            return true
          else
            return false
        )

        -- If we couldn't solve the ⋆ goal, we are likely going to make bad
        -- decisions and instantiate metavariables randomly. Abort.
        let mut subGoals := subGoals
        if let some g := starGoal then
          let addrGoal? ← subGoals.findM? fun (sg : Grind.Goal) => do
            if sg.mvarId == g.mvarId then return false
            let t ← instantiateMVars (← sg.mvarId.getType)
            unless t.isAppOfArity ``Eq 3 do return false
            return t.appArg!.isMVar
          let solved ←
            if let some addrGoal := addrGoal? then
              let addrGoalType ← instantiateMVars (← addrGoal.mvarId.getType)
              let addr := addrGoalType.appFn!.appArg!
              let addrMVar := addrGoalType.appArg!
              let candidates ← Kraken.Tactic.findSepAtCandidates g.mvarId
              let tryAssignAndCancel (cand : Kraken.Tactic.SepAtCandidate) (hEq : Expr) : Grind.GrindTacticM Bool := do
                withConfig (fun c => { c with assignSyntheticOpaque := true }) do
                  unless ← isDefEq addrMVar cand.addr do return false
                  addrGoal.mvarId.assign hEq
                  Kraken.Tactic.solveSepAtCandidate g.mvarId cand
              let simplifyAddrEq (candAddr : Expr) : Grind.GrindTacticM (Expr × Grind.Goal) :=
                addrGoal.mvarId.withContext do
                  let eqType ← mkEq addr candAddr
                  let eqMVar ← mkFreshExprSyntheticOpaqueMVar eqType
                  let eqType' ← expandLets eqType
                  let eqType' ← Grind.liftSymM (Sym.preprocessExpr eqType')
                  let eqType' ← Grind.liftGrindM <|
                    Sym.dsimp (config := { maxSteps := 100000 })
                      (methods := { pre := evalGround >> kdsimpDecls >> kdsimpMatch >> kdsimpProj >> kbeta })
                      eqType'
                  let mvarId ← eqMVar.mvarId!.replaceTargetDefEq eqType'
                  let eqGoal : Grind.Goal := { addrGoal with mvarId }
                  let eqGoal ← do
                    let r ← Grind.liftGrindM (Sym.simpGoal eqGoal.mvarId simpMethods)
                    match r with
                    | .noProgress => pure eqGoal
                    | .goal mvarId => pure { eqGoal with mvarId }
                    | .closed => pure eqGoal
                  pure (eqMVar, eqGoal)
              -- Pass 1: fast syntactic / reducible isDefEq check across all candidate clauses
              let mut solvedSep := false
              for cand in candidates do
                unless solvedSep do
                  let saved ← Grind.saveState
                  try
                    if ← addrGoal.mvarId.withContext (withReducible (isDefEq addr cand.addr)) then
                      let hEq ← addrGoal.mvarId.withContext (mkEqRefl addr)
                      if ← tryAssignAndCancel cand hEq then
                        solvedSep := true
                      else
                        saved.restore
                    else
                      saved.restore
                  catch _ =>
                    saved.restore
              -- Pass 2: unfold local lets + ksimp, then check if closed or reducible isDefEq
              unless solvedSep do
                for cand in candidates do
                  unless solvedSep do
                    let saved ← Grind.saveState
                    try
                      let (eqMVar, eqGoal) ← simplifyAddrEq cand.addr
                      if !(← eqGoal.mvarId.isAssigned) then
                        eqGoal.mvarId.withContext do
                          let eqT ← instantiateMVars (← eqGoal.mvarId.getType)
                          if eqT.isAppOfArity ``Eq 3 then
                            let lhs := eqT.appFn!.appArg!
                            let rhs := eqT.appArg!
                            if ← withReducible (isDefEq lhs rhs) then
                              eqGoal.mvarId.assign (← mkEqRefl lhs)
                      if ← eqGoal.mvarId.isAssigned then
                        let hEq ← instantiateMVars eqMVar
                        if ← tryAssignAndCancel cand hEq then
                          solvedSep := true
                        else
                          saved.restore
                      else
                        saved.restore
                    catch _ =>
                      saved.restore
              -- Pass 3: full grind on simplified address equality
              unless solvedSep do
                for cand in candidates do
                  unless solvedSep do
                    let saved ← Grind.saveState
                    try
                      let (eqMVar, eqGoal) ← simplifyAddrEq cand.addr
                      unless ← eqGoal.mvarId.isAssigned do
                        let cleanMVarId ← eqGoal.mvarId.withContext do
                          let mut toClear : Array FVarId := #[]
                          for localDecl? in (← getLCtx).decls do
                            if let some localDecl := localDecl? then
                              if localDecl.hasValue ||
                                 localDecl.type.getAppFn.isConstOf ``Std.ExtHashMap.sep ||
                                 localDecl.type.isAppOf ``Std.ExtHashMap then
                                toClear := toClear.push localDecl.fvarId
                          eqGoal.mvarId.tryClearMany toClear
                        let g ← Grind.liftGrindM (Grind.mkGoal cleanMVarId)
                        let g ← Grind.liftGrindM g.internalizeAll
                        match ← Grind.liftGrindM g.grind with
                        | .closed => pure ()
                        | .failed _ => failure
                      let hEq ← instantiateMVars eqMVar
                      if ← tryAssignAndCancel cand hEq then
                        solvedSep := true
                      else
                        saved.restore
                    catch _ =>
                      saved.restore
              pure solvedSep
            else
              let (r, g') ← solveIfNotAlready g
              subGoals := subGoals.map fun sg => if sg.mvarId == g.mvarId then g' else sg
              pure r
          if not solved then
            return (goal, subGoals)

        -- Then, we repeatedly visit subgoals until all are solved or we make no progress.
        while !(← subGoals.allM (·.mvarId.isAssigned)) do
          let mut progress := false
          let mut newSubGoals := []
          for subGoal in subGoals do
            let (r, subGoal') ← solveIfNotAlready subGoal
            progress := progress || r
            newSubGoals := newSubGoals ++ [subGoal']
          subGoals := newSubGoals
          unless progress do break

        -- Unsolved goals left? Return control to the user
        let unsolvedGoals ← subGoals.filterMapM fun (g: Grind.Goal) => do
          if ← g.mvarId.isAssigned then
            return none
          else
            return some g
        unsolvedGoals.forM fun mvarId => do
          let t ← mvarId.mvarId.getType
          trace[Kraken.kstep] "Unsolved goal: {t}"
        if unsolvedGoals.length > 0 then
          return (goal, unsolvedGoals)

        pure (true, goal)
      | #[] =>
        pure (false, goal)
      | _ =>
        throwError "TODO"

    let (keepGoingIte, goal) ←
      if !keepGoingSimp && !keepGoingSpec && effectsAll.appArg!.isAppOfArity ``ite 5 then
        let iteExpr := effectsAll.appArg!
        let α := iteExpr.getArg! 0
        let c := iteExpr.getArg! 1
        let inst := iteExpr.getArg! 2
        let t := iteExpr.getArg! 3
        let f := iteExpr.getArg! 4
        let tryProveIteCond (prop : Expr) : Grind.GrindTacticM (Option Expr) :=
          goal.mvarId.withContext do
            let saved ← Grind.saveState
            try
              let mvar ← mkFreshExprSyntheticOpaqueMVar prop
              let prop' ← expandLets prop
              let prop' ← Grind.liftSymM (Sym.preprocessExpr prop')
              let prop' ← Grind.liftGrindM <|
                Sym.dsimp (config := { maxSteps := 100000 })
                  (methods := { pre := evalGround >> kdsimpDecls >> kdsimpMatch >> kdsimpProj >> kbeta })
                  prop'
              let mvarId ← mvar.mvarId!.replaceTargetDefEq prop'
              let mvarId ← do
                let r ← Grind.liftGrindM (Sym.simpGoal mvarId simpMethods)
                match r with
                | .noProgress => pure mvarId
                | .goal mvarId => pure mvarId
                | .closed => pure mvarId
              unless ← mvarId.isAssigned do
                try
                  mvarId.refl
                catch _ => pure ()
              unless ← mvarId.isAssigned do
                let cleanMVarId ← mvarId.withContext do
                  let mut toClear : Array FVarId := #[]
                  for localDecl? in (← getLCtx).decls do
                    if let some localDecl := localDecl? then
                      if localDecl.hasValue ||
                         localDecl.type.getAppFn.isConstOf ``Std.ExtHashMap.sep ||
                         localDecl.type.isAppOf ``Std.ExtHashMap then
                        toClear := toClear.push localDecl.fvarId
                  mvarId.tryClearMany toClear
                let g ← Grind.liftGrindM (Grind.mkGoal cleanMVarId)
                let g ← Grind.liftGrindM g.internalizeAll
                match ← Grind.liftGrindM g.grind with
                | .closed => pure ()
                | .failed _ => failure
              let prf ← instantiateMVars mvar
              return some prf
            catch _ =>
              saved.restore
              return none
        if let some hc ← tryProveIteCond c then
          let eqPrf ← goal.mvarId.withContext <|
            mkAppOptM ``if_pos #[some c, some inst, some hc, some α, some t, some f]
          let (goal, _) ← rwTarget goal false eqPrf
          pure (true, goal)
        else if let some hnc ← tryProveIteCond (mkNot c) then
          let eqPrf ← goal.mvarId.withContext <|
            mkAppOptM ``if_neg #[some c, some inst, some hnc, some α, some t, some f]
          let (goal, _) ← rwTarget goal false eqPrf
          pure (true, goal)
        else
          pure (false, goal)
      else
        pure (false, goal)

    trace[Kraken.kstep] "kstep: keepGoing = {keepGoingSimp}"

    if keepGoingSimp || keepGoingSpec || keepGoingIte then
      go goal
    else
      pure (goal, [])

  let (goal, subGoals) ← go goal

  -- Remove the gimmick debug marker.
  let goal ← removeGimmick goal

  trace[Kraken.kstep] "END KSTEP: {subGoals.length} sub-goals left"

  if let .some r := maxInstrCount then
    let remaining ← r.get
    if remaining > 0 then
      throwError m!"kstep could not step through the remaining {remaining} steps"

  Grind.setGoals (subGoals ++ [ goal ])

syntax (name := symRotateRight) "rotate_right" (ppSpace num)? : grind

@[grind_tactic symRotateRight]
def evalSymRotateRight : Grind.GrindTactic := fun stx => do
  let n := if stx[1].isNone then 1 else stx[1][0].toNat
  let goals ← Grind.getGoals
  Grind.setGoals (goals.rotateRight n)

syntax (name := tacticKStep) "kstep" optConfig (ppSpace num)? : tactic

@[tactic tacticKStep]
def evalTacticKStep : Tactic := fun stx => withMainContext do
  let `(tactic| kstep $cfg:optConfig $[$n:num]?) := stx | throwUnsupportedSyntax
  let step ← `(grind| kstep $cfg:optConfig $[$n:num]?)
  let goal ← getMainGoal
  let params ← Grind.mkDefaultParams { clean := false }
  let (_, state) ← Grind.GrindTacticM.runAtGoal goal params (sym := true) do
    unless (← Grind.getUnsolvedGoals).isEmpty do
      Grind.evalGrindTactic step
  replaceMainGoal (state.goals.map (·.mvarId))
