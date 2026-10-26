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

@[ksimp, grind =]
theorem BitVec.ofNat_sub_of_le {w : Nat} (x y : Nat) (h : y ≤ x) :
    BitVec.ofNat w (x - y) = BitVec.ofNat w x - BitVec.ofNat w y := by
  have := congrArg (BitVec.ofNat w) (Nat.sub_add_cancel h)
  rw [BitVec.ofNat_add] at this
  grind

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
  List.drop_drop
  List.take_of_length_le
  List.take_replicate
  List.drop_replicate
  UInt64.toBitVec_add

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
  BitVec.ofNat_eq_ofNat
  BitVec.ofNat_add
  BitVec.ofNat_mul
  BitVec.ofNat_toNat
  BitVec.ofNat_uInt64ToNat
  BitVec.setWidth_eq
  BitVec.shiftLeft_zero
  BitVec.zero_shiftLeft
  BitVec.zero_or
  BitVec.or_zero
  BitVec.xor_self
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
  UInt64.toBitVec_add
  UInt64.toBitVec_ofNat
  UInt64.toBitVec_sub
  UInt64.toNat_toBitVec

end

public meta section

open Lean Meta Elab Tactic Kraken

private def isCalleeSavedEqType (t : Expr) : Bool :=
  match t.consumeMData.getAppFn'.constName? with
  | some n => (`Reg64s.CalleeSavedEq).isSuffixOf n
  | none => false

private def clearSepAndLets (mvarId : MVarId) (clearCS : Bool := true) : MetaM MVarId :=
  mvarId.withContext do
    let mut toClear : Array FVarId := #[]
    for localDecl? in (← getLCtx).decls do
      if let some localDecl := localDecl? then
        if localDecl.hasValue ||
           localDecl.type.getAppFn.isConstOf ``Std.ExtHashMap.sep ||
           localDecl.type.isAppOf ``Std.ExtHashMap ||
           (clearCS && isCalleeSavedEqType localDecl.type) then
          toClear := toClear.push localDecl.fvarId
    mvarId.tryClearMany toClear

/-- Discharge program address and label offset equalities for program(s) `ps`. -/
elab "kaddr" ps:ident+ : tactic => withMainContext do
  let solved ← withReducible do
    try (← getMainGoal).refl; pure true catch _ => pure false
  if solved then return
  evalTactic (← `(tactic| (try simp only [Kraken.Executable.addrOf_zero, Kraken.Executable.startAddr_apply, Kraken.Layout.start_shift])))
  if (← getUnsolvedGoals).isEmpty then return
  let goal ← getMainGoal
  let cleanGoal ← clearSepAndLets goal
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
               arg 1
               simp only [List.mapIdx_cons, List.mapIdx_nil,
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
               arg 1
               simp only [List.mapIdx_cons, List.mapIdx_nil,
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
               arg 1
               simp only [List.mapIdx_cons, List.mapIdx_nil,
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
                 (try rw [Kraken.Executable.startAddr_apply])
                 rw [Executable.directivesFromStart]
                 (try delta $p)
                 arg 1
                 simp only [List.mapIdx_cons, List.mapIdx_nil,
                            Nat.add_zero, Nat.zero_add, Nat.reduceAdd])))
          else
            evalTactic (← `(tactic|
              ((try unfold Kraken.Executable.Exec Kraken.Executable.ExecTraced)
               conv =>
                 arg 2
                 (try rw [Kraken.Executable.startAddr_apply])
                 (try rw [Kraken.Executable.program_apply])
                 (try rw [Executable.directivesFromStart])
                 (try delta $p)
                 arg 1
                 simp only [List.mapIdx_cons, List.mapIdx_nil,
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
               arg 1
               simp only [List.mapIdx_cons, List.mapIdx_nil,
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
               arg 1
               simp only [List.mapIdx_cons, List.mapIdx_nil,
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
               arg 1
               simp only [List.mapIdx_cons, List.mapIdx_nil,
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
                 (try rw [Kraken.Executable.startAddr_apply])
                 rw [Executable.directivesFromStart]
                 (try delta $p)
                 arg 1
                 simp only [List.mapIdx_cons, List.mapIdx_nil,
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
                 (try rw [Kraken.Executable.startAddr_apply])
                 (try rw [Kraken.Executable.program_apply])
                 (try rw [Executable.directivesFromStart])
                 (try delta $p)
                 arg 1
                 simp only [List.mapIdx_cons, List.mapIdx_nil,
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
  if e.hasLooseBVars then
    return ← k e fvars
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

def kdeltaBetaOnly (targets: List Name) : DSimproc := fun e => do
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
    -- Application, *sans* the let-bindings in the arguments.
    let e_rebuilt := mkAppN f args
    if f.isConstOf ``Kraken.Effects.All then
      if fvars.size > 0 then
        let e' ← shareCommon e_rebuilt
        let e'' ← mkLetFVars fvars e'
        return .step e''
      else
        return .rfl
    else
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
        let e' ← shareCommon e_rebuilt
        let e'' ← mkLetFVars fvars e'
        return .step e''
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

run_meta do
  let info ← getConstInfo ``Directives.interp
  let val := mkConst ``Directives.interp (info.levelParams.map mkLevelParam)
  addAndCompile (.defnDecl {
    name := `Directives.interpHold
    levelParams := info.levelParams
    type := info.type
    value := val
    hints := .regular 0
    safety := .safe
    all := [`Directives.interpHold]
  })

theorem gimmickId_Effects_All_interp_to_hold {D MD : Type} [ArchDirective D MD] [Labels]
    (post : TracedPost MD) (ds : List (Kraken.Sized D)) (s : MD) (pc : Int64)
    (ret : Int64 → MD → Kraken.Effects MD) :
    gimmickId (Kraken.Effects.All post (Directives.interp ds s pc ret)) =
    gimmickId (Kraken.Effects.All post (Directives.interpHold ds s pc ret)) := by rfl

theorem gimmickId_Effects_All_hold_to_interp {D MD : Type} [ArchDirective D MD] [Labels]
    (post : TracedPost MD) (ds : List (Kraken.Sized D)) (s : MD) (pc : Int64)
    (ret : Int64 → MD → Kraken.Effects MD) :
    gimmickId (Kraken.Effects.All post (Directives.interpHold ds s pc ret)) =
    gimmickId (Kraken.Effects.All post (Directives.interp ds s pc ret)) := by rfl

theorem gimmickId_Effects_All_interp_nil {D MD : Type} [ArchDirective D MD] [Labels]
    (post : TracedPost MD) (s : MD) (pc : Int64) (ret : Int64 → MD → Kraken.Effects MD) :
    gimmickId (Kraken.Effects.All post (Directives.interpHold ([] : List (Kraken.Sized D)) s pc ret)) =
    gimmickId (Kraken.Effects.All post (ret pc s)) := by rfl

theorem gimmickId_Effects_All_ite_true {MD : Type} (post : TracedPost MD)
    {c : Prop} [inst : Decidable c] (hc : c) (t f : Kraken.Effects MD) :
    gimmickId (Kraken.Effects.All post (@ite _ c inst t f)) =
    gimmickId (Kraken.Effects.All post t) := by
  simp [hc]

theorem gimmickId_Effects_All_ite_false {MD : Type} (post : TracedPost MD)
    {c : Prop} [inst : Decidable c] (hnc : ¬ c) (t f : Kraken.Effects MD) :
    gimmickId (Kraken.Effects.All post (@ite _ c inst t f)) =
    gimmickId (Kraken.Effects.All post f) := by
  simp [hnc]

theorem BitVec.add_add_eq_of_add_eq {w : Nat} (base a b c : BitVec w) (h : a + b = c) :
    (base + a) + b = base + c := by
  rw [BitVec.add_assoc, h]

theorem BitVec.add_eq_add_add_of_add_eq {w : Nat} (base a b c : BitVec w) (h : a + b = c) :
    base + c = (base + a) + b := by
  rw [BitVec.add_assoc, h]

theorem gimmickId_Effects_All_interp_cons {D MD : Type} [ArchDirective D MD] [Labels]
    (post : TracedPost MD) (d : D) (sz : Nat) (ds : List (Kraken.Sized D)) (s : MD) (pc : Int64)
    (ret : Int64 → MD → Kraken.Effects MD) :
    gimmickId (Kraken.Effects.All post (Directives.interpHold ({directive := d, size := sz} :: ds) s pc ret)) =
    gimmickId (Kraken.Effects.All post (ArchDirective.interp d s (.mk pc (pc + .ofNat sz))
      (fun s => Directives.interpHold ds s (pc + .ofNat sz) ret) ret)) := by rfl

theorem gimmickId_Effects_All_interp_cons' {D MD : Type} [ArchDirective D MD] [Labels]
    (post : TracedPost MD) (d : Kraken.Sized D) (ds : List (Kraken.Sized D)) (s : MD) (pc : Int64)
    (ret : Int64 → MD → Kraken.Effects MD) :
    gimmickId (Kraken.Effects.All post (Directives.interpHold (d :: ds) s pc ret)) =
    gimmickId (Kraken.Effects.All post (ArchDirective.interp d.directive s (.mk pc (pc + .ofNat d.size))
      (fun s => Directives.interpHold ds s (pc + .ofNat d.size) ret) ret)) := by rfl

theorem gimmickId_Effects_All_done {MD : Type}
    (post : TracedPost MD) (a : Kraken.MachineState MD) :
    gimmickId (Kraken.Effects.All post (.done a)) =
    gimmickId (post a []) := rfl

theorem gimmickId_Effects_All_undefined {MD α : Type} [NondetSupportingType α]
    (post : TracedPost MD) (cont : α → Kraken.Effects MD) :
    gimmickId (Kraken.Effects.All post (@Kraken.Effects.undefined MD α _ cont)) =
    gimmickId (∀ v : α, (cont v).All post) := rfl

theorem gimmickId_Effects_All_require_read_access {MD : Type}
    (post : TracedPost MD) (addr : BitVec 64) (w : Width) (cont : Unit → Kraken.Effects MD) :
    gimmickId (Kraken.Effects.All post (.require_read_access addr w cont)) =
    gimmickId ((cont ()).All (fun a tr => post a (.read addr w :: tr))) := rfl

theorem gimmickId_Effects_All_require_write_access {MD : Type}
    (post : TracedPost MD) (addr : BitVec 64) (w : Width) (cont : Unit → Kraken.Effects MD) :
    gimmickId (Kraken.Effects.All post (.require_write_access addr w cont)) =
    gimmickId ((cont ()).All (fun a tr => post a (.write addr w :: tr))) := rfl

theorem gimmickId_Effects_All_require_exec_access {MD : Type}
    (post : TracedPost MD) (p : Std.Rco Int64) (cont : Unit → Kraken.Effects MD) :
    gimmickId (Kraken.Effects.All post (.require_exec_access p cont)) =
    gimmickId ((cont ()).All (fun a tr => post a (.exec p :: tr))) := rfl

theorem gimmickId_Effects_All_require_const_time {MD : Type}
    (post : TracedPost MD) (vals : List (BitVec 64)) (cont : Unit → Kraken.Effects MD) :
    gimmickId (Kraken.Effects.All post (.require_const_time vals cont)) =
    gimmickId ((cont ()).All (fun a tr => post a (.var_time vals :: tr))) := rfl

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
    let α := e.getArg! 0
    let c := e.getArg! 1
    if !c.hasFVar && !c.hasLooseBVars then
      let inst ← withDefault (whnf (e.getArg! 2))
      if inst.isAppOfArity ``Decidable.isTrue 2 then
        return .step (← share (e.getArg! 3))
      if inst.isAppOfArity ``Decidable.isFalse 2 then
        return .step (← share (e.getArg! 4))
    if α.isAppOf ``Kraken.Effects then
      let c' ← match (← Sym.DSimp.dsimp c) with
        | .rfl _ => pure c
        | .step c' _ => pure c'
      return ← peelLets c' #[] fun c'' fvars => do
        if fvars.isEmpty && isSameExpr c c'' then
          return .rfl (done := true)
        else
          let args := e.getAppArgs.set! 1 c''
          let e' ← shareCommon (mkAppN e.getAppFn args)
          let e'' ← mkLetFVars fvars e'
          return .step e'' (done := true)
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

def rwTarget (goal: Grind.Goal) (symm : Bool) (term : Expr) : Grind.GrindTacticM (Grind.Goal × List Grind.Goal) := do
  goal.withContext do
    let target ← instantiateMVars (← goal.mvarId.getType)
    let rootRewrite? : Option (Expr × Expr × List MVarId) ←
      if target.isAppOfArity ``gimmickId 1 && target.appArg!.isAppOfArity ``Kraken.Effects.All 3 then
        let gimmickFn := target.appFn!
        let inner := target.appArg!
        let saved ← saveState
        try
          Term.withSynthesize do
            let heqType ← Sym.unfoldReducible (← instantiateMVars (← inferType term))
            let (xs, bis, eqType) ← forallMetaTelescopeReducing heqType
            let some (_, lhs, rhs) := eqType.eq? | failure
            let (lhs, rhs) := if symm then (rhs, lhs) else (lhs, rhs)
            let mut proof := mkAppN term xs
            if symm then
              proof ← mkEqSymm proof
            let eNewInner ←
              if lhs.isAppOfArity ``Kraken.Effects.All 3 && (← isDefEq lhs inner) then
                pure rhs
              else if ← isDefEq lhs inner.appArg! then
                proof ← mkCongrArg inner.appFn! proof
                pure (mkApp inner.appFn! rhs)
              else
                failure
            for x in xs, bi in bis do
              if bi.isInstImplicit && !(← x.mvarId!.isAssigned) then
                x.mvarId!.assign (← synthInstance (← inferType x))
            let eqProof ← mkCongrArg gimmickFn (← instantiateMVars proof)
            let eNew := mkApp gimmickFn (← instantiateMVars eNewInner)
            let mvarIds := (xs.map (·.mvarId!)).toList
            pure (some (eNew, eqProof, mvarIds))
        catch _ =>
          restoreState saved
          pure none
      else
        pure none
    let (eNewRaw, eqProof, mvarIds) ← match rootRewrite? with
      | some res => pure res
      | none =>
        let mvarCounterSaved := (← getMCtx).mvarCounter
        let r ← Term.withSynthesize do
          let heq := term
          let heqType ← instantiateMVars (← inferType heq)
          let heqType' ← Sym.unfoldReducible heqType
          let heq ← if isSameExpr heqType heqType' then pure heq else mkExpectedTypeHint heq heqType'
          goal.mvarId.rewrite target heq symm
        let mctx ← getMCtx
        let mvarIds := r.mvarIds.filter fun mvarId => (mctx.getDecl mvarId |>.index) >= mvarCounterSaved
        pure (r.eNew, r.eqProof, mvarIds)
    let eNew ← Grind.liftSymM <| Sym.preprocessExpr eNewRaw
    let mvarId ← goal.mvarId.replaceTargetEq eNew eqProof
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
  let kdsimpDecls := kdeltaBetaOnly declsForDSimp
  let skipPostAndDepForallD : DSimproc := fun e => do
    if (e.isForall && !e.isArrow) || e.isAppOf ``Exists || e.isAppOf ``Or ||
       e.isAppOf ``TracedEventually || e.isAppOf ``TracedGoal ||
       e.isAppOf ``Kraken.Executable.mk then
      return .rfl (done := true)
    if e.isAppOfArity ``Eventually 4 then
      let args := e.getAppArgs
      let post := args[2]!
      let st := args[3]!
      let post' ← match (← Sym.DSimp.dsimp post) with
        | .rfl _ => pure post
        | .step post' _ => pure post'
      let st' ← match (← Sym.DSimp.dsimp st) with
        | .rfl _ => pure st
        | .step st' _ => pure st'
      return ← peelLets st' #[] fun st'' fvars => do
        if fvars.isEmpty && isSameExpr post post' && isSameExpr st st'' then
          return .rfl (done := true)
        else
          let args' := (args.set! 2 post').set! 3 st''
          let e' ← shareCommon (mkAppN e.getAppFn args')
          let e'' ← mkLetFVars fvars e'
          return .step e'' (done := true)
    if e.isAppOfArity ``gimmickId 1 then
      let inner := e.appArg!
      match (← Sym.DSimp.dsimp inner) with
      | .rfl _ => return .rfl (done := true)
      | .step inner' _ =>
        let e' ← shareCommon (mkApp e.appFn! inner')
        return .step e' (done := true)
    if e.isAppOfArity ``Kraken.Effects.All 3 then
      let eff := e.appArg!
      let eff' ← match (← Sym.DSimp.dsimp eff) with
        | .rfl _ => pure eff
        | .step eff' _ => pure eff'
      return ← peelLets eff' #[] fun eff'' fvars => do
        if fvars.isEmpty && isSameExpr eff eff'' then
          return .rfl (done := true)
        else
          let e' ← shareCommon (mkApp e.appFn! eff'')
          let e'' ← mkLetFVars fvars e'
          return .step e'' (done := true)
    if e.isAppOf ``Kraken.Effects.require_exec_access ||
       e.isAppOf ``Kraken.Effects.require_const_time ||
       e.isAppOf ``Kraken.Effects.require_read_access ||
       e.isAppOf ``Kraken.Effects.require_write_access ||
       e.isAppOf ``Kraken.Effects.undefined then
      return .rfl (done := true)
    if e.isAppOf ``Directives.interp || e.isAppOf `Directives.interpHold then
      if e.getAppNumArgs == 8 then
        let args := e.getAppArgs
        let ds := args[4]!
        let s := args[5]!
        let pc := args[6]!
        let ds' ←
          if ds.isAppOfArity ``List.cons 3 || ds.isAppOfArity ``List.nil 1 then
            pure ds
          else
            match (← Sym.DSimp.dsimp ds) with
            | .rfl _ => pure ds
            | .step ds' _ => pure ds'
        let s' ← match (← Sym.DSimp.dsimp s) with
          | .rfl _ => pure s
          | .step s' _ => pure s'
        let pc' ← match (← Sym.DSimp.dsimp pc) with
          | .rfl _ => pure pc
          | .step pc' _ => pure pc'
        return ← peelLets s' #[] fun s'' fvars1 =>
          peelLets pc' fvars1 fun pc'' fvars2 => do
            if fvars2.isEmpty && isSameExpr ds ds' && isSameExpr s s'' && isSameExpr pc pc'' then
              return .rfl (done := true)
            else
              let args' := ((args.set! 4 ds').set! 5 s'').set! 6 pc''
              let e' ← shareCommon (mkAppN e.getAppFn args')
              let e'' ← mkLetFVars fvars2 e'
              return .step e'' (done := true)
      else
        return .rfl (done := true)
    return .rfl
  let isBitwiseOp (e : Expr) : Bool :=
    e.isAppOf ``HXor.hXor || e.isAppOf ``XorOp.xor || e.isAppOf ``BitVec.xor || e.isAppOf ``Nat.xor ||
    e.isAppOf ``HAnd.hAnd || e.isAppOf ``AndOp.and || e.isAppOf ``BitVec.and || e.isAppOf ``Nat.land ||
    e.isAppOf ``HOr.hOr || e.isAppOf ``OrOp.or || e.isAppOf ``BitVec.or || e.isAppOf ``Nat.lor
  let kEvalGroundNoBitwise : DSimproc := fun e => do
    if isBitwiseOp e then return .rfl
    (evalGround : DSimproc) e
  let dsimpCore := skipPostAndDepForallD >> kEvalGroundNoBitwise >> kdsimpDecls >> kdsimpMatch >> kdsimpProj >> kbeta
  let dsimpPre := if ← isTracingEnabledFor `Kraken.kstep then klog >> dsimpCore else dsimpCore

  -- https://lean-lang.org/doc/api/Lean/Meta/Sym/Simp/SimpM.html
  -- note the "contextual ite handling" --> are we doing this?
  let simpTheorems ← ksimpExt.getTheorems
  let skipPostAndDepForall : Sym.Simp.Simproc := fun e => do
    if (e.isForall && !e.isArrow) || e.isAppOf ``Exists || e.isAppOf ``Or ||
       e.isAppOf ``TracedEventually || e.isAppOf ``Std.ExtHashMap.sep ||
       e.isAppOf ``Kraken.Executable.mk then
      return .rfl (done := true)
    if e.isAppOfArity ``Directives.interp 8 || e.isAppOfArity `Directives.interpHold 8 then
      match ← Sym.Simp.simpAppArgRange e 5 7 with
      | .step e' h _ cd => return .step e' h (done := true) (contextDependent := cd)
      | .rfl _ cd => return .rfl (done := true) (contextDependent := cd)
    if e.isAppOfArity ``Eventually 4 || e.isAppOfArity ``TracedGoal 4 then
      match ← Sym.Simp.simpAppArgRange e 3 4 with
      | .step e' h _ cd => return .step e' h (done := true) (contextDependent := cd)
      | .rfl _ cd => return .rfl (done := true) (contextDependent := cd)
    if e.isAppOfArity ``Kraken.Effects.All 3 then
      match ← Sym.Simp.simpAppArgRange e 2 3 with
      | .step e' h _ cd => return .step e' h (done := true) (contextDependent := cd)
      | .rfl _ cd => return .rfl (done := true) (contextDependent := cd)
    if e.isAppOfArity ``ite 5 && (e.getArg! 0).isAppOf ``Kraken.Effects then
      return ← Sym.Simp.simpControl e
    return .rfl
  let simpMethods: Sym.Simp.Methods := {
    pre := skipPostAndDepForall
    post := Sym.Simp.evalGround >> simpTheorems.rewrite
  }

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
    if config.debug then
      logInfo m!"[hb={← IO.getNumHeartbeats}] start of go"
    let goal ← goal.withContext (preprocessGoalIfNeeded goal)
    if config.debug then
      logInfo m!"[hb={← IO.getNumHeartbeats}] after preprocessGoalIfNeeded"
    -- STEP 1: dsimp and step through Directives.interp via equational theorems
    let rec stepDirectivesLoop (goal : Grind.Goal) : Grind.GrindTacticM Grind.Goal := do
      let goal ← goal.withContext do
        let target ← instantiateMVars (← goal.mvarId.getType)
        let_expr gimmickId inner := target | return goal
        let inner := inner.consumeMData
        if inner.isForall && !inner.isArrow then
          introsIf goal
        else
          return goal
      let goal ← goal.withContext do
        let target ← goal.mvarId.getType
        let target' ← Grind.liftGrindM <|
          Sym.dsimp
            (config := { maxSteps := 1000000 })
            (methods := { pre := dsimpPre })
            target
        let mvarId ←
          if isSameExpr target target' then
            pure goal.mvarId
          else
            goal.mvarId.replaceTargetDefEq target'
        let mvarId ←
          if (target'.find? isBitwiseOp).isSome then
            let target'' ← Grind.liftGrindM <|
              Sym.dsimp
                (config := { maxSteps := 1000000 })
                (methods := { pre := skipPostAndDepForallD >> evalGround })
                target'
            if isSameExpr target' target'' then
              pure mvarId
            else
              mvarId.replaceTargetDefEq target''
          else
            pure mvarId
        if config.debug then
          logInfo m!"[hb={← IO.getNumHeartbeats}] after Sym.dsimp"
        introsIf ({ goal with mvarId })
      let stepEq? ← goal.withContext do
        let target ← instantiateMVars (← goal.mvarId.getType)
        unless target.isAppOfArity ``gimmickId 1 do return none
        let inner := target.appArg!
        unless inner.isAppOfArity ``Kraken.Effects.All 3 do return none
        let MD := inner.getArg! 0
        let post := inner.getArg! 1
        let eff := inner.getArg! 2
        if eff.isAppOfArity ``Kraken.Effects.require_exec_access 3 then
          let p := eff.getArg! 1
          let cont := eff.getArg! 2
          let eqPrf := mkAppN (mkConst ``gimmickId_Effects_All_require_exec_access) #[MD, post, p, cont]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
          return some (false, true, rhs, eqPrf)
        else if eff.isAppOfArity ``Kraken.Effects.require_const_time 3 then
          let vals := eff.getArg! 1
          let cont := eff.getArg! 2
          let eqPrf := mkAppN (mkConst ``gimmickId_Effects_All_require_const_time) #[MD, post, vals, cont]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
          return some (false, true, rhs, eqPrf)
        else if eff.isAppOfArity ``Kraken.Effects.require_read_access 4 then
          let addr := eff.getArg! 1
          let w := eff.getArg! 2
          let cont := eff.getArg! 3
          let eqPrf := mkAppN (mkConst ``gimmickId_Effects_All_require_read_access) #[MD, post, addr, w, cont]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
          return some (false, true, rhs, eqPrf)
        else if eff.isAppOfArity ``Kraken.Effects.require_write_access 4 then
          let addr := eff.getArg! 1
          let w := eff.getArg! 2
          let cont := eff.getArg! 3
          let eqPrf := mkAppN (mkConst ``gimmickId_Effects_All_require_write_access) #[MD, post, addr, w, cont]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
          return some (false, true, rhs, eqPrf)
        else if eff.isAppOfArity ``Kraken.Effects.done 2 then
          let a := eff.getArg! 1
          let eqPrf := mkAppN (mkConst ``gimmickId_Effects_All_done) #[MD, post, a]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
          return some (false, true, rhs, eqPrf)
        else if eff.isAppOfArity ``Kraken.Effects.undefined 4 then
          let α := eff.getArg! 1
          let inst := eff.getArg! 2
          let cont := eff.getArg! 3
          let eqPrf := mkAppN (mkConst ``gimmickId_Effects_All_undefined) #[MD, α, inst, post, cont]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
          return some (false, true, rhs, eqPrf)
        else if eff.isAppOfArity ``Directives.interp 8 then
          if (← maxInstrCount.mapM (·.get)) = .some 0 then
            return none
          let iArgs := eff.getAppArgs
          let eqPrf := mkAppN (mkConst ``gimmickId_Effects_All_interp_to_hold)
            #[iArgs[0]!, iArgs[1]!, iArgs[2]!, iArgs[3]!, post, iArgs[4]!, iArgs[5]!, iArgs[6]!, iArgs[7]!]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
          return some (false, true, rhs, eqPrf)
        else if eff.isAppOfArity `Directives.interpHold 8 then
          let iArgs := eff.getAppArgs
          let D := iArgs[0]!
          let MD := iArgs[1]!
          let inst := iArgs[2]!
          let labels := iArgs[3]!
          let ds := iArgs[4]!
          let s := iArgs[5]!
          let pc := iArgs[6]!
          let ret := iArgs[7]!
          if ds.isAppOfArity ``List.nil 1 then
            let eqPrf := mkAppN (mkConst ``gimmickId_Effects_All_interp_nil)
              #[D, MD, inst, labels, post, s, pc, ret]
            let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
            return some (false, true, rhs, eqPrf)
          else if (← maxInstrCount.mapM (·.get)) = .some 0 then
            let eqPrf := mkAppN (mkConst ``gimmickId_Effects_All_hold_to_interp)
              #[D, MD, inst, labels, post, ds, s, pc, ret]
            let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
            return some (false, false, rhs, eqPrf)
          else if ds.isAppOfArity ``List.cons 3 then
            let d := ds.getArg! 1
            let dsTail := ds.getArg! 2
            let eqPrf :=
              if d.isAppOfArity ``Kraken.Sized.mk 3 then
                mkAppN (mkConst ``gimmickId_Effects_All_interp_cons)
                  #[D, MD, inst, labels, post, d.getArg! 1, d.getArg! 2, dsTail, s, pc, ret]
              else
                mkAppN (mkConst ``gimmickId_Effects_All_interp_cons')
                  #[D, MD, inst, labels, post, d, dsTail, s, pc, ret]
            let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
            return some (true, true, rhs, eqPrf)
          else
            return none
        else
          return none
      match stepEq? with
      | some (decCount, keepLooping, rhs, eqPrf) =>
        if decCount then
          maxInstrCount.forM (fun r => r.modify (· - 1))
        let mvarId ← goal.withContext (goal.mvarId.replaceTargetEq rhs eqPrf)
        let goal := { goal with mvarId }
        if keepLooping then
          stepDirectivesLoop goal
        else
          return goal
      | none =>
        return goal

    let goal ← stepDirectivesLoop goal
    goal.withContext do
    if config.debug then
      logInfo m!"[hb={← IO.getNumHeartbeats}] after stepDirectivesLoop"

    -- STEP 2: simp
    let (keepGoingSimp, goal) ← Grind.liftGrindM $ do
      let simpResult ← Sym.simpGoal goal.mvarId simpMethods
      match simpResult with
      | .noProgress => pure (false, goal)
      | .goal mvarId => pure (true, { goal with mvarId })
      | .closed => throwError "unexpected"
    if config.debug then
      logInfo m!"[hb={← IO.getNumHeartbeats}] after Sym.simpGoal (keepGoingSimp={keepGoingSimp})"

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
        if config.debug then
          logInfo m!"[hb={← IO.getNumHeartbeats}] before rwTarget {thmName}"
        trace[Kraken.kstep] "Found a spec lemma: {thmName}"
        let (goal, subGoals) ← rwTarget goal false (mkConst thmName)
        if config.debug then
          logInfo m!"[hb={← IO.getNumHeartbeats}] after rwTarget {thmName} ({subGoals.length} subgoals)"
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

          let t ← instantiateMVars (← subGoal.mvarId.getType)
          if !t.hasExprMVar then
            -- Solvable with refl, maybe.
            try
              withReducible subGoal.mvarId.refl
              trace[Kraken.kstep] "Solved by refl: {t}"
              return (true, subGoal)
            catch _ => pure ()

            -- Try solving with grind, roll back state otherwise (we don't want to
            -- return the failed Grind state).
            let saved ← Grind.saveState
            try
              let cleanMVarId ← clearSepAndLets subGoal.mvarId (!isCalleeSavedEqType t)
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
          let lenGoal? ← subGoals.findM? fun (sg : Grind.Goal) => do
            if sg.mvarId == g.mvarId then return false
            let t ← instantiateMVars (← sg.mvarId.getType)
            unless t.isAppOfArity ``Eq 3 do return false
            let lhs := t.appFn!.appArg!
            return lhs.isAppOfArity ``List.length 2 && lhs.appArg!.isMVar
          let solved ←
            if let some addrGoal := addrGoal? then
              let addrGoalType ← instantiateMVars (← addrGoal.mvarId.getType)
              let addr := addrGoalType.appFn!.appArg!
              let addrMVar := addrGoalType.appArg!
              if config.debug then
                logInfo m!"[hb={← IO.getNumHeartbeats}] before findSepAtCandidates"
              let candidates ← Kraken.Tactic.findSepAtCandidates g.mvarId
              if config.debug then
                logInfo m!"[hb={← IO.getNumHeartbeats}] after findSepAtCandidates ({candidates.size} candidates)"
              let solveLenFast (lenGoal : Grind.Goal) : Grind.GrindTacticM Bool := do
                let lenGoal ← lenGoal.mvarId.withContext (preprocessGoalIfNeeded lenGoal)
                let simpResult ← Grind.liftGrindM (Sym.simpGoal lenGoal.mvarId simpMethods)
                let lenGoal ← match simpResult with
                  | .noProgress => pure lenGoal
                  | .goal mvarId => pure { lenGoal with mvarId }
                  | .closed => pure lenGoal
                if ← lenGoal.mvarId.isAssigned then return true
                if ← withReducible lenGoal.mvarId.assumptionCore then return true
                try
                  withReducible lenGoal.mvarId.refl
                  return true
                catch _ =>
                  return false
              let tryAssignAndCancel (cand : Kraken.Tactic.SepAtCandidate) (hEq : Expr) : Grind.GrindTacticM Bool := do
                withConfig (fun c => { c with assignSyntheticOpaque := true }) do
                  if config.debug then
                    logInfo m!"[hb={← IO.getNumHeartbeats}] tryAssignAndCancel cand.addr={cand.addr} cand.bs={cand.bs}"
                  -- Attempt 1: direct unsplit candidate `cand.bs` (fast length check first, then grind fallback)
                  let saved1 ← Grind.saveState
                  let ok1 ← try
                    unless ← isDefEq addrMVar cand.addr do failure
                    addrGoal.mvarId.assign hEq
                    unless ← Kraken.Tactic.solveSepAtCandidate g.mvarId cand none do failure
                    if let some lenGoal := lenGoal? then
                      unless ← solveLenFast lenGoal do
                        let (_, lenGoal') ← solveIfNotAlready lenGoal
                        unless ← lenGoal'.mvarId.isAssigned do failure
                    pure true
                  catch _ =>
                    saved1.restore
                    pure false
                  if config.debug then
                    logInfo m!"[hb={← IO.getNumHeartbeats}] after Attempt 1 (ok1={ok1})"
                  if ok1 then return true
                  -- Attempt 2: prefix split via `Mem.At_take_drop_sep` when `lenGoal?` is present
                  let some lenGoal := lenGoal? | return false
                  let saved2 ← Grind.saveState
                  let ok2 ← try
                    let lenType ← instantiateMVars (← lenGoal.mvarId.getType)
                    let wBytes := lenType.appArg!
                    let nExpr ← match ← (evalNat (← whnf wBytes)).run with
                      | some n => pure (mkNatLit n)
                      | none => pure wBytes
                    let (hSplit, hTakeLen) ← g.mvarId.withContext do
                      let splitFn ← mkAppM ``Mem.At_take_drop_sep #[cand.bs, nExpr, cand.addr]
                      let splitFnType ← inferType splitFn
                      let kType := splitFnType.bindingDomain!
                      let lenBoundType := splitFnType.bindingBody!.bindingDomain!
                      if config.debug then
                        logInfo m!"[hb={← IO.getNumHeartbeats}] Attempt 2 before provePropGoal"
                      let some hBoth ← Kraken.Tactic.provePropGoal (mkAnd kType lenBoundType) | failure
                      if config.debug then
                        logInfo m!"[hb={← IO.getNumHeartbeats}] Attempt 2 after provePropGoal"
                      let hK ← mkAppM ``And.left #[hBoth]
                      let hLen ← mkAppM ``And.right #[hBoth]
                      let hSplit := mkApp2 splitFn hK hLen
                      let hTakeLen ← mkAppM ``List.length_take_of_le #[hK]
                      pure (hSplit, hTakeLen)
                    unless ← isDefEq addrMVar cand.addr do failure
                    addrGoal.mvarId.assign hEq
                    unless ← Kraken.Tactic.solveSepAtCandidate g.mvarId cand (some hSplit) do failure
                    lenGoal.mvarId.withContext do
                      let expectedLenType ← instantiateMVars (← lenGoal.mvarId.getType)
                      let hTakeLen ← mkExpectedTypeHint hTakeLen expectedLenType
                      lenGoal.mvarId.assign hTakeLen
                    pure true
                  catch _ =>
                    saved2.restore
                    pure false
                  if config.debug then
                    logInfo m!"[hb={← IO.getNumHeartbeats}] after Attempt 2 (ok2={ok2})"
                  return ok2
              let rec peelBitVecAddOffset (e : Expr) : MetaM (Expr × Nat) := do
                let e := e.consumeMData
                if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``BitVec.add 3 then
                  let args := e.getAppArgs
                  let a := args[args.size - 2]!
                  let b := args[args.size - 1]!.consumeMData
                  if let some ⟨64, bv⟩ ← getBitVecValue? b then
                    let n := bv.toNat
                    if 0 < n && n ≤ 4096 then
                      let (base, off) ← peelBitVecAddOffset a
                      return (base, off + n)
                return (e, 0)
              let tryAssignSliceAndCancel (cand : Kraken.Tactic.SepAtCandidate) (off : Nat) (hEq : Expr) : Grind.GrindTacticM Bool := do
                withConfig (fun c => { c with assignSyntheticOpaque := true }) do
                  let some lenGoal := lenGoal? | return false
                  let saved ← Grind.saveState
                  try
                    let lenType ← instantiateMVars (← lenGoal.mvarId.getType)
                    let wBytes := lenType.appArg!
                    let nExpr ← match ← (evalNat (← whnf wBytes)).run with
                      | some n => pure (mkNatLit n)
                      | none => pure wBytes
                    let offExpr := mkNatLit off
                    let (hSplit, hTakeLen, targetAddr) ← g.mvarId.withContext do
                      let splitFn ← mkAppM ``Mem.At_slice_extract_sep #[cand.bs, offExpr, nExpr, cand.addr]
                      let splitFnType ← inferType splitFn
                      let sliceType := splitFnType.bindingDomain!
                      let lenBoundType := splitFnType.bindingBody!.bindingDomain!
                      let some hBoth ← Kraken.Tactic.provePropGoal (mkAnd sliceType lenBoundType) | failure
                      let hSlice ← mkAppM ``And.left #[hBoth]
                      let hLen ← mkAppM ``And.right #[hBoth]
                      let hSplit := mkApp2 splitFn hSlice hLen
                      let hTakeLen ← mkAppM ``Mem.length_drop_take_of_le #[cand.bs, offExpr, nExpr, hSlice]
                      let splitEqType ← instantiateMVars (← inferType hSplit)
                      let rhsArgs := splitEqType.appArg!.getAppArgs
                      let extractedClause := rhsArgs[rhsArgs.size - 2]!
                      let some (_, splitAddr) ← Kraken.Tactic.extractAtBytesAndAddr? extractedClause | failure
                      pure (hSplit, hTakeLen, splitAddr)
                    unless ← isDefEq addrMVar targetAddr do failure
                    addrGoal.mvarId.assign hEq
                    unless ← Kraken.Tactic.solveSepAtCandidate g.mvarId cand (some hSplit) do failure
                    lenGoal.mvarId.withContext do
                      let expectedLenType ← instantiateMVars (← lenGoal.mvarId.getType)
                      let hTakeLen ← mkExpectedTypeHint hTakeLen expectedLenType
                      lenGoal.mvarId.assign hTakeLen
                    pure true
                  catch _ =>
                    saved.restore
                    pure false
              let simplifyAddrEq (candAddr : Expr) : Grind.GrindTacticM (Expr × Grind.Goal) :=
                addrGoal.mvarId.withContext do
                  let eqType ← mkEq addr candAddr
                  let eqMVar ← mkFreshExprSyntheticOpaqueMVar eqType
                  let eqType' ← expandLets eqType
                  let eqType' ← Grind.liftSymM (Sym.preprocessExpr eqType')
                  let eqType' ← Grind.liftGrindM <|
                    Sym.dsimp (config := { maxSteps := 100000 })
                      (methods := { pre := dsimpCore })
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
              let trySliceAtOffset (cand : Kraken.Tactic.SepAtCandidate) (off : Nat) : Grind.GrindTacticM Bool := do
                let savedSlice ← Grind.saveState
                try
                  let sliceAddr ← addrGoal.mvarId.withContext do
                    let wOff ← mkAppM ``BitVec.ofNat #[mkNatLit 64, mkNatLit off]
                    mkAppM ``HAdd.hAdd #[cand.addr, wOff]
                  let (eqMVarS, eqGoalS) ← simplifyAddrEq sliceAddr
                  if !(← eqGoalS.mvarId.isAssigned) then
                    eqGoalS.mvarId.withContext do
                      let eqT ← instantiateMVars (← eqGoalS.mvarId.getType)
                      if eqT.isAppOfArity ``Eq 3 then
                        let lhs := eqT.appFn!.appArg!
                        let rhs := eqT.appArg!
                        if ← withReducible (isDefEq lhs rhs) then
                          eqGoalS.mvarId.assign (← mkEqRefl lhs)
                  unless ← eqGoalS.mvarId.isAssigned do
                    let cleanMVarId ← clearSepAndLets eqGoalS.mvarId
                    let gS ← Grind.liftGrindM (Grind.mkGoal cleanMVarId)
                    let gS ← Grind.liftGrindM gS.internalizeAll
                    match ← Grind.liftGrindM gS.grind with
                    | .closed => pure ()
                    | .failed _ => failure
                  let hEqS ← instantiateMVars eqMVarS
                  if ← tryAssignSliceAndCancel cand off hEqS then
                    pure true
                  else
                    savedSlice.restore
                    pure false
                catch _ =>
                  savedSlice.restore
                  pure false
              let peelSingleBitVecAddOffset (e : Expr) : MetaM (Expr × Nat) := do
                let e := e.consumeMData
                if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``BitVec.add 3 then
                  let args := e.getAppArgs
                  let a := args[args.size - 2]!
                  let b := args[args.size - 1]!.consumeMData
                  if let some ⟨64, bv⟩ ← getBitVecValue? b then
                    let n := bv.toNat
                    if 0 < n && n ≤ 4096 then
                      return (a, n)
                return (e, 0)
              let tryProveBitVecAddEq (lhs rhs : Expr) : MetaM (Option Expr) := do
                if lhs == rhs then
                  return some (← mkEqRefl lhs)
                let (lhsBase, lhsOff) ← peelBitVecAddOffset lhs
                let (rhsBase, rhsOff) ← peelBitVecAddOffset rhs
                if lhsOff != rhsOff then
                  return none
                let (lhs1, lOff1) ← peelSingleBitVecAddOffset lhs
                let (rhs1, rOff1) ← peelSingleBitVecAddOffset rhs
                if lOff1 == lhsOff && rOff1 == rhsOff then
                  if ← withReducible (isDefEq lhsBase rhsBase <&&> isDefEq lhs rhs) then
                    return some (← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs))
                  else
                    return none
                else if lOff1 > 0 && lOff1 < lhsOff && rOff1 == rhsOff && rOff1 > 0 then
                  let (lhs2, lOff2) ← peelSingleBitVecAddOffset lhs1
                  if lOff1 + lOff2 == lhsOff && (← withReducible (isDefEq lhs2 rhsBase)) then
                    let a := (lhs1.getAppArgs)[lhs1.getAppArgs.size - 1]!
                    let b := (lhs.getAppArgs)[lhs.getAppArgs.size - 1]!
                    let c := (rhs.getAppArgs)[rhs.getAppArgs.size - 1]!
                    let hAdd ← mkExpectedTypeHint (← mkEqRefl c) (← mkEq (← mkAppM ``HAdd.hAdd #[a, b]) c)
                    let prf := mkAppN (mkConst ``BitVec.add_add_eq_of_add_eq) #[mkNatLit 64, lhs2, a, b, c, hAdd]
                    if lhs2 == rhsBase then
                      return some prf
                    else
                      return some (← mkExpectedTypeHint prf (← mkEq lhs rhs))
                  else
                    return none
                else if rOff1 > 0 && rOff1 < rhsOff && lOff1 == lhsOff && lOff1 > 0 then
                  let (rhs2, rOff2) ← peelSingleBitVecAddOffset rhs1
                  if rOff1 + rOff2 == rhsOff && (← withReducible (isDefEq lhsBase rhs2)) then
                    let a := (rhs1.getAppArgs)[rhs1.getAppArgs.size - 1]!
                    let b := (rhs.getAppArgs)[rhs.getAppArgs.size - 1]!
                    let c := (lhs.getAppArgs)[lhs.getAppArgs.size - 1]!
                    let hAdd ← mkExpectedTypeHint (← mkEqRefl c) (← mkEq (← mkAppM ``HAdd.hAdd #[a, b]) c)
                    let prf := mkAppN (mkConst ``BitVec.add_eq_add_add_of_add_eq) #[mkNatLit 64, lhsBase, a, b, c, hAdd]
                    if lhsBase == rhs2 then
                      return some prf
                    else
                      return some (← mkExpectedTypeHint prf (← mkEq lhs rhs))
                  else
                    return none
                else
                  return none
              -- Pass 1: fast syntactic / reducible isDefEq / associative offset check across all candidate clauses
              let mut solvedSep := false
              for cand in candidates do
                unless solvedSep do
                  let saved ← Grind.saveState
                  try
                    if let some hEq ← addrGoal.mvarId.withContext (tryProveBitVecAddEq addr cand.addr) then
                      if ← tryAssignAndCancel cand hEq then
                        solvedSep := true
                      else
                        saved.restore
                    else
                      saved.restore
                  catch _ =>
                    saved.restore
              -- Pass 2: unfold local lets + ksimp, then check if closed or reducible isDefEq
              let mut sliceCandidates : Array (Kraken.Tactic.SepAtCandidate × Nat) := #[]
              let mut skipGrindClauseIdxs : Array Nat := #[]
              unless solvedSep do
                for cand in candidates do
                  unless solvedSep do
                    let saved ← Grind.saveState
                    try
                      if config.debug then
                        logInfo m!"[hb={← IO.getNumHeartbeats}] Pass 2 before simplifyAddrEq cand.addr={cand.addr}"
                      let (eqMVar, eqGoal) ← simplifyAddrEq cand.addr
                      if config.debug then
                        logInfo m!"[hb={← IO.getNumHeartbeats}] Pass 2 after simplifyAddrEq"
                      if !(← eqGoal.mvarId.isAssigned) then
                        eqGoal.mvarId.withContext do
                          let eqT ← instantiateMVars (← eqGoal.mvarId.getType)
                          if eqT.isAppOfArity ``Eq 3 then
                            let lhs := eqT.appFn!.appArg!
                            let rhs := eqT.appArg!
                            if let some prf ← tryProveBitVecAddEq lhs rhs then
                              eqGoal.mvarId.assign prf
                      if ← eqGoal.mvarId.isAssigned then
                        let hEq ← instantiateMVars eqMVar
                        if ← tryAssignAndCancel cand hEq then
                          solvedSep := true
                        else
                          saved.restore
                      else
                        let (sliceOffset?, sameBaseDiffOff) ← eqGoal.mvarId.withContext do
                          let eqT ← instantiateMVars (← eqGoal.mvarId.getType)
                          if eqT.isAppOfArity ``Eq 3 then
                            let (lhsBase, lhsOff) ← peelBitVecAddOffset eqT.appFn!.appArg!
                            let (rhsBase, rhsOff) ← peelBitVecAddOffset eqT.appArg!
                            if lhsOff != rhsOff && (← withReducible (isDefEq lhsBase rhsBase)) then
                              if lhsOff > rhsOff then
                                pure (some (lhsOff - rhsOff), true)
                              else
                                pure (none, true)
                            else
                              pure (none, false)
                          else
                            pure (none, false)
                        saved.restore
                        if sameBaseDiffOff then
                          skipGrindClauseIdxs := skipGrindClauseIdxs.push cand.clauseIdx
                        if let some off := sliceOffset? then
                          let canSlice :=
                            if cand.bs.isAppOfArity ``Int.toBytes 2 || cand.bs.isAppOfArity ``Nat.toBytes 2 then
                              match (cand.bs.getArg! 0).rawNatLit? with
                              | some k => off < k
                              | none => true
                            else
                              true
                          if canSlice then
                            sliceCandidates := sliceCandidates.push (cand, off)
                    catch _ =>
                      saved.restore
              -- Pass 2b: try slicing multi-word candidates only after exact-address candidates have been checked
              unless solvedSep do
                for (cand, off) in sliceCandidates do
                  unless solvedSep do
                    if ← trySliceAtOffset cand off then
                      solvedSep := true
              -- Pass 3: full grind on simplified address equality
              unless solvedSep do
                for cand in candidates do
                  unless solvedSep || skipGrindClauseIdxs.contains cand.clauseIdx do
                    let saved ← Grind.saveState
                    try
                      let (eqMVar, eqGoal) ← simplifyAddrEq cand.addr
                      unless ← eqGoal.mvarId.isAssigned do
                        let cleanMVarId ← clearSepAndLets eqGoal.mvarId
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
        if config.debug then
          logInfo m!"[hb={← IO.getNumHeartbeats}] entering STEP 4 (ite) on {effectsAll.appArg!.getArg! 1}"
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
                  withReducible mvarId.refl
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
        let MD := effectsAll.getArg! 0
        let post := effectsAll.getArg! 1
        let gimmickFn := mkConst ``gimmickId
        let allFn := effectsAll.getAppFn
        if let some hc ← tryProveIteCond c then
          let eqPrf := mkAppN (mkConst ``gimmickId_Effects_All_ite_true) #[MD, post, c, inst, hc, t, f]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (mkApp gimmickFn (mkAppN allFn #[MD, post, t])))
          let mvarId ← goal.mvarId.replaceTargetEq rhs eqPrf
          pure (true, { goal with mvarId })
        else if let some hnc ← tryProveIteCond (mkNot c) then
          let eqPrf := mkAppN (mkConst ``gimmickId_Effects_All_ite_false) #[MD, post, c, inst, hnc, t, f]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (mkApp gimmickFn (mkAppN allFn #[MD, post, f])))
          let mvarId ← goal.mvarId.replaceTargetEq rhs eqPrf
          pure (true, { goal with mvarId })
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
