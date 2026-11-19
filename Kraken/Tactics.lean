module

/-
Common Kraken Proof Tactics.

Core tactics and theorems for stepping through Kraken assembly proofs.
-/

public import Kraken.Attribute
import Kraken.Layout
import Kraken.OmniSemantics

public meta section

open Lean Meta Elab Tactic Kraken

/-- Set up a straight-line proof for `p` from `s`, naming the state fields and
general-purpose registers. `status` and `dmem` are called `flags` and `mem`. -/
syntax (name := kprologue) "kprologue" ident "with" ident : tactic

private def kprologueBinderName (field : Lean.Name) : Lean.Name :=
  if field == `status then `flags
  else if field == `dmem then `mem
  else field

elab_rules : tactic
  | `(tactic| kprologue $p:ident with $s:ident) => withMainContext do
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

      let rec peelTargetLets : Expr → Expr
        | .letE _ _ _ b _ => peelTargetLets b
        | .mdata _ b => peelTargetLets b
        | e => e
      let target ← withReducible <| whnf <| peelTargetLets (← instantiateMVars (← getMainTarget))
      if target.getAppFn.isConstOf `Eventually then
        evalTactic (← `(tactic|
          obtain $statePat:rcasesPat := $s))
      else
        let straightlineStepId := mkIdent `straightlineStep
        let execStraightlineId := mkIdent `Executable.straightline

        evalTactic (← `(tactic|
          (let ss := $s
           change ($straightlineStepId:ident _ ⟨ss, _⟩ _)
           obtain $statePat:rcasesPat := $s
           delta $p
           dsimp only [$straightlineStepId:ident, $execStraightlineId:ident]
           rw [Kraken.Layout.directivesFromStart]
           dsimp only [Kraken.Program.stripLabels, Kraken.Layout.layoutGo])))

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

    if f.isConstOf `Effects.All && args.size == 3 && args[2]!.isApp && args[2]!.getAppFn'.isConstOf `Directives.interp then
      -- We optionally track how many times we've hit Directives.interp -- this tracks how
      -- many instructions we've stepped through.
      if (← maxInstrCount.mapM (·.get)) = .some 0 then
        return .rfl
      maxInstrCount.forM (fun r => r.modify (· - 1))

      -- Finding a node of the form `Effects.All ... (Directives.interp ...)`
      -- means that we are ready to step through. We manually force reduction of
      -- Directives.interp (since it is *not* in our list of targets), then let
      -- everything simplify until we're called again.
      let some arg2 ← Meta.unfoldDefinition? args[2]! true | throwError "can't unfold Directives.interp"
      let e := mkAppN f (args.set! 2 arg2)
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
  let f := e.getAppFn
  let .const declName _ := f | return .rfl
  if declName == ``Kraken.Labels.label? then return .rfl
  let some _projInfo ← getProjectionFnInfo? declName | return .rfl
  let reduceProjCont? (e? : Option Expr) : DSimpM Result := do
    match e? with
    | none   => return .rfl
    | some e =>
      match (← reduceProj? e.getAppFn) with
      | some f => return .step (← shareCommon (mkAppN f e.getAppArgs))
      | none   => return .rfl
  -- TODO: special support for instances?
  reduceProjCont? (← unfoldDefinition? e)

def kLiftLets : DSimproc := fun e => do
  -- We only lift lets to the top-level (which is always an application of
  -- Effects.all)
  unless e.isApp && e.getAppFn'.isConstOf `Effects.All do return .rfl

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
      goal.mvarId.rewrite (← goal.mvarId.getType) heq symm
    let mctx ← getMCtx
    let mvarIds := r.mvarIds.filter fun mvarId => (mctx.getDecl mvarId |>.index) >= mvarCounterSaved
    let eNew ← Grind.liftSymM <| Sym.preprocessExpr r.eNew
    let mvarId ← goal.mvarId.replaceTargetEq eNew r.eqProof
    let mvarIds ← mvarIds.filterM fun mvarId => return !(← mvarId.isAssigned)
    let sideGoals ← mvarIds.mapM fun mvarId => do
      let target ← mvarId.getType
      let target' ← Grind.liftSymM <| Sym.preprocessExpr target
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

  -- TODO: remove once we have lift_lets
  let introsIf (goal: Grind.Goal): Grind.GrindTacticM Grind.Goal := do
    let goal ← removeGimmick goal
    let goal ← match ← Grind.liftGrindM (goal.intros #[]) with
      | Grind.IntrosResult.failed => pure goal
      | .goal _ goal => pure goal
    pure (← insertGimmick goal)

  let rec findLabelIdx? (p lblExpr : Expr) (i : Nat) : MetaM (Option Nat) := do
    let p ← whnfD p
    match_expr p with
    | List.cons _ hd tl =>
      let hd ← whnfD hd
      match_expr hd with
      | Kraken.Directive.label _ _ l' =>
        if ← isDefEq l' lblExpr then return some i else findLabelIdx? tl lblExpr i
      | _ => findLabelIdx? tl lblExpr (i + 1)
    | _ => return none

  let rec getBodyElem? (p : Expr) (i : Nat) : MetaM (Option Expr) := do
    let p ← whnfD p
    match_expr p with
    | List.cons _ hd tl =>
      let hd ← whnfD hd
      match_expr hd with
      | Kraken.Directive.label _ _ _ => getBodyElem? tl i
      | _ => if i == 0 then return some hd else getBodyElem? tl (i - 1)
    | _ => return none

  let matchLayoutApply? (exe : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
    let exe' ← withTransparency .instances (whnfCore exe)
    match_expr exe' with
    | Kraken.Layout.apply instrTy constTy l prog => return some (instrTy, constTy, l, prog)
    | _ => return none

  let matchExeLabels? (L : Expr) : MetaM (Option Expr) := do
    let L' ← withTransparency .instances (whnfCore L)
    if L'.getAppFn.isConstOf ``Kraken.Executable.labels && L'.getAppNumArgs > 0 then
      return some L'.appArg!
    else if let .proj ``Kraken.Executable 2 exe := L' then
      return some exe
    else
      return none

  let proveExeLabel? (L lblExpr : Expr) : MetaM (Option (Expr × Expr)) := do
    let some exe ← matchExeLabels? L | return none
    let some (instrTy, constTy, l, prog) ← matchLayoutApply? exe | return none
    let some k ← findLabelIdx? prog lblExpr 0 | return none
    let s ← saveState
    try
      let kExpr := ToExpr.toExpr k
      let labelsList ← mkAppOptM ``Kraken.Program.extractLabels #[some instrTy, some constTy, some prog]
      let hkLhs ← mkAppM ``List.lookup #[lblExpr, labelsList]
      let hkRhs ← mkAppM ``Option.some #[kExpr]
      let hkType ← mkEq hkLhs hkRhs
      let hkProof ← mkEqRefl hkRhs
      let hkTyped ← mkExpectedTypeHint hkProof hkType
      let heq ← mkAppOptM ``Kraken.Layout.label?_eq_some_addrOf
        #[some instrTy, some constTy, some l, some prog, some lblExpr, some kExpr, some hkTyped]
      let addrExpr ← mkAppOptM ``Kraken.Layout.addrOf #[some instrTy, some constTy, some l, some prog, some kExpr]
      return some (addrExpr, heq)
    catch _ =>
      s.restore
      return none

  let proveLabelLookup? (L lblExpr : Expr) : MetaM (Option (Expr × Expr)) := do
    if let some res ← proveExeLabel? L lblExpr then
      return some res
    let targetLhs := mkApp2 (mkConst ``Kraken.Labels.label?) L lblExpr
    let lctx ← getLCtx
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      match_expr ty with
      | Eq _ lhs rhs =>
        if rhs.isAppOfArity ``Option.some 2 then
          if ← withReducibleAndInstances (isDefEq lhs targetLhs) then
            return some (rhs.getArg! 1, ldecl.toExpr)
      | HasSubset.Subset _ _ lSub lSup =>
        if ← isDefEq lSup L then
          if let some (addrExpr, hSub) ← proveExeLabel? lSub lblExpr then
            return some (addrExpr, mkAppN ldecl.toExpr #[lblExpr, addrExpr, hSub])
      | _ => pure ()
    return none

  let matchEffectsLookupLabel? (e : Expr) : Option (Expr × Expr) :=
    if e.isApp && e.getAppFn.isConstOf `Effects.All && e.getAppArgs.size == 3 then
      let L := e.getArg! 0
      let eff := e.getArg! 2
      if eff.isAppOfArity `Effects.lookup_label 2 then
        some (L, eff.getArg! 0)
      else
        none
    else
      none

  let resolveLabel? (goal : Grind.Goal) : Grind.GrindTacticM (Option Grind.Goal) := do
    let goalT ← goal.withContext do instantiateMVars (← goal.mvarId.getType)
    let_expr gimmickId goalT' := goalT | return none
    let some allApp := goalT'.find? fun e =>
      match matchEffectsLookupLabel? e with
      | some (L, lbl) => !L.hasLooseBVars && !lbl.hasLooseBVars
      | none => false
    | return none
    let some (L, lblExpr) := matchEffectsLookupLabel? allApp | return none
    let some (addrExpr, heq) ← goal.withContext (proveLabelLookup? L lblExpr) | return none
    let saved ← saveState
    try
      let goalNoGim ← removeGimmick goal
      let heqRule ← goalNoGim.withContext do
        let lhs := mkApp2 (mkConst ``Kraken.Labels.label?) L lblExpr
        let rhs ← mkAppM ``Option.some #[addrExpr]
        let heqTyped ← mkExpectedTypeHint heq (← mkEq lhs rhs)
        mkAppOptM `Effects.All_lookup_label_of_eq #[some L, some lblExpr, some addrExpr, some heqTyped]
      let (goalNew, sideGoals) ← rwTarget goalNoGim false heqRule
      unless sideGoals.isEmpty do failure
      return some (← insertGimmick goalNew)
    catch _ =>
      saved.restore
      return none

  let stepAt? (goal : Grind.Goal) : Grind.GrindTacticM (Option Grind.Goal) := do
    let goalT ← goal.withContext do instantiateMVars (← goal.mvarId.getType)
    let_expr gimmickId goalT' := goalT | return none
    let goalT'' ← goal.withContext <| withReducible <| whnf goalT'
    let_expr Eventually _ trans post state := goalT'' | return none
    unless trans.getAppFn.constName?.map (·.getString! == "step1") == some true && trans.getAppNumArgs == 2 do
      return none
    let exe := trans.getArg! 0
    let labels := trans.getArg! 1
    unless state.isApp && state.getAppNumArgs == 2 &&
      (state.getAppFn.constName?.map (·.getString! == "mk") |>.getD false) do
      return none
    let s := state.getArg! 0
    let pc := state.getArg! 1
    -- Normalize `layout.start` to `layout.addrOf p 0` if `exe = layout p`.
    if pc.isAppOfArity ``Kraken.Layout.start 3 then
      if let some (instrTy, constTy, lExe, pExe) ← goal.withContext (matchLayoutApply? exe) then
        if ← goal.withContext (isDefEq (pc.getArg! 2) lExe) then
          let saved0 ← saveState
          try
            let goalNoGim ← removeGimmick goal
            let hZeroTyped ← goalNoGim.withContext do
              let hZero ← mkAppOptM ``Kraken.Layout.addrOf_zero #[some instrTy, some constTy, some lExe, some pExe]
              let addr0 ← mkAppOptM ``Kraken.Layout.addrOf
                #[some instrTy, some constTy, some lExe, some pExe, some (ToExpr.toExpr (0 : Nat))]
              mkExpectedTypeHint hZero (← mkEq addr0 pc)
            let (goalNew, sideGoals) ← rwTarget goalNoGim true hZeroTyped
            unless sideGoals.isEmpty do failure
            return some (← insertGimmick goalNew)
          catch _ =>
            saved0.restore
    unless pc.isAppOfArity ``Kraken.Layout.addrOf 5 do
      return none
    let instrTy := pc.getArg! 0
    let constTy := pc.getArg! 1
    let l := pc.getArg! 2
    let p := pc.getArg! 3
    let kExpr := pc.getArg! 4
    let some k := kExpr.nat? <|> kExpr.rawNatLit? | return none
    let some d ← goal.withContext (getBodyElem? p k) | return none
    let isInstr ← goal.withContext do
      let d' ← whnfD d
      return d'.getAppFn.isConstOf ``Kraken.Directive.instr
    if isInstr then
      if (← maxInstrCount.mapM (·.get)) == some 0 then
        return none
    let saved ← saveState
    try
      let goalNoGim ← removeGimmick goal
      let goalNew ← goalNoGim.withContext do
        let dischargeFit (hfitMVar : Expr) : Grind.GrindTacticM Unit := do
          unless ← hfitMVar.mvarId!.assumptionCore do
            let hfitT ← instantiateMVars (← hfitMVar.mvarId!.getType)
            let hfitT' ← Grind.liftSymM <| Sym.preprocessExpr hfitT
            let mvarFit ← hfitMVar.mvarId!.replaceTargetDefEq hfitT'
            let subG : Grind.Goal := { goalNoGim with mvarId := mvarFit }
            let subG ← Grind.liftGrindM subG.internalizeAll
            match ← Grind.liftGrindM subG.grind with
            | .closed => pure ()
            | .failed _ => failure
        let kNatExpr := ToExpr.toExpr k
        let pcExe := mkApp4 (mkConst ``Kraken.Layout.apply) instrTy constTy l p
        let (stepProof, hMVar) ←
          if ← isDefEq pcExe exe then
            let stepConst ← mkConstWithFreshMVarLevels `step_at
            let (mvars, _, _) ← forallMetaBoundedTelescope (← inferType stepConst) 10
            unless ← isDefEq mvars[0]! l do failure
            unless ← isDefEq mvars[1]! p do failure
            unless ← isDefEq mvars[3]! labels do failure
            unless ← isDefEq mvars[4]! kNatExpr do failure
            unless ← isDefEq mvars[5]! d do failure
            unless ← isDefEq mvars[7]! post do failure
            unless ← isDefEq mvars[8]! s do failure
            mvars[6]!.mvarId!.refl
            dischargeFit mvars[2]!
            pure (mkAppN stepConst mvars, mvars[9]!)
          else
            let exeLabels ← mkAppM ``Kraken.Executable.labels #[exe]
            unless ← isDefEq labels exeLabels do failure
            let stepConst ← mkConstWithFreshMVarLevels `step_at_sub
            let (mvars, _, _) ← forallMetaBoundedTelescope (← inferType stepConst) 11
            unless ← isDefEq mvars[0]! l do failure
            unless ← isDefEq mvars[1]! p do failure
            unless ← isDefEq mvars[2]! exe do failure
            unless ← isDefEq mvars[5]! kNatExpr do failure
            unless ← isDefEq mvars[6]! d do failure
            unless ← isDefEq mvars[8]! post do failure
            unless ← isDefEq mvars[9]! s do failure
            mvars[7]!.mvarId!.refl
            unless ← mvars[4]!.mvarId!.assumptionCore do failure
            dischargeFit mvars[3]!
            pure (mkAppN stepConst mvars, mvars[10]!)
        let hType ← instantiateMVars (← hMVar.mvarId!.getType)
        let hType' ← Grind.liftSymM <| Sym.preprocessExpr hType
        let mvarNew ← hMVar.mvarId!.replaceTargetDefEq hType'
        goalNoGim.mvarId.assign stepProof
        return { goalNoGim with mvarId := mvarNew }
      if isInstr then
        maxInstrCount.forM (·.modify (· - 1))
      return some (← insertGimmick goalNew)
    catch _ =>
      saved.restore
      return none

  -- MAIN LOOP
  let rec go (goal: Grind.Goal): Grind.GrindTacticM (Grind.Goal × List Grind.Goal) := do
    -- STEP 1: dsimp
    let goal ← do
      let mvarId ← goal.mvarId.replaceTargetDefEq (← goal.mvarId.withContext <| Grind.liftGrindM $
        Sym.dsimp
          (config := { maxSteps := 1000000 })
          (methods := {
            pre := klog >> evalGround >> kdsimpDecls >> kdsimpMatch >> kdsimpProj >> kbeta })
          (← goal.mvarId.getType))
      introsIf ({ goal with mvarId })

    if config.debug then
      let _ ← goal.mvarId.getType
      logInfo m!"MAIN LOOP, after step 1: {goal.mvarId}"

    if let some goal' ← resolveLabel? goal then
      return ← go goal'

    -- TEMPORARY: trying to simplify binders in the goal
    /- let goal ← Meta.letToHave goal -/
    /- let goal ← Grind.liftGrindM $ shareCommon goal -/
    /- let mvarId ← mvarId.replaceTargetDefEq goal -/

    -- STEP 2: simp
    let (keepGoingSimp, goal) ← Grind.liftGrindM $ do
      let simpResult ← Sym.simpGoal goal.mvarId simpMethods
      match simpResult with
      | .noProgress => pure (false, goal)
      | .goal mvarId => pure (true, { goal with mvarId })
      | .closed => throwError "unexpected"
    if config.debug then
      let t ← goal.mvarId.getType
      logInfo m!"MAIN LOOP, after step 2: {t}"

    -- STEP 3: spec lemmas
    let goalState ← do
      let goalT ← goal.mvarId.getType
      let_expr gimmickId goalT' := goalT | throwError "missing gimmick"
      let goalT' ← instantiateMVars goalT'
      let rec getEffectsState (e : Expr) : Option Expr :=
        match e with
        | .letE _ _ _ body _ => getEffectsState body
        | .mdata _ e => getEffectsState e
        | _ =>
          if e.isApp && e.getAppFn.isConstOf `Effects.All && e.getAppArgs.size == 3 then
            some e.getAppArgs[2]!
          else
            none
      -- No more Effects.All in the goal -- try stepping `Eventually (step1 ...)` if applicable.
      let some state := getEffectsState goalT' | do
        if let some goal' ← stepAt? goal then
          return ← go goal'
        return (goal, [])
      pure state

    let (keepGoingSpec, goal) ←
      match Sym.getMatch (← getMCtx) specTree goalState with
      | #[ thmName ] =>
        logInfo m!"Found a spec lemma: {thmName}"
        let (goal, subGoals) ← rwTarget goal false (mkConst thmName)
        logInfo m!"{subGoals.length} subgoals generated"

        let subGoals ← subGoals.mapM fun (subGoal: Grind.Goal) => do
          -- Try simp -- who knows, one might get lucky
          let simpResult ← Grind.liftGrindM (Sym.simpGoal subGoal.mvarId simpMethods)
          match simpResult with
          | .noProgress => pure subGoal
          | .goal mvarId => pure { subGoal with mvarId }
          | .closed => pure subGoal

        -- Found a spec lemma, which will generate subgoals; for now, subgoals (if not solved
        -- already!) are solved via `exact` (which may pick any hypothesis in the context, beware),
        -- or grind.
        let solveIfNotAlready: Grind.Goal → Grind.GrindTacticM Bool := fun subGoal => do
          -- Already solved this subgoal; skip
          if ← subGoal.mvarId.isAssigned then
            let t ← subGoal.mvarId.getType
            logInfo m!"Already solved: {t}"
            return false

          -- Solvable with exact; we made progress
          if ← withReducible subGoal.mvarId.assumptionCore then
            let t ← subGoal.mvarId.getType
            let .some e ← getExprMVarAssignment? subGoal.mvarId | throwError "oh noes"
            logInfo m!"Solved by exact: {t} by {e}"
            return true

          -- Solvable with refl, maybe.
          try
            subGoal.mvarId.refl
            let t ← subGoal.mvarId.getType
            logInfo m!"Solved by refl: {t}"
            return true
          catch _ => pure ()

          -- Try solving with grind, roll back state otherwise (we don't want to
          -- return the failed Grind state).
          try
            let subGoal ← Grind.liftGrindM subGoal.internalizeAll
            let t ← subGoal.mvarId.getType
            match ← Grind.liftGrindM subGoal.grind with
            | .closed =>
                logInfo m!"Solved by grind: {t}"
                return true
            | .failed _ =>
                logInfo m!"NOT solved by grind: {t}"
                throwError "catch me"
          catch _ =>
            return false

        -- For this reason, we try to be intentional about the order in which we solve subgoals:
        -- solving the ⋆ separation logic predicate first allows making sensible decisions about
        -- metavariables, rather than picking any random hypothesis in the context
        let starGoal ← subGoals.findM? (fun g => do
          let t ← g.mvarId.getType
          if t.getAppFn.isConstOf `Std.ExtHashMap.sep then
            logInfo m!"Found sep goal: {t}"
            return true
          else
            return false
        )

        -- If we couldn't solve the ⋆ goal, we are likely going to make bad
        -- decisions and instantiate metavariables randomly. Abort.
        if let some g := starGoal then
          let solved ← solveIfNotAlready g
          if not solved then
            return (goal, subGoals)

        -- Then, we repeatedly visit subgoals until we make no progress.
        while ← (
          subGoals.foldlM (fun progress subGoal => do
            let r ← solveIfNotAlready subGoal
            pure (r || progress)
          ) false
        ) do pure ()

        -- Unsolved goals left? Return control to the user
        let unsolvedGoals ← subGoals.filterMapM fun (g: Grind.Goal) => do
          if ← g.mvarId.isAssigned then
            return none
          else
            return some g
        unsolvedGoals.forM fun mvarId => do
          let t ← mvarId.mvarId.getType
          logInfo m!"Unsolved goal: {t}"
        if unsolvedGoals.length > 0 then
          return (goal, unsolvedGoals)

        pure (true, goal)
      | #[] =>
        pure (false, goal)
      | _ =>
        throwError "TODO"

    logInfo m!"kstep: keepGoing = {keepGoingSimp}"

    if keepGoingSimp || keepGoingSpec then
      go goal
    else
      pure (goal, [])

  let (goal, subGoals) ← go goal

  -- Remove the gimmick debug marker.
  let goal ← removeGimmick goal

  logInfo m!"END KSTEP: {subGoals.length} sub-goals left"

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
