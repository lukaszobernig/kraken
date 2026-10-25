module

import Kraken.Mem
import Kraken.Separation
public meta import Lean.Elab.Tactic
public meta import Lean.Meta.Tactic.AC
public meta import Lean.Meta.Tactic.Grind

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
  | sep (p q : SepTree)
  | atom (e : Expr)

def SepTree.clauses : SepTree → List Expr
  | .emp _ => []
  | .sep p q => p.clauses ++ q.clauses
  | .atom e => [e]

partial def parseSepTree (e : Expr) : MetaM SepTree := do
  let e ← reduceProjectionApp (← instantiateMVars e)
  if e.getAppFn.constName? == some ``Std.ExtHashMap.emp then
    return .emp e
  if e.getAppFn.constName? == some ``Std.ExtHashMap.sep then
    let args := e.getAppArgs
    let p ← parseSepTree args[args.size - 2]!
    let q ← parseSepTree args[args.size - 1]!
    return .sep p q
  return .atom e

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
  | .sep p q =>
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

-- fuel: bound definitional unfolding to avoid expensive general reduction.
private partial def matchClosed (lhs rhs : Expr) (fuel : Nat := 2) : MetaM Bool := do
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  if lhs == rhs then return true
  if lhs.isMVar || rhs.isMVar then return ← isDefEq lhs rhs
  let lhs ← reduceProjectionApp lhs
  let rhs ← reduceProjectionApp rhs
  if lhs == rhs then return true
  if lhs.getAppFn == rhs.getAppFn then
    let lhsArgs := lhs.getAppArgs
    let rhsArgs := rhs.getAppArgs
    unless lhsArgs.size == rhsArgs.size do return false
    for lhsArg in lhsArgs, rhsArg in rhsArgs do
      unless ← matchClosed lhsArg rhsArg fuel do return false
    return true
  if fuel == 0 then
    if !lhs.hasFVar && !rhs.hasFVar && !lhs.hasExprMVar && !rhs.hasExprMVar then
      return ← isDefEq lhs rhs
    return false
  if let some lhs ← unfoldDefinition? lhs then
    if ← matchClosed lhs rhs (fuel - 1) then return true
  if let some rhs ← unfoldDefinition? rhs then
    if ← matchClosed lhs rhs (fuel - 1) then return true
  return false

private def matchAtom (lhs rhs : Expr) : MetaM Bool :=
  matchClosed lhs rhs

private def extractAtBytesAndAddr? (clause : Expr) : MetaM (Option (Expr × Expr)) := do
  let clause ← instantiateMVars clause
  unless clause.isAppOfArity ``Eq 2 do return none
  let rhs := clause.appArg!
  if rhs.isAppOfArity ``List.At 3 then
    return some (rhs.appFn!.appArg!, rhs.appArg!)
  if rhs.isAppOfArity ``UInt64.At 3 then
    return some (← mkAppM ``UInt64.toBytes #[rhs.appFn!.appArg!], rhs.appArg!)
  if rhs.isAppOfArity ``UInt32.At 3 then
    return some (← mkAppM ``UInt32.toBytes #[rhs.appFn!.appArg!], rhs.appArg!)
  if rhs.isAppOfArity ``UInt16.At 3 then
    return some (← mkAppM ``UInt16.toBytes #[rhs.appFn!.appArg!], rhs.appArg!)
  if rhs.isAppOfArity ``UInt8.At 3 then
    return some (← mkAppM ``UInt8.toBytes #[rhs.appFn!.appArg!], rhs.appArg!)
  return none

private def provePropEq (lhs rhs : Expr) : MetaM (Option Expr) :=
  commitWhenSomeNoEx? do
    unless ← isDefEq (← inferType lhs) (← inferType rhs) do return none
    let goal ← mkFreshExprMVar (← mkEq lhs rhs)
    let mut goalId := goal.mvarId!
    for localDecl? in (← getLCtx).decls.toArray.reverse do
      if let some localDecl := localDecl? then
        if localDecl.isLet || (localDecl.type.find? (·.isConstOf ``Std.ExtHashMap)).isSome then
          try goalId ← goalId.clear localDecl.fvarId catch _ => pure ()
    let params ← Lean.Meta.Grind.mkDefaultParams {}
    let res ← Lean.Meta.Grind.main goalId params
    if res.hasFailed then return none
    unless ← goal.mvarId!.isAssigned do return none
    return some (← instantiateMVars goal)

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
  return none

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

private def solveSepEq (lhs rhs : Expr) : MetaM (Option Expr) :=
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
    let some (lhsCan, rhsCan) ← cancelAndAlign predType lhsSlots rhsSlots | return none
    let some (lhs', _, []) ← rebuildSepTree lhsTree lhsCan | return none
    let some (rhs', rhsEq?, []) ← rebuildSepTree rhsTree rhsCan | return none
    let acProof ← mkFreshExprMVar (← mkEq lhs' rhs')
    Lean.Meta.AC.rewriteUnnormalizedRefl acProof.mvarId!
    let acProof ← instantiateMVars acProof
    match rhsEq? with
    | some rhsEq => return some (← mkEqTrans acProof rhsEq)
    | none => return some acProof

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
  clauses : List Expr
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
                clauses
                clauseIdx := idx
                bs
                addr
              }
  return cands

/--
Directly solves a `starGoal` of the form `(Eq (?bs.At ?addr') ⋆ ?R) s.dmem` using a
pre-matched `SepAtCandidate` without re-scanning the local context or re-running
`matchClosed`.
-/
def solveSepAtCandidate (starGoal : MVarId) (cand : SepAtCandidate) : MetaM Bool :=
  starGoal.withContext do
    withConfig (fun config => { config with assignSyntheticOpaque := true }) do
      let res? ← commitWhenSomeNoEx? do
        let target ← reduceProjectionApp (← instantiateMVars (← starGoal.getType))
        unless target.isApp do return none
        let targetFn := target.appFn!
        let predType ← inferType targetFn
        let sepArgs := targetFn.getAppArgs
        unless sepArgs.size >= 2 do return none
        let atClause := sepArgs[sepArgs.size - 2]!
        let rMVar := sepArgs[sepArgs.size - 1]!
        unless atClause.isAppOfArity ``Eq 2 do return none
        let atExpr := atClause.appArg!
        unless atExpr.isAppOfArity ``List.At 3 do return none
        let bsMVar := atExpr.appFn!.appArg!
        let addrMVar := atExpr.appArg!
        unless ← isDefEq addrMVar cand.addr do return none
        unless ← isDefEq bsMVar cand.bs do return none
        let remClauses := cand.clauses.eraseIdx cand.clauseIdx
        unless ← isDefEq rMVar (← denoteClauses predType remClauses) do return none
        let targetTree ← parseSepTree targetFn
        let alignedRhs := (cand.clauses[cand.clauseIdx]! :: remClauses).map (·, none)
        let some (lhs', _, []) ← rebuildSepTree cand.hypTree (cand.clauses.map (·, none)) | return none
        let some (rhs', _, []) ← rebuildSepTree targetTree alignedRhs | return none
        let hSeps ← mkFreshExprMVar (← mkEq lhs' rhs')
        Lean.Meta.AC.rewriteUnnormalizedRefl hSeps.mvarId!
        let hFunEq ← mkAppM ``congrFun #[← instantiateMVars hSeps, cand.hypArg]
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
  let target ← goal.getType
  let solved ← ecancelGoal goal
  unless solved do
    throwError "ecancel: could not automatically solve goal {target}"
end Kraken.Tactic
