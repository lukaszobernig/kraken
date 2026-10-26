module

/-
Register frames ("modifies" clauses) for Kraken block specifications.

A block specification states which registers a block *writes*; every other register is
preserved. `r' ≡ r except [X13, X14]` says that register files `r'` and `r` agree on every
register other than `X13` and `X14`. The register names are resolved against the `RegFile`
instance of the register-file type, so the notation (and the tactics `kframe`/`kframe_eqs`)
work for any architecture.
-/

public meta import Lean

@[expose] public section

namespace Kraken

/-- A register file `R` with a finite set of register `Name`s, all holding 64-bit values. -/
class RegFile (R : Type) where
  Name : Type
  get : R → Name → UInt64
  /-- All register names. -/
  names : List Name
  mem_names : ∀ n, n ∈ names

namespace RegFile

variable {R : Type} [RegFile R]

/-- `r'` agrees with `r` on every register not in `W`. -/
def EqExcept (W : List (Name R)) (r' r : R) : Prop :=
  ∀ n, n ∉ W → RegFile.get r' n = RegFile.get r n

theorem EqExcept.refl (W : List (Name R)) (r : R) : EqExcept W r r :=
  fun _ _ => rfl

theorem EqExcept.get {W : List (Name R)} {r' r : R} (h : EqExcept W r' r)
    (n : Name R) (hn : n ∉ W := by simp) : RegFile.get r' n = RegFile.get r n :=
  h n hn

theorem EqExcept.mono {W W' : List (Name R)} {r' r : R} (h : EqExcept W r' r)
    (hW : ∀ n, n ∈ W → n ∈ W') : EqExcept W' r' r :=
  fun n hn => h n fun hmem => hn (hW n hmem)

theorem EqExcept.trans {W₁ W₂ : List (Name R)} {r₁ r₂ r₃ : R}
    (h₁ : EqExcept W₁ r₂ r₁) (h₂ : EqExcept W₂ r₃ r₂) : EqExcept (W₁ ++ W₂) r₃ r₁ :=
  fun n hn =>
    have hn₁ : n ∉ W₁ := fun h => hn (List.mem_append_left _ h)
    have hn₂ : n ∉ W₂ := fun h => hn (List.mem_append_right _ h)
    (h₂ n hn₂).trans (h₁ n hn₁)

theorem EqExcept.symm {W : List (Name R)} {r' r : R} (h : EqExcept W r' r) : EqExcept W r r' :=
  fun n hn => (h n hn).symm

theorem EqExcept.nil_iff {r' r : R} : EqExcept [] r' r ↔ ∀ n, RegFile.get r' n = RegFile.get r n :=
  ⟨fun h n => h n (List.not_mem_nil), fun h n _ => h n⟩

end RegFile

end Kraken

end

public meta section

open Lean Meta Elab Term

namespace Kraken.RegFile

/-- `r' ≡ r except [a, b, …]`: `r'` and `r` agree on all registers but `a, b, …`
(see `Kraken.RegFile.EqExcept`). The names are constructors of the register-name type of
`r'`/`r` (possibly nested one level, e.g. `X13` for `XRegOrSp.reg XReg.X13`). -/
syntax:50 term:51 " ≡ " term:51 " except " "[" ident,* "]" : term

/-- Resolve a register name against the constructors of `nameTy` (one level of nesting allowed). -/
private def resolveRegName (nameTy : Lean.Name) (id : Ident) : MetaM Expr := do
  let s := id.getId.toString
  let info ← getConstInfoInduct nameTy
  for c in info.ctors do
    let cinfo ← getConstInfoCtor c
    if c.getString! == s && cinfo.numFields == 0 then
      return mkConst c
  for c in info.ctors do
    let cinfo ← getConstInfoCtor c
    if cinfo.numFields == 1 then
      let fieldTy ← forallTelescopeReducing cinfo.type fun xs _ => do
        inferType xs[xs.size - 1]!
      if let .const innerTy _ := fieldTy.getAppFn then
        if let some innerInfo := (← getEnv).find? innerTy then
          if let .inductInfo innerInd := innerInfo then
            for c' in innerInd.ctors do
              let c'info ← getConstInfoCtor c'
              if c'.getString! == s && c'info.numFields == 0 then
                return mkApp (mkConst c) (mkConst c')
  throwErrorAt id "unknown register `{s}` for register names of type `{nameTy}`"

elab_rules : term
  | `($r':term ≡ $r:term except [$ns:ident,*]) => do
    let r' ← elabTerm r' none
    let R ← instantiateMVars (← inferType r')
    let r ← elabTermEnsuringType r R
    let inst ← synthInstance (mkApp (mkConst ``Kraken.RegFile) R)
    let nameTyE ← whnf (mkApp2 (mkConst ``Kraken.RegFile.Name) R inst)
    let .const nameTy _ := nameTyE.getAppFn
      | throwError "`≡ … except` : register names of `{R}` are not an inductive type ({nameTyE})"
    let elems ← ns.getElems.mapM fun id => (resolveRegName nameTy id : MetaM Expr)
    let W ← mkListLit nameTyE elems.toList
    return mkAppN (mkConst ``Kraken.RegFile.EqExcept) #[R, inst, W, r', r]

/-- Last identifier component of a register-name term, for pretty printing. -/
private partial def regNameIdent? (stx : Term) : Option Ident :=
  match stx with
  | `(↑$a:term) => regNameIdent? a
  | `($f:ident $a:term) => regNameIdent? a <|> some (mkIdent f.getId.getString!.toName)
  | `($x:ident) => some (mkIdent x.getId.getString!.toName)
  | `(.$x:ident) => some x
  | `(.$f:ident $a:term) => regNameIdent? a <|> some f
  | `(($t:term)) => regNameIdent? t
  | _ => none

@[app_unexpander Kraken.RegFile.EqExcept]
def unexpandEqExcept : PrettyPrinter.Unexpander
  | `($_ [$ns:term,*] $r' $r) => do
    let some ids := ns.getElems.mapM regNameIdent? | throw ()
    `($r' ≡ $r except [$ids,*])
  | _ => throw ()

end Kraken.RegFile

end
