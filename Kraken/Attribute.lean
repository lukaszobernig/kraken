module

public meta import Lean

public meta section

open Lean

initialize kstepExtension : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    name := `kstepExtension
    addEntry := fun s n => s.insert n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `kstep
  descr := "declarations to be reduced in the goal as part of the kstep tactic"
  add := fun declName _stx _kind => do
    modifyEnv fun env => kstepExtension.addEntry env declName
}

initialize kspecExtension : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    name := `kspecExtension
    addEntry := fun s n => s.insert n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `kspec
  descr := "specification lemmas for built-in, in separation logic, to be leveraged by the kstep tactic"
  add := fun declName _stx _kind => do
    modifyEnv fun env => kspecExtension.addEntry env declName
}

open Lean.Meta

initialize ksimpExt : Sym.Simp.SymSimpExtension ←
  Sym.Simp.registerSymSimpAttr `ksimp "simp theorems used by kstep"

/-- Simp lemmas that present processor flags and branch conditions at the value level, e.g.
`(StatusFlags.subs a b).c = decide (b.toNat ≤ a.toNat)`. They are used by `kstep` when it
decides a branch condition and by `kfinish`, but not while stepping, so that the flag functions
(`StatusFlags.subs a b`, …) stay folded in the symbolic state. -/
initialize kcondExt : SimpExtension ←
  registerSimpAttr `kcond "simp lemmas presenting flags and branch conditions at the value level"
