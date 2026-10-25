module

/-
Omnisemantics for x64.
-/

import Kraken.Attribute
public import Kraken.OmniSemantics
public import Kraken.X64.Semantics

@[expose] public section

theorem MachineData.loadAvx_mono (s : MachineData) (addr : BitVec 64) (w : AvxWidth) (ca : Bool)
    {k₁ k₂ : w.type → MachineData → Effects} {P Q : MachineState → Prop}
    (hk : ∀ v s', (k₁ v s').All P → (k₂ v s').All Q) :
    (s.loadAvx addr w k₁ ca).All P → (s.loadAvx addr w k₂ ca).All Q := by
  unfold MachineData.loadAvx
  split
  · exact False.elim
  · dsimp only [Kraken.Effects.All]
    split
    · exact hk _ _
    · exact False.elim

theorem MachineData.storeAvx_mono (s : MachineData) (addr : BitVec 64) {w : AvxWidth} (v : w.type) (ca : Bool)
    {k₁ k₂ : MachineData → Effects} {P Q : MachineState → Prop}
    (hk : ∀ s', (k₁ s').All P → (k₂ s').All Q) :
    (s.storeAvx addr v k₁ ca).All P → (s.storeAvx addr v k₂ ca).All Q := by
  unfold MachineData.storeAvx
  split
  · exact False.elim
  · dsimp only [Kraken.Effects.All]
    split
    · exact hk _
    · exact False.elim

section
variable [Labels] [AddressSize]

omit [Labels] [AddressSize] in
theorem Reg.interp_mono {w} (r : Reg w) (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : w.type → MachineData → Effects} {P Q : MachineState → Prop}
    (hk : ∀ v s', (k₁ v s').All P → (k₂ v s').All Q) :
    (r.interp s p k₁).All P → (r.interp s p k₂).All Q :=
  hk _ _

theorem RegOrMem.interp_mono {w} (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : w.type → MachineData → Effects} {P Q : MachineState → Prop}
    (hk : ∀ v s', (k₁ v s').All P → (k₂ v s').All Q) :
    (o.interp s p k₁).All P → (o.interp s p k₂).All Q := by
  cases o
  · exact hk _ _
  · exact MachineData.load_mono _ _ w hk

theorem Operand.interp_mono {w} (o : Operand w) (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : w.type → MachineData → Effects} {P Q : MachineState → Prop}
    (hk : ∀ v s', (k₁ v s').All P → (k₂ v s').All Q) :
    (o.interp s p k₁).All P → (o.interp s p k₂).All Q := by
  cases o
  · exact RegOrMem.interp_mono _ s p hk
  · exact hk _ _

theorem MachineData.set_mono {w} (s : MachineData) (d : Dst w) (v : w.type) (p : Std.Rco Int64)
    {k₁ k₂ : MachineData → Effects} {P Q : MachineState → Prop}
    (hk : ∀ s', (k₁ s').All P → (k₂ s').All Q) :
    (s.set d v p k₁).All P → (s.set d v p k₂).All Q := by
  cases d
  · exact hk _
  · exact MachineData.store_mono _ _ v hk

theorem RelRegOrMem.interp_mono (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : BitVec 64 → MachineData → Effects} {P Q : MachineState → Prop}
    (hk : ∀ v s', (k₁ v s').All P → (k₂ v s').All Q) :
    (o.interp s p k₁).All P → (o.interp s p k₂).All Q := by
  cases o
  · exact hk _ _
  · exact hk _ _
  · exact MachineData.load_mono _ _ .W64 hk

theorem AvxRegOrMem.interp_mono {w} (o : AvxRegOrMem w) (s : MachineData) (p : Std.Rco Int64) {ca : Bool}
    {k₁ k₂ : w.type → MachineData → Effects} {P Q : MachineState → Prop}
    (hk : ∀ v s', (k₁ v s').All P → (k₂ v s').All Q) :
    (o.interp s p k₁ ca).All P → (o.interp s p k₂ ca).All Q := by
  cases o
  · exact hk _ _
  · exact MachineData.loadAvx_mono _ _ w ca hk

theorem AvxOperand.interp_mono {w} (o : AvxOperand w) (s : MachineData) (p : Std.Rco Int64) {ca : Bool}
    {k₁ k₂ : w.type → MachineData → Effects} {P Q : MachineState → Prop}
    (hk : ∀ v s', (k₁ v s').All P → (k₂ v s').All Q) :
    (o.interp s p k₁ ca).All P → (o.interp s p k₂ ca).All Q := by
  cases o
  exact AvxRegOrMem.interp_mono _ s p hk

theorem MachineData.setAvx_mono {w} (s : MachineData) (d : AvxDst w) (v : w.type) (p : Std.Rco Int64) {ca : Bool}
    {k₁ k₂ : MachineData → Effects} {P Q : MachineState → Prop}
    (hk : ∀ s', (k₁ s').All P → (k₂ s').All Q) :
    (s.setAvx d v p k₁ ca).All P → (s.setAvx d v p k₂ ca).All Q := by
  cases d
  · exact hk _
  · exact MachineData.storeAvx_mono _ _ v ca hk

theorem MachineData.setAvxLegacy_mono {w} (s : MachineData) (d : AvxDst w) (v : w.type) (p : Std.Rco Int64) {ca : Bool}
    {k₁ k₂ : MachineData → Effects} {P Q : MachineState → Prop}
    (hk : ∀ s', (k₁ s').All P → (k₂ s').All Q) :
    (s.setAvxLegacy d v p k₁ ca).All P → (s.setAvxLegacy d v p k₂ ca).All Q := by
  cases d
  · exact hk _
  · exact MachineData.storeAvx_mono _ _ v ca hk

set_option maxHeartbeats 2000000 in
theorem Operation.interp_mono {w} (op : Operation w) (p : Std.Rco Int64) (s : MachineData)
    {P Q : MachineState → Prop} {next₁ next₂ : MachineData → Effects} {jmp₁ jmp₂ : Int64 → MachineData → Effects}
    (hnext : ∀ s', (next₁ s').All P → (next₂ s').All Q)
    (hjmp : ∀ a s', (jmp₁ a s').All P → (jmp₂ a s').All Q) :
    (op.interp p s next₁ jmp₁).All P → (op.interp p s next₂ jmp₂).All Q := by
  cases op <;> simp only [Operation.interp]
  all_goals
    repeat' first
      | exact hnext _
      | exact hjmp _ _
      | exact False.elim
      | apply Operand.interp_mono; intro _ _
      | apply RegOrMem.interp_mono; intro _ _
      | apply RelRegOrMem.interp_mono; intro _ _
      | apply Reg.interp_mono; intro _ _
      | apply MachineData.set_mono; intro _
      | apply MachineData.load_mono; intro _ _
      | apply MachineData.store_mono; intro _
      | apply Effects.undefined_mono; intro _
      | split

theorem AvxOperation.interp_mono {w} (op : AvxOperation w) (p : Std.Rco Int64) (s : MachineData)
    {P Q : MachineState → Prop} {next₁ next₂ : MachineData → Effects}
    (hnext : ∀ s', (next₁ s').All P → (next₂ s').All Q) :
    (op.interp p s next₁).All P → (op.interp p s next₂).All Q := by
  cases op with
  | movups dst src => exact AvxOperand.interp_mono _ s p fun _ _ => MachineData.setAvxLegacy_mono _ dst _ p hnext
  | vmovups dst src => exact AvxOperand.interp_mono _ s p fun _ _ => MachineData.setAvx_mono _ dst _ p hnext
  | movaps dst src => exact AvxOperand.interp_mono _ s p fun _ _ => MachineData.setAvxLegacy_mono _ dst _ p hnext
  | subps dst src =>
    exact AvxOperand.interp_mono _ s p fun _ _ =>
      AvxRegOrMem.interp_mono _ _ p fun _ _ =>
        MachineData.setAvxLegacy_mono _ _ _ p hnext
  | addps dst src =>
    exact AvxOperand.interp_mono _ s p fun _ _ =>
      AvxRegOrMem.interp_mono _ _ p fun _ _ =>
        MachineData.setAvxLegacy_mono _ _ _ p hnext

end

theorem Instr.interp_mono [Labels] (i : Instr) (s : MachineData) (p : Std.Rco Int64)
    {P Q : MachineState → Prop} {next₁ next₂ : MachineData → Effects} {jmp₁ jmp₂ : Int64 → MachineData → Effects}
    (hnext : ∀ s', (next₁ s').All P → (next₂ s').All Q)
    (hjmp : ∀ a s', (jmp₁ a s').All P → (jmp₂ a s').All Q) :
    (i.interp s p next₁ jmp₁).All P → (i.interp s p next₂ jmp₂).All Q := by
  rcases i with ⟨addr_sz, op_sz, op⟩ | ⟨addr_sz, op_sz, op⟩ <;> dsimp only [Instr.interp, Kraken.Effects.All]
  · letI : AddressSize := ⟨addr_sz⟩
    exact Operation.interp_mono op p s hnext hjmp
  · letI : AddressSize := ⟨addr_sz⟩
    exact AvxOperation.interp_mono op p s hnext

theorem Directive.interp_mono [Labels] (d : Directive) (s : MachineData) (p : Std.Rco Int64)
    {P Q : MachineState → Prop} {next₁ next₂ : MachineData → Effects} {jmp₁ jmp₂ : Int64 → MachineData → Effects}
    (hnext : ∀ s', (next₁ s').All P → (next₂ s').All Q)
    (hjmp : ∀ a s', (jmp₁ a s').All P → (jmp₂ a s').All Q) :
    (d.interp s p next₁ jmp₁).All P → (d.interp s p next₂ jmp₂).All Q := by
  cases d with
  | label _ => exact hnext s
  | instr i => exact Instr.interp_mono i s p hnext hjmp
  | byteArray _ => exact False.elim

instance : OmniDirective Directive where
  interp_mono := Directive.interp_mono
