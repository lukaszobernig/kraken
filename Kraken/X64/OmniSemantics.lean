module

/-
Omnisemantics for x64.
-/

import Kraken.Attribute
public import Kraken.OmniSemantics
public import Kraken.X64.Semantics

@[expose] public section

theorem MachineData.loadAvx_mono (s : MachineData) (addr : BitVec 64) (w : AvxWidth) (ca : Bool)
    {k₁ k₂ : w.type → MachineData → Effects} {P Q : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ v s' pfx', (k₁ v s').All (P.prepend pfx') → (k₂ v s').All (Q.prepend pfx')) :
    (s.loadAvx addr w k₁ ca).All (P.prepend pfx) → (s.loadAvx addr w k₂ ca).All (Q.prepend pfx) := by
  unfold MachineData.loadAvx
  split
  · exact False.elim
  · dsimp only [Kraken.Effects.All]
    rw [TracedPost.prepend_cons, TracedPost.prepend_cons]
    split
    · exact hk _ _ _
    · exact False.elim

theorem MachineData.storeAvx_mono (s : MachineData) (addr : BitVec 64) {w : AvxWidth} (v : w.type) (ca : Bool)
    {k₁ k₂ : MachineData → Effects} {P Q : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ s' pfx', (k₁ s').All (P.prepend pfx') → (k₂ s').All (Q.prepend pfx')) :
    (s.storeAvx addr v k₁ ca).All (P.prepend pfx) → (s.storeAvx addr v k₂ ca).All (Q.prepend pfx) := by
  unfold MachineData.storeAvx
  split
  · exact False.elim
  · dsimp only [Kraken.Effects.All]
    rw [TracedPost.prepend_cons, TracedPost.prepend_cons]
    split
    · exact hk _ _
    · exact False.elim

section
variable [Labels] [AddressSize]

omit [Labels] [AddressSize] in
theorem Reg.interp_mono {w} (r : Reg w) (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : w.type → MachineData → Effects} {P Q : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ v s' pfx', (k₁ v s').All (P.prepend pfx') → (k₂ v s').All (Q.prepend pfx')) :
    (r.interp s p k₁).All (P.prepend pfx) → (r.interp s p k₂).All (Q.prepend pfx) :=
  hk _ _ pfx

theorem RegOrMem.interp_mono {w} (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : w.type → MachineData → Effects} {P Q : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ v s' pfx', (k₁ v s').All (P.prepend pfx') → (k₂ v s').All (Q.prepend pfx')) :
    (o.interp s p k₁).All (P.prepend pfx) → (o.interp s p k₂).All (Q.prepend pfx) := by
  cases o
  · exact hk _ _ pfx
  · exact MachineData.load_mono _ _ w hk

theorem Operand.interp_mono {w} (o : Operand w) (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : w.type → MachineData → Effects} {P Q : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ v s' pfx', (k₁ v s').All (P.prepend pfx') → (k₂ v s').All (Q.prepend pfx')) :
    (o.interp s p k₁).All (P.prepend pfx) → (o.interp s p k₂).All (Q.prepend pfx) := by
  cases o
  · exact RegOrMem.interp_mono _ s p hk
  · exact hk _ _ pfx

theorem MachineData.set_mono {w} (s : MachineData) (d : Dst w) (v : w.type) (p : Std.Rco Int64)
    {k₁ k₂ : MachineData → Effects} {P Q : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ s' pfx', (k₁ s').All (P.prepend pfx') → (k₂ s').All (Q.prepend pfx')) :
    (s.set d v p k₁).All (P.prepend pfx) → (s.set d v p k₂).All (Q.prepend pfx) := by
  cases d
  · exact hk _ pfx
  · exact MachineData.store_mono _ _ v hk

theorem RelRegOrMem.interp_mono (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : BitVec 64 → MachineData → Effects} {P Q : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ v s' pfx', (k₁ v s').All (P.prepend pfx') → (k₂ v s').All (Q.prepend pfx')) :
    (o.interp s p k₁).All (P.prepend pfx) → (o.interp s p k₂).All (Q.prepend pfx) := by
  cases o
  · exact hk _ _ pfx
  · exact hk _ _ pfx
  · exact MachineData.load_mono _ _ .W64 hk

theorem AvxRegOrMem.interp_mono {w} (o : AvxRegOrMem w) (s : MachineData) (p : Std.Rco Int64) {ca : Bool}
    {k₁ k₂ : w.type → MachineData → Effects} {P Q : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ v s' pfx', (k₁ v s').All (P.prepend pfx') → (k₂ v s').All (Q.prepend pfx')) :
    (o.interp s p k₁ ca).All (P.prepend pfx) → (o.interp s p k₂ ca).All (Q.prepend pfx) := by
  cases o
  · exact hk _ _ pfx
  · exact MachineData.loadAvx_mono _ _ w ca hk

theorem AvxOperand.interp_mono {w} (o : AvxOperand w) (s : MachineData) (p : Std.Rco Int64) {ca : Bool}
    {k₁ k₂ : w.type → MachineData → Effects} {P Q : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ v s' pfx', (k₁ v s').All (P.prepend pfx') → (k₂ v s').All (Q.prepend pfx')) :
    (o.interp s p k₁ ca).All (P.prepend pfx) → (o.interp s p k₂ ca).All (Q.prepend pfx) := by
  cases o
  exact AvxRegOrMem.interp_mono _ s p hk

theorem MachineData.setAvx_mono {w} (s : MachineData) (d : AvxDst w) (v : w.type) (p : Std.Rco Int64) {ca : Bool}
    {k₁ k₂ : MachineData → Effects} {P Q : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ s' pfx', (k₁ s').All (P.prepend pfx') → (k₂ s').All (Q.prepend pfx')) :
    (s.setAvx d v p k₁ ca).All (P.prepend pfx) → (s.setAvx d v p k₂ ca).All (Q.prepend pfx) := by
  cases d
  · exact hk _ pfx
  · exact MachineData.storeAvx_mono _ _ v ca hk

theorem MachineData.setAvxLegacy_mono {w} (s : MachineData) (d : AvxDst w) (v : w.type) (p : Std.Rco Int64) {ca : Bool}
    {k₁ k₂ : MachineData → Effects} {P Q : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ s' pfx', (k₁ s').All (P.prepend pfx') → (k₂ s').All (Q.prepend pfx')) :
    (s.setAvxLegacy d v p k₁ ca).All (P.prepend pfx) → (s.setAvxLegacy d v p k₂ ca).All (Q.prepend pfx) := by
  cases d
  · exact hk _ pfx
  · exact MachineData.storeAvx_mono _ _ v ca hk

set_option maxHeartbeats 2000000 in
theorem Operation.interp_mono {w} (op : Operation w) (p : Std.Rco Int64) (s : MachineData)
    {P Q : TracedPost MachineData} {next₁ next₂ : MachineData → Effects} {jmp₁ jmp₂ : Int64 → MachineData → Effects}
    {pfx : List LeakageEvent}
    (hnext : ∀ s' pfx', (next₁ s').All (P.prepend pfx') → (next₂ s').All (Q.prepend pfx'))
    (hjmp : ∀ a s' pfx', (jmp₁ a s').All (P.prepend pfx') → (jmp₂ a s').All (Q.prepend pfx')) :
    (op.interp p s next₁ jmp₁).All (P.prepend pfx) → (op.interp p s next₂ jmp₂).All (Q.prepend pfx) := by
  cases op <;> simp only [Operation.interp]
  all_goals
    repeat' first
      | exact hnext _ _
      | exact hjmp _ _ _
      | exact False.elim
      | apply Operand.interp_mono; intro _ _ _
      | apply RegOrMem.interp_mono; intro _ _ _
      | apply RelRegOrMem.interp_mono; intro _ _ _
      | apply Reg.interp_mono; intro _ _ _
      | apply MachineData.set_mono; intro _ _
      | apply MachineData.load_mono; intro _ _ _
      | apply MachineData.store_mono; intro _ _
      | apply Effects.undefined_mono; intro _ _
      | apply Effects.require_const_time_mono; intro _ _
      | split

theorem AvxOperation.interp_mono {w} (op : AvxOperation w) (p : Std.Rco Int64) (s : MachineData)
    {P Q : TracedPost MachineData} {next₁ next₂ : MachineData → Effects} {pfx : List LeakageEvent}
    (hnext : ∀ s' pfx', (next₁ s').All (P.prepend pfx') → (next₂ s').All (Q.prepend pfx')) :
    (op.interp p s next₁).All (P.prepend pfx) → (op.interp p s next₂).All (Q.prepend pfx) := by
  cases op with
  | movups dst src => exact AvxOperand.interp_mono _ s p fun _ _ _ => MachineData.setAvxLegacy_mono _ dst _ p hnext
  | vmovups dst src => exact AvxOperand.interp_mono _ s p fun _ _ _ => MachineData.setAvx_mono _ dst _ p hnext
  | movaps dst src => exact AvxOperand.interp_mono _ s p fun _ _ _ => MachineData.setAvxLegacy_mono _ dst _ p hnext
  | subps dst src =>
    exact AvxOperand.interp_mono _ s p fun _ _ _ =>
      AvxRegOrMem.interp_mono _ _ p fun _ _ _ =>
        MachineData.setAvxLegacy_mono _ _ _ p hnext
  | addps dst src =>
    exact AvxOperand.interp_mono _ s p fun _ _ _ =>
      AvxRegOrMem.interp_mono _ _ p fun _ _ _ =>
        MachineData.setAvxLegacy_mono _ _ _ p hnext

end

theorem Instr.interp_mono [Labels] (i : Instr) (s : MachineData) (p : Std.Rco Int64)
    {P Q : TracedPost MachineData} {next₁ next₂ : MachineData → Effects} {jmp₁ jmp₂ : Int64 → MachineData → Effects}
    {pfx : List LeakageEvent}
    (hnext : ∀ s' pfx', (next₁ s').All (P.prepend pfx') → (next₂ s').All (Q.prepend pfx'))
    (hjmp : ∀ a s' pfx', (jmp₁ a s').All (P.prepend pfx') → (jmp₂ a s').All (Q.prepend pfx')) :
    (i.interp s p next₁ jmp₁).All (P.prepend pfx) → (i.interp s p next₂ jmp₂).All (Q.prepend pfx) := by
  rcases i with ⟨addr_sz, op_sz, op⟩ | ⟨addr_sz, op_sz, op⟩ <;>
    (dsimp only [Instr.interp, Kraken.Effects.All]; rw [TracedPost.prepend_cons, TracedPost.prepend_cons])
  · letI : AddressSize := ⟨addr_sz⟩
    exact Operation.interp_mono op p s hnext hjmp
  · letI : AddressSize := ⟨addr_sz⟩
    exact AvxOperation.interp_mono op p s hnext

theorem Directive.interp_mono [Labels] (d : Directive) (s : MachineData) (p : Std.Rco Int64)
    {P Q : TracedPost MachineData} {next₁ next₂ : MachineData → Effects} {jmp₁ jmp₂ : Int64 → MachineData → Effects}
    {pfx : List LeakageEvent}
    (hnext : ∀ s' pfx', (next₁ s').All (P.prepend pfx') → (next₂ s').All (Q.prepend pfx'))
    (hjmp : ∀ a s' pfx', (jmp₁ a s').All (P.prepend pfx') → (jmp₂ a s').All (Q.prepend pfx')) :
    (d.interp s p next₁ jmp₁).All (P.prepend pfx) → (d.interp s p next₂ jmp₂).All (Q.prepend pfx) := by
  cases d with
  | label _ => exact hnext s pfx
  | instr i => exact Instr.interp_mono i s p hnext hjmp
  | byteArray _ => exact False.elim

instance : OmniDirective Directive where
  interp_mono := Directive.interp_mono
