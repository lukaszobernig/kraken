module

/-
Omnisemantics for AArch64.
-/

public import Kraken.AArch64.Semantics
import Kraken.Attribute
public import Kraken.OmniSemantics

@[expose] public section

theorem AddrExpr.checkSPAlignment_mono (mem : AddrExpr) (s : MachineData)
    {k₁ k₂ : Unit → Effects} {Q₁ Q₂ : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ u pfx', (k₁ u).All (Q₁.prepend pfx') → (k₂ u).All (Q₂.prepend pfx')) :
    (mem.checkSPAlignment s k₁).All (Q₁.prepend pfx) → (mem.checkSPAlignment s k₂).All (Q₂.prepend pfx) := by
  unfold AddrExpr.checkSPAlignment
  split
  · split
    · exact False.elim
    · exact hk () pfx
  · exact hk () pfx

theorem AddrExpr.interpLoad_mono [Labels] {w : Width} (mem : AddrExpr)
    (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : w.type → MachineData → Effects} {Q₁ Q₂ : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ v s' pfx', (k₁ v s').All (Q₁.prepend pfx') → (k₂ v s').All (Q₂.prepend pfx')) :
    (mem.interpLoad s p k₁).All (Q₁.prepend pfx) → (mem.interpLoad s p k₂).All (Q₂.prepend pfx) := by
  unfold AddrExpr.interpLoad
  exact AddrExpr.checkSPAlignment_mono mem s fun _ _ =>
    MachineData.load_mono _ _ w hk

theorem AddrExpr.interpStore_mono [Labels] {w : Width} (mem : AddrExpr)
    (s : MachineData) (p : Std.Rco Int64) (val : w.type)
    {k₁ k₂ : MachineData → Effects} {Q₁ Q₂ : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ s' pfx', (k₁ s').All (Q₁.prepend pfx') → (k₂ s').All (Q₂.prepend pfx')) :
    (mem.interpStore s p val k₁).All (Q₁.prepend pfx) → (mem.interpStore s p val k₂).All (Q₂.prepend pfx) := by
  unfold AddrExpr.interpStore
  exact AddrExpr.checkSPAlignment_mono mem s fun _ _ =>
    MachineData.store_mono _ _ val hk

theorem UnscaledAddrExpr.checkSPAlignment_mono (mem : UnscaledAddrExpr) (s : MachineData)
    {k₁ k₂ : Unit → Effects} {Q₁ Q₂ : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ u pfx', (k₁ u).All (Q₁.prepend pfx') → (k₂ u).All (Q₂.prepend pfx')) :
    (mem.checkSPAlignment s k₁).All (Q₁.prepend pfx) → (mem.checkSPAlignment s k₂).All (Q₂.prepend pfx) := by
  unfold UnscaledAddrExpr.checkSPAlignment
  split
  · split
    · exact False.elim
    · exact hk () pfx
  · exact hk () pfx

theorem UnscaledAddrExpr.interpLoad_mono [Labels] {w : Width} (mem : UnscaledAddrExpr)
    (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : w.type → MachineData → Effects} {Q₁ Q₂ : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ v s' pfx', (k₁ v s').All (Q₁.prepend pfx') → (k₂ v s').All (Q₂.prepend pfx')) :
    (mem.interpLoad s p k₁).All (Q₁.prepend pfx) → (mem.interpLoad s p k₂).All (Q₂.prepend pfx) := by
  unfold UnscaledAddrExpr.interpLoad
  exact UnscaledAddrExpr.checkSPAlignment_mono mem s fun _ _ =>
    MachineData.load_mono _ _ w hk

theorem UnscaledAddrExpr.interpStore_mono [Labels] {w : Width} (mem : UnscaledAddrExpr)
    (s : MachineData) (p : Std.Rco Int64) (val : w.type)
    {k₁ k₂ : MachineData → Effects} {Q₁ Q₂ : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ s' pfx', (k₁ s').All (Q₁.prepend pfx') → (k₂ s').All (Q₂.prepend pfx')) :
    (mem.interpStore s p val k₁).All (Q₁.prepend pfx) → (mem.interpStore s p val k₂).All (Q₂.prepend pfx) := by
  unfold UnscaledAddrExpr.interpStore
  exact UnscaledAddrExpr.checkSPAlignment_mono mem s fun _ _ =>
    MachineData.store_mono _ _ val hk

theorem Literal.interpLoad_mono [Labels] {w : Width} (expr : Literal)
    (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : w.type → MachineData → Effects} {Q₁ Q₂ : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ v s' pfx', (k₁ v s').All (Q₁.prepend pfx') → (k₂ v s').All (Q₂.prepend pfx')) :
    (expr.interpLoad s p k₁).All (Q₁.prepend pfx) → (expr.interpLoad s p k₂).All (Q₂.prepend pfx) := by
  unfold Literal.interpLoad
  split
  · exact MachineData.load_mono _ _ w hk
  · exact hk _ _ pfx

theorem AddrOrLit.interpLoad_mono [Labels] {w : Width} (expr : AddrOrLit)
    (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : w.type → MachineData → Effects} {Q₁ Q₂ : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ v s' pfx', (k₁ v s').All (Q₁.prepend pfx') → (k₂ v s').All (Q₂.prepend pfx')) :
    (expr.interpLoad s p k₁).All (Q₁.prepend pfx) → (expr.interpLoad s p k₂).All (Q₂.prepend pfx) := by
  unfold AddrOrLit.interpLoad
  split
  · exact AddrExpr.interpLoad_mono _ s p hk
  · exact Literal.interpLoad_mono _ s p hk

theorem MachineData.setRegOrSp_mono (s : MachineData) {w} (r : RegOrSp w) (v : w.type)
    {k₁ k₂ : MachineData → Effects} {Q₁ Q₂ : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ s' pfx', (k₁ s').All (Q₁.prepend pfx') → (k₂ s').All (Q₂.prepend pfx')) :
    (s.setRegOrSp r v k₁).All (Q₁.prepend pfx) → (s.setRegOrSp r v k₂).All (Q₂.prepend pfx) :=
  hk _ pfx

theorem MachineData.setRegOrZr_mono (s : MachineData) {w} (r : RegOrZr w) (v : w.type)
    {k₁ k₂ : MachineData → Effects} {Q₁ Q₂ : TracedPost MachineData} {pfx : List LeakageEvent}
    (hk : ∀ s' pfx', (k₁ s').All (Q₁.prepend pfx') → (k₂ s').All (Q₂.prepend pfx')) :
    (s.setRegOrZr r v k₁).All (Q₁.prepend pfx) → (s.setRegOrZr r v k₂).All (Q₂.prepend pfx) :=
  hk _ pfx

set_option maxHeartbeats 2000000 in
theorem Operation.interp_mono [Labels] {w} (op : Operation w) (p : Std.Rco Int64) (s : MachineData)
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
      | apply AddrOrLit.interpLoad_mono; intro _ _ _
      | apply AddrExpr.interpLoad_mono; intro _ _ _
      | apply AddrExpr.interpStore_mono; intro _ _
      | apply AddrExpr.checkSPAlignment_mono; intro _ _
      | apply UnscaledAddrExpr.interpLoad_mono; intro _ _ _
      | apply UnscaledAddrExpr.interpStore_mono; intro _ _
      | apply UnscaledAddrExpr.checkSPAlignment_mono; intro _ _
      | apply MachineData.load_mono; intro _ _ _
      | apply MachineData.store_mono; intro _ _
      | apply MachineData.setRegOrSp_mono; intro _ _
      | apply MachineData.setRegOrZr_mono; intro _ _
      | apply Effects.require_const_time_mono; intro _ _
      | split

theorem Instr.interp_mono [Labels] (i : Instr) (s : MachineData) (p : Std.Rco Int64)
    {P Q : TracedPost MachineData} {next₁ next₂ : MachineData → Effects} {jmp₁ jmp₂ : Int64 → MachineData → Effects}
    {pfx : List LeakageEvent}
    (hnext : ∀ s' pfx', (next₁ s').All (P.prepend pfx') → (next₂ s').All (Q.prepend pfx'))
    (hjmp : ∀ a s' pfx', (jmp₁ a s').All (P.prepend pfx') → (jmp₂ a s').All (Q.prepend pfx')) :
    (i.interp s p next₁ jmp₁).All (P.prepend pfx) → (i.interp s p next₂ jmp₂).All (Q.prepend pfx) := by
  unfold Instr.interp
  dsimp only [Kraken.Effects.All]
  rw [TracedPost.prepend_cons, TracedPost.prepend_cons]
  exact Operation.interp_mono i.operation p s hnext hjmp

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
