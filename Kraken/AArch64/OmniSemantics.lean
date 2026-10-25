module

/-
Omnisemantics for AArch64.
-/

public import Kraken.AArch64.Semantics
import Kraken.Attribute
public import Kraken.OmniSemantics

@[expose] public section

theorem AddrExpr.checkSPAlignment_mono (mem : AddrExpr) (s : MachineData)
    {k₁ k₂ : Unit → Effects} {Q₁ Q₂ : MachineState → Prop}
    (hk : ∀ u, (k₁ u).All Q₁ → (k₂ u).All Q₂) :
    (mem.checkSPAlignment s k₁).All Q₁ → (mem.checkSPAlignment s k₂).All Q₂ := by
  unfold AddrExpr.checkSPAlignment
  split
  · split
    · exact False.elim
    · exact hk ()
  · exact hk ()

theorem AddrExpr.interpLoad_mono [Labels] {w : Width} (mem : AddrExpr)
    (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : w.type → MachineData → Effects} {Q₁ Q₂ : MachineState → Prop}
    (hk : ∀ v s', (k₁ v s').All Q₁ → (k₂ v s').All Q₂) :
    (mem.interpLoad s p k₁).All Q₁ → (mem.interpLoad s p k₂).All Q₂ := by
  unfold AddrExpr.interpLoad
  exact AddrExpr.checkSPAlignment_mono mem s fun _ =>
    MachineData.load_mono _ _ w hk

theorem AddrExpr.interpStore_mono [Labels] {w : Width} (mem : AddrExpr)
    (s : MachineData) (p : Std.Rco Int64) (val : w.type)
    {k₁ k₂ : MachineData → Effects} {Q₁ Q₂ : MachineState → Prop}
    (hk : ∀ s', (k₁ s').All Q₁ → (k₂ s').All Q₂) :
    (mem.interpStore s p val k₁).All Q₁ → (mem.interpStore s p val k₂).All Q₂ := by
  unfold AddrExpr.interpStore
  exact AddrExpr.checkSPAlignment_mono mem s fun _ =>
    MachineData.store_mono _ _ val hk

theorem UnscaledAddrExpr.checkSPAlignment_mono (mem : UnscaledAddrExpr) (s : MachineData)
    {k₁ k₂ : Unit → Effects} {Q₁ Q₂ : MachineState → Prop}
    (hk : ∀ u, (k₁ u).All Q₁ → (k₂ u).All Q₂) :
    (mem.checkSPAlignment s k₁).All Q₁ → (mem.checkSPAlignment s k₂).All Q₂ := by
  unfold UnscaledAddrExpr.checkSPAlignment
  split
  · split
    · exact False.elim
    · exact hk ()
  · exact hk ()

theorem UnscaledAddrExpr.interpLoad_mono [Labels] {w : Width} (mem : UnscaledAddrExpr)
    (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : w.type → MachineData → Effects} {Q₁ Q₂ : MachineState → Prop}
    (hk : ∀ v s', (k₁ v s').All Q₁ → (k₂ v s').All Q₂) :
    (mem.interpLoad s p k₁).All Q₁ → (mem.interpLoad s p k₂).All Q₂ := by
  unfold UnscaledAddrExpr.interpLoad
  exact UnscaledAddrExpr.checkSPAlignment_mono mem s fun _ =>
    MachineData.load_mono _ _ w hk

theorem UnscaledAddrExpr.interpStore_mono [Labels] {w : Width} (mem : UnscaledAddrExpr)
    (s : MachineData) (p : Std.Rco Int64) (val : w.type)
    {k₁ k₂ : MachineData → Effects} {Q₁ Q₂ : MachineState → Prop}
    (hk : ∀ s', (k₁ s').All Q₁ → (k₂ s').All Q₂) :
    (mem.interpStore s p val k₁).All Q₁ → (mem.interpStore s p val k₂).All Q₂ := by
  unfold UnscaledAddrExpr.interpStore
  exact UnscaledAddrExpr.checkSPAlignment_mono mem s fun _ =>
    MachineData.store_mono _ _ val hk

theorem Literal.interpLoad_mono [Labels] {w : Width} (expr : Literal)
    (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : w.type → MachineData → Effects} {Q₁ Q₂ : MachineState → Prop}
    (hk : ∀ v s', (k₁ v s').All Q₁ → (k₂ v s').All Q₂) :
    (expr.interpLoad s p k₁).All Q₁ → (expr.interpLoad s p k₂).All Q₂ := by
  unfold Literal.interpLoad
  split
  · exact MachineData.load_mono _ _ w hk
  · exact hk _ _

theorem AddrOrLit.interpLoad_mono [Labels] {w : Width} (expr : AddrOrLit)
    (s : MachineData) (p : Std.Rco Int64)
    {k₁ k₂ : w.type → MachineData → Effects} {Q₁ Q₂ : MachineState → Prop}
    (hk : ∀ v s', (k₁ v s').All Q₁ → (k₂ v s').All Q₂) :
    (expr.interpLoad s p k₁).All Q₁ → (expr.interpLoad s p k₂).All Q₂ := by
  unfold AddrOrLit.interpLoad
  split
  · exact AddrExpr.interpLoad_mono _ s p hk
  · exact Literal.interpLoad_mono _ s p hk

theorem MachineData.setRegOrSp_mono (s : MachineData) {w} (r : RegOrSp w) (v : w.type)
    {k₁ k₂ : MachineData → Effects} {Q₁ Q₂ : MachineState → Prop}
    (hk : ∀ s', (k₁ s').All Q₁ → (k₂ s').All Q₂) :
    (s.setRegOrSp r v k₁).All Q₁ → (s.setRegOrSp r v k₂).All Q₂ :=
  hk _

theorem MachineData.setRegOrZr_mono (s : MachineData) {w} (r : RegOrZr w) (v : w.type)
    {k₁ k₂ : MachineData → Effects} {Q₁ Q₂ : MachineState → Prop}
    (hk : ∀ s', (k₁ s').All Q₁ → (k₂ s').All Q₂) :
    (s.setRegOrZr r v k₁).All Q₁ → (s.setRegOrZr r v k₂).All Q₂ :=
  hk _

set_option maxHeartbeats 2000000 in
theorem Operation.interp_mono [Labels] {w} (op : Operation w) (p : Std.Rco Int64) (s : MachineData)
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
      | apply AddrOrLit.interpLoad_mono; intro _ _
      | apply AddrExpr.interpLoad_mono; intro _ _
      | apply AddrExpr.interpStore_mono; intro _
      | apply AddrExpr.checkSPAlignment_mono; intro _
      | apply UnscaledAddrExpr.interpLoad_mono; intro _ _
      | apply UnscaledAddrExpr.interpStore_mono; intro _
      | apply UnscaledAddrExpr.checkSPAlignment_mono; intro _
      | apply MachineData.load_mono; intro _ _
      | apply MachineData.store_mono; intro _
      | apply MachineData.setRegOrSp_mono; intro _
      | apply MachineData.setRegOrZr_mono; intro _
      | split

theorem Instr.interp_mono [Labels] (i : Instr) (s : MachineData) (p : Std.Rco Int64)
    {P Q : MachineState → Prop} {next₁ next₂ : MachineData → Effects} {jmp₁ jmp₂ : Int64 → MachineData → Effects}
    (hnext : ∀ s', (next₁ s').All P → (next₂ s').All Q)
    (hjmp : ∀ a s', (jmp₁ a s').All P → (jmp₂ a s').All Q) :
    (i.interp s p next₁ jmp₁).All P → (i.interp s p next₂ jmp₂).All Q := by
  unfold Instr.interp
  dsimp only [Kraken.Effects.All]
  exact Operation.interp_mono i.operation p s hnext hjmp

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
