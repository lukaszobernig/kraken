module

/-
Kraken - Example Programs

This demonstrates our proof style using the `kstep` stepping tactic that
advances through ASM instructions. This is a work in progress, and is the result
of several experiments, which can be found in the Git history at revision
a556993a and earlier.

For semantics, see Kraken/Semantics.lean.
For tactics, see Kraken/Tactics.lean.
-/

import Kraken.Eval
import Kraken.SeparationMem
import Kraken.SeparationTactics
import Kraken.Tactics
import Std.Tactic.BVDecide
import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import Kraken.X64.PrettyPrint
import Kraken.X64.Semantics

open Kraken.X64.Parser

--------------------------------------------------------------------------------

def p1 := parse("start: mov $1, %rax")

-- Super-simple example to debug tactics
example [layout : Layout] [Layout.Valid p1] (s : MachineData) :
    (layout p1).Spec s (post := fun st => st.data.regs.rax = 1) := by
  kprologue p1 with s
  sym => kstep; tactic =>
  apply Eventually.done
  rfl

def swap : Program := parse("
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax")

theorem swap_correct [layout : Layout] [Layout.Valid swap] (d : MachineData) :
    (layout swap).Spec d
      (post := fun st =>
        st.data.regs.get Reg.rax = d.regs.get Reg.rbx ∧
        st.data.regs.get Reg.rbx = d.regs.get Reg.rax) := by
  kprologue swap with d
  sym => kstep; tactic =>
  apply Eventually.done
  grind

-- Stepping demo. Ideally, this demo should be without the first .mov
def p2 : Program := parse("
start:
  mov $1, %rax
  xor %rax, %rax
  jnz start
  mov $2, %rax")

-- Example 2: stepping through both straightline and control instructions
example [layout : Layout] [Layout.Valid p2] (s : MachineData) :
    (layout p2).Spec s (post := fun st => st.data.regs.rax = 2) := by
  kprologue p2 with s
  sym => kstep; tactic =>
  apply Eventually.done
  rfl

-- Example 3, more sophisticated

def p3: Program := parse("
init:
  mov $2, %rdx             # rdx: current result = 2
start:
  sub $0, %rbx             # TEST: zf = (rbx == 0)
  jz _end                 # end loop if rbx == 0 (a.k.a. « while rbx >= 0 »)
  mulx %rdx, %rdx, %rax    # BODY: rdx := rdx * rdx
  sub $1, %rbx              # rbx -= 1
  jmp start               # go back to test & loop body
_end:
  nop
")

def p3_spec (s: MachineData): Nat := 2^(2^s.regs.rbx.toNat)

theorem p3_correct [layout: Layout] [Layout.Valid p3] (s: MachineData):
    (layout p3).Spec s
      (pre := p3_spec s < 2^64)
      (post := fun st =>
        st.data.regs.rdx.toNat = p3_spec s ∧ (0 < s.regs.rbx.toNat → st.data.regs.rax = 0)) := by
  intro h_bounds
  unfold p3_spec at *
  kprologue p3 to "start"
  sym => kstep; tactic =>
  apply reg_dec_loop (step1 (layout p3)) _ _
    (fun i st =>
      st.pc = (layout p3).label "start" ∧
      st.data.regs.rbx.toNat = i ∧
      i ≤ s.regs.rbx.toNat ∧
      st.data.regs.rdx.toNat = 2 ^ (2 ^ (s.regs.rbx.toNat - i)) ∧
      (i < s.regs.rbx.toNat → st.data.regs.rax = 0))
    s.regs.rbx.toNat
  refine ⟨⟨by kaddr p3, rfl, Nat.le_refl _, by simp; decide, fun h => absurd h (Nat.lt_irrefl _)⟩, ?_, ?_⟩
  · rintro ⟨state, pc⟩ ⟨rfl, h_rbx_zero, h_rbx_le, h_inv, h_rax⟩
    kprologue p3 at "start" with state
    sym => kstep; tactic =>
    kprologue p3 at "_end"
    sym => kstep; tactic =>
    apply Eventually.done
    exact ⟨by dsimp; rw [h_inv, Nat.sub_zero], fun h_pos => h_rax h_pos⟩
  · rintro ⟨state, pc⟩ k hk_nz ⟨rfl, h_rbx_k, h_k_le, h_inv, _⟩
    kprologue p3 at "start" to "_end" with state
    sym => kstep; tactic =>
    rename_i b_mul v_mul _ _ _ _
    apply Eventually.done
    have h_pow_eq : rdx.toNat * rdx.toNat = 2 ^ 2 ^ (s.regs.rbx.toNat - (k - 1)) := by
      rw [h_inv, show s.regs.rbx.toNat - (k - 1) = (s.regs.rbx.toNat - k) + 1 by omega]
      rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ]
    have h_prod_lt : rdx.toNat * rdx.toNat < 2 ^ 64 := by
      rw [h_pow_eq]
      refine Nat.lt_of_le_of_lt ?_ h_bounds
      apply Nat.pow_le_pow_right (by decide)
      apply Nat.pow_le_pow_right (by decide)
      omega
    have hv_mul : v_mul = ↑(rdx.toNat * rdx.toNat) := by
      dsimp [v_mul, b_mul, BitVec.unsigned]
      grind
    dsimp only
    refine ⟨by kaddr p3, by grind, by omega, ?_, ?_⟩
    · rw [hv_mul, ← h_pow_eq]
      change (BitVec.ofNat 64 (rdx.toNat * rdx.toNat)).toNat = rdx.toNat * rdx.toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_prod_lt]
    · intro _
      rw [hv_mul]
      change ({ toBitVec := BitVec.ofNat 64 ((rdx.toNat * rdx.toNat) >>> 64) } : UInt64) = 0
      have h_shr : (rdx.toNat * rdx.toNat) >>> 64 = 0 :=
        Nat.shiftRight_eq_div_pow _ _ ▸ Nat.div_eq_of_lt h_prod_lt
      rw [h_shr]
      rfl

def p4 := eval% parse("start: mov $2, %rax
dec %rax")

-- Super-simple example to debug tactics
example [layout : Layout] [Layout.Valid p4] (s : MachineData) :
    (layout p4).Spec s (post := fun st => st.data.regs.rax = 1) := by
  kprologue p4 with s
  sym => kstep; tactic =>
  apply Eventually.done
  rfl

/- Examples -/

def p5 := parse("start: mov $2, %rax
dec %rax
start2:
dec %rax")

example [layout : Layout] [Layout.Valid p5] (s : MachineData) :
    (layout p5).Spec s (post := fun st => st.data.regs.rax = 0) := by
  kprologue p5 with s
  sym => kstep; tactic =>
  apply Eventually.done
  dsimp; bv_decide

def p6 := parse("push %rax
mov $0, %rax
pop %rax")

theorem p6_correct [layout : Layout] [Layout.Valid p6] (s₀ : MachineData)
    (stack : List UInt8) (R : DataMem → Prop) :
    (layout p6).Spec s₀
      (pre :=
        stack.length = 8 ∧
        (s₀.dmem =⋆ stack @ s₀.regs.rsp - 8 ⋆ R))
      (post := fun st =>
        st.data.regs.rax = s₀.regs.rax ∧ st.data.regs.rsp = s₀.regs.rsp) := by
  kprologue p6 with s₀
  sym => kstep; tactic =>
  apply Eventually.done
  simp (config := { zetaDelta := true }) only [show (OfNat.ofNat 8 : UInt64) = 8 from rfl]
  bv_decide


open Std
open Std.ExtHashMap

def move_2_regs_to_heap := parse("
    movq %rax, (%rdi)
    movq %rcx, 8(%rdi)
    movq (%rdi), %r12
    movq 8(%rdi), %r13
")

theorem move_2_regs_to_heap_correct [layout : Layout] [Layout.Valid move_2_regs_to_heap] (s₀ : MachineData)
    (v1 v2 : UInt64) (R : DataMem → Prop) :
    (layout move_2_regs_to_heap).Spec s₀
      (pre :=
        s₀.dmem =⋆ v1 @ s₀.regs.rdi ⋆ v2 @ s₀.regs.rdi + 8 ⋆ R)
      (post := fun st =>
        st.data.regs.r12 = s₀.regs.rax ∧
        st.data.regs.r13 = s₀.regs.rcx ∧
        st.data.regs.rdi = s₀.regs.rdi) := by
  kprologue move_2_regs_to_heap with s₀
  sym => kstep; tactic =>
  apply Eventually.done
  exact ⟨rfl, rfl, rfl⟩

def sib_example := parse("
    movq $42, %rax
    movq %rax, (%rdi, %r15, 8)
    movq $0, %rax
    movq (%rdi, %r15, 8), %rax
")

theorem sib_example_correct [layout : Layout] [Layout.Valid sib_example] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop) :
    (layout sib_example).Spec s₀
      (pre :=
        s₀.dmem =⋆ v @ s₀.regs.rdi + s₀.regs.r15 * 8 ⋆ R)
      (post := fun st => st.data.regs.rax = 42) := by
  kprologue sib_example with s₀
  sym => kstep; tactic =>
  apply Eventually.done
  rfl

def alu_mem_example := parse("
    movq $42, %rax
    movq %rax, 136(%rdx)
    movq $100, %rcx
    addq 136(%rdx), %rcx
")

theorem alu_mem_example_correct [layout : Layout] [Layout.Valid alu_mem_example] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop) :
    (layout alu_mem_example).Spec s₀
      (pre :=
        s₀.dmem =⋆ v @ s₀.regs.rdx + 136 ⋆ R)
      (post := fun st => st.data.regs.rcx = 142) := by
  kprologue alu_mem_example with s₀
  sym => kstep; tactic =>
  apply Eventually.done
  rfl

def dynamic_stack_example := parse("
    movq $99, -8(%rsp)
    movq %rsp, %rbp
    leaq -1024(%rsp, %r9, 8), %rsp
    movq $42, %rax
    movq %rax, 16(%rsp, %r15, 8)
    movq $0, %rax
    movq 16(%rsp, %r15, 8), %rax
    movq %rbp, %rsp
    movq -8(%rsp), %rbx
")

theorem dynamic_stack_example_correct [layout : Layout] [Layout.Valid dynamic_stack_example] (s₀ : MachineData)
    (stack : List UInt8) (R : DataMem → Prop) :
    (layout dynamic_stack_example).Spec s₀
      (pre :=
        stack.length = 1024 ∧
        s₀.regs.r9.toNat + s₀.regs.r15.toNat < 125 ∧
        (s₀.dmem =⋆ stack @ s₀.regs.rsp - 1024 ⋆ R))
      (post := fun st =>
        st.data.regs.rax = 42 ∧ st.data.regs.rbx = 99 ∧ st.data.regs.rsp = s₀.regs.rsp) := by
  rintro ⟨lstack, h, h_mem⟩
  kprologue dynamic_stack_example with s₀
  rw [Mem.At_take_drop_sep stack 1016 _ (by omega) (by omega)] at h_mem
  rw [Mem.At_slice_sep (stack.take 1016) ((r9.toNat + r15.toNat) * 8 + 16) 8 _
    (by simp [lstack]; omega) (by simp [lstack])] at h_mem
  sym => kstep; tactic =>
  apply Eventually.done
  exact ⟨rfl, rfl, rfl⟩

-- Example 10: Loop zeroing an array of 64-bit words in memory using `tailrec_loop`
def memset_loop : Program := parse("
loop:
  movq $0, (%rdi)
  addq $8, %rdi
  subq $1, %rcx
  jnz loop
")

theorem memset_loop_correct [layout : Layout] [Layout.Valid memset_loop] (s₀ : MachineData)
    (n : Nat) (buf : List UInt8) (R : DataMem → Prop) :
    (layout memset_loop).Spec s₀
      (pre :=
        0 < n ∧
        s₀.regs.rcx.toNat = n ∧
        buf.length = 8 * n ∧
        buf.length ≤ 2 ^ 64 ∧
        (s₀.dmem =⋆ buf @ s₀.regs.rdi ⋆ R))
      (post := fun st =>
        st.data.regs.rcx = 0 ∧
        st.data.regs.rdi.toBitVec = s₀.regs.rdi.toBitVec + BitVec.ofNat 64 (8 * n) ∧
        (st.data.dmem =⋆ (List.replicate (8 * n) 0) @ s₀.regs.rdi ⋆ R)) := by
  rintro ⟨hn, h_rcx, h_len, h_bound, h_mem⟩
  apply tailrec_loop (step1 (layout memset_loop)) _ ⟨s₀, layout.start⟩
    (P := fun v (ptr, bs, frame) st =>
      st.pc = layout.start ∧
      0 < v ∧
      st.data.regs.rcx.toNat = v ∧
      st.data.regs.rdi.toBitVec = ptr ∧
      bs.length = 8 * v ∧
      bs.length ≤ 2 ^ 64 ∧
      (st.data.dmem =⋆ bs @ ptr ⋆ frame))
    (Q := fun v (ptr, _, frame) st =>
      st.data.regs.rcx = 0 ∧
      st.data.regs.rdi.toBitVec = ptr + BitVec.ofNat 64 (8 * v) ∧
      (st.data.dmem =⋆ (List.replicate (8 * v) 0) @ ptr ⋆ frame))
    (lt := (· < ·))
    (Hwf := Nat.lt_wfRel.wf)
    (v0 := n)
    (g0 := (s₀.regs.rdi.toBitVec, buf, R))
  · exact ⟨rfl, hn, h_rcx, rfl, h_len, h_bound, h_mem⟩
  · rintro v ⟨ptr, bs, frame⟩ ⟨s, pc⟩ ⟨rfl, hv, h_rcx, rfl, h_bs_len, h_bs_bound, h_mem⟩
    by_cases hv1 : v = 1
    · subst hv1
      kprologue memset_loop with s
      sym => kstep; tactic =>
      apply Eventually.done
      exact Or.inl ⟨by grind, by grind, by ecancel⟩
    · kprologue memset_loop with s
      rw [Mem.At_take_drop_sep bs 8 rdi.toBitVec (by omega) h_bs_bound] at h_mem
      sym => kstep; tactic =>
      apply Eventually.done
      refine Or.inr ⟨v - 1, rdi.toBitVec + 8#64, bs.drop 8,
        (List.replicate 8 0) @ rdi ⋆ frame,
        ⟨rfl, by grind, by grind, by grind, by simp [h_bs_len]; omega, by simp; omega, by ecancel⟩,
        by omega, ?_⟩
      intro t_s hQ_rcx hQ_rdi hQ_mem
      refine ⟨hQ_rcx, by grind, ?_⟩
      rw [Mem.At_take_drop_sep _ 8 _ (by simp; omega) (by simp; omega)]
      ecancel
  · intro st hQ
    exact hQ

-- Example 11: Composable basic blocks (both standalone subprograms and per-block lemmas)

-- A standalone basic block that swaps two 64-bit words in memory at (%rdi) and (%rsi)
def swap_mem_block : Program := parse("
  movq (%rdi), %rax
  movq (%rsi), %rcx
  movq %rcx, (%rdi)
  movq %rax, (%rsi)
")

-- Verified once for any `[layout : Layout]` and `[Labels]` using `Executable.ExecSpec`
theorem swap_mem_block_spec [layout : Layout] [Labels] (s₀ : MachineData)
    (x y : UInt64) (R : DataMem → Prop) :
    (layout swap_mem_block).ExecSpec s₀
      (pre :=
        s₀.dmem =⋆ x @ s₀.regs.rdi ⋆ y @ s₀.regs.rsi ⋆ R)
      (post := fun st =>
        st.pc = (layout swap_mem_block).addrOf swap_mem_block.length ∧
        st.data.regs.rax = x.toBitVec ∧
        st.data.regs.rcx = y.toBitVec ∧
        st.data.regs.rdi = s₀.regs.rdi ∧
        st.data.regs.rsi = s₀.regs.rsi ∧
        (st.data.dmem =⋆ y @ s₀.regs.rdi ⋆ x @ s₀.regs.rsi ⋆ R)) := by
  kprologue swap_mem_block with s₀
  sym => kstep; tactic =>
  refine ⟨by kaddr swap_mem_block, by grind, by grind, trivial, trivial, by ecancel⟩

-- A larger program that embeds `swap_mem_block` and follows it with a second basic block `finish:`
def swap_and_add : Program := parse("
  movq (%rdi), %rax
  movq (%rsi), %rcx
  movq %rcx, (%rdi)
  movq %rax, (%rsi)
finish:
  addq %rcx, %rax
")

-- Separate basic-block lemma for the `finish:` block within `swap_and_add`
theorem swap_and_add_finish_spec [layout : Layout] [Layout.Valid swap_and_add] (s : MachineData) :
    (layout swap_and_add).Spec s
      (pc := (layout swap_and_add).label "finish")
      (post := fun st =>
        st.data.regs.rax = s.regs.rax + s.regs.rcx ∧
        st.data.dmem = s.dmem) := by
  kprologue swap_and_add at "finish" with s
  sym => kstep; tactic =>
  apply Eventually.done
  exact ⟨by grind, rfl⟩

-- Composing the standalone `swap_mem_block_spec` (`step1_subprog`) with `swap_and_add_finish_spec` (`Spec.bind_at`)
theorem swap_and_add_correct [layout : Layout] [Layout.Valid swap_and_add] (s₀ : MachineData)
    (x y : UInt64) (R : DataMem → Prop) :
    (layout swap_and_add).Spec s₀
      (pre :=
        s₀.dmem =⋆ x @ s₀.regs.rdi ⋆ y @ s₀.regs.rsi ⋆ R)
      (post := fun st =>
        st.data.regs.rax = x.toBitVec + y.toBitVec ∧
        (st.data.dmem =⋆ y @ s₀.regs.rdi ⋆ x @ s₀.regs.rsi ⋆ R)) := by
  intro h_mem
  refine step1_subprog 0 (swap_mem_block_spec s₀ x y R) h_mem (by rfl) (by kaddr swap_and_add) ?_
  rintro s₁ ⟨h_rax, h_rcx, -, -, h_mem₁⟩
  refine (swap_and_add_finish_spec s₁).bind_at (by kaddr swap_and_add) ?_
  rintro ⟨s₂, _⟩ ⟨h_rax₂, h_dmem₂⟩
  apply Eventually.done
  exact ⟨by grind, h_dmem₂ ▸ h_mem₁⟩

-- Constant-time specification for `swap_mem_block` using `ExecSpec (trace := some tr)`
theorem swap_mem_block_ct_spec [layout : Layout] [Labels] (x_ptr y_ptr : BitVec 64) :
    ∃ tr, ∀ (s₀ : MachineData) (x y : UInt64) (R : DataMem → Prop),
      (layout swap_mem_block).ExecSpec s₀
        (trace := some tr)
        (pre :=
          s₀.regs.rdi = x_ptr ∧ s₀.regs.rsi = y_ptr ∧
          (s₀.dmem =⋆ x @ x_ptr ⋆ y @ y_ptr ⋆ R))
        (post := fun st =>
          st.pc = (layout swap_mem_block).addrOf swap_mem_block.length ∧
          st.data.regs.rax = x.toBitVec ∧
          st.data.regs.rcx = y.toBitVec ∧
          st.data.regs.rdi = x_ptr ∧
          st.data.regs.rsi = y_ptr ∧
          (st.data.dmem =⋆ y @ x_ptr ⋆ x @ y_ptr ⋆ R)) := by
  kintro s₀ x y R
  kprologue swap_mem_block with s₀
  kstep
  kdone
  refine ⟨by kaddr swap_mem_block, by grind, by grind, by assumption, by assumption, by ecancel⟩

-- Constant-time specification for the `finish:` block within `swap_and_add`
theorem swap_and_add_finish_ct_spec [layout : Layout] [Layout.Valid swap_and_add] :
    ∃ tr, ∀ (s : MachineData),
      (layout swap_and_add).Spec s
        (pc := (layout swap_and_add).label "finish")
        (trace := some tr)
        (post := fun st =>
          st.data.regs.rax = s.regs.rax + s.regs.rcx ∧
          st.data.dmem = s.dmem) := by
  kintro s
  kprologue swap_and_add at "finish" with s
  kstep
  kdone
  exact ⟨by grind, rfl⟩

-- Composing `swap_mem_block_ct_spec` (`step1_subprog_traced`) with `swap_and_add_finish_ct_spec` (`Spec.bind_at_traced`)
theorem swap_and_add_ct_correct [layout : Layout] [Layout.Valid swap_and_add] (x_ptr y_ptr : BitVec 64) :
    ∃ tr, ∀ (s₀ : MachineData) (x y : UInt64) (R : DataMem → Prop),
      (layout swap_and_add).Spec s₀
        (trace := some tr)
        (pre :=
          s₀.regs.rdi = x_ptr ∧ s₀.regs.rsi = y_ptr ∧
          (s₀.dmem =⋆ x @ x_ptr ⋆ y @ y_ptr ⋆ R))
        (post := fun st =>
          st.data.regs.rax = x.toBitVec + y.toBitVec ∧
          (st.data.dmem =⋆ y @ x_ptr ⋆ x @ y_ptr ⋆ R)) := by
  kintro s₀ x y R ⟨h_rdi, h_rsi, h_mem⟩
  refine step1_subprog_traced 0 ((swap_mem_block_ct_spec x_ptr y_ptr).choose_spec s₀ x y R)
    ⟨h_rdi, h_rsi, h_mem⟩ (by rfl) (by kaddr swap_and_add) ?_
  rintro s₁ ⟨h_rax, h_rcx, -, -, h_mem₁⟩
  refine (swap_and_add_finish_ct_spec.choose_spec s₁).bind_at_traced (by kaddr swap_and_add) ?_
  rintro ⟨s₂, _⟩ ⟨h_rax₂, h_dmem₂⟩
  kdone
  exact ⟨by grind, h_dmem₂ ▸ h_mem₁⟩
