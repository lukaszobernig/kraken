module

/-
Standard System V AMD64 ABI `memcpy(dst, src, n)` verification.
-/

import Kraken.SeparationMem
import Kraken.SeparationTactics
import Kraken.Tactics
import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import Kraken.X64.Semantics

open Kraken.X64.Parser
open Std
open Std.ExtHashMap

-- Standard System V AMD64 ABI `memcpy(dst, src, n)`
-- Arguments: %rdi = dst, %rsi = src, %rdx = n, (%rsp) = return address `ra`
-- Returns: %rax = dst, %rsp = rsp₀ + 8, pc = ra, callee-saved registers preserved,
--          and `src` bytes copied into `dst`.
def memcpy : Program := parse("
memcpy:
  movq %rdi, %rax
  subq $0, %rdx
  jz done
loop:
  movb (%rsi), %cl
  movb %cl, (%rdi)
  addq $1, %rsi
  addq $1, %rdi
  subq $1, %rdx
  jnz loop
done:
  ret
")

theorem memcpy_correct [layout : Layout] [Layout.Valid memcpy] (s₀ : MachineData)
    (n : Nat) (ra : UInt64) (dst src : List UInt8) (R : DataMem → Prop) :
    (layout memcpy).Spec s₀
      (pre :=
        s₀.regs.rdx.toNat = n ∧
        dst.length = n ∧
        src.length = n ∧
        (s₀.dmem =⋆ ra @ s₀.regs.rsp ⋆ dst @ s₀.regs.rdi ⋆ src @ s₀.regs.rsi ⋆ R))
      (post := fun st =>
        st.pc = Int64.ofBitVec ra.toBitVec ∧
        st.data.regs.rax = s₀.regs.rdi ∧
        st.data.regs.rsp = s₀.regs.rsp + 8 ∧
        st.data.regs.CalleeSavedEq s₀.regs ∧
        (st.data.dmem =⋆ ra @ s₀.regs.rsp ⋆ src @ s₀.regs.rdi ⋆ src @ s₀.regs.rsi ⋆ R)) := by
  rintro ⟨h_rdx, h_dst_len, h_src_len, h_mem⟩
  apply tailrec_loop_cps (step1 (layout memcpy)) _ _
    (P := fun v (dst_ptr, src_ptr, dst_bs, src_bs, frame) st =>
      st.pc = (layout memcpy).label "loop" ∧
      0 < v ∧
      st.data.regs.rdx.toNat = v ∧
      st.data.regs.rdi.toBitVec = dst_ptr ∧
      st.data.regs.rsi.toBitVec = src_ptr ∧
      st.data.regs.rax = s₀.regs.rdi ∧
      st.data.regs.rsp = s₀.regs.rsp ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      dst_bs.length = v ∧
      src_bs.length = v ∧
      (st.data.dmem =⋆ dst_bs @ dst_ptr ⋆ src_bs @ src_ptr ⋆ frame))
    (Q := fun _ (dst_ptr, src_ptr, _, src_bs, frame) st =>
      st.pc = (layout memcpy).label "done" ∧
      st.data.regs.rax = s₀.regs.rdi ∧
      st.data.regs.rsp = s₀.regs.rsp ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      (st.data.dmem =⋆ src_bs @ dst_ptr ⋆ src_bs @ src_ptr ⋆ frame))
    (lt := (· < ·))
    (Hwf := Nat.lt_wfRel.wf)
    (v0 := n)
    (g0 := (s₀.regs.rdi.toBitVec, s₀.regs.rsi.toBitVec, dst, src, ra @ s₀.regs.rsp ⋆ R))
  · kprologue memcpy to "loop"
    by_cases hn : n = 0
    · sym => kstep; tactic =>
      subst hn
      obtain rfl := List.eq_nil_of_length_eq_zero h_dst_len
      obtain rfl := List.eq_nil_of_length_eq_zero h_src_len
      apply Eventually.done
      exact Or.inl ⟨by kaddr memcpy, rfl, rfl, Reg64s.CalleeSavedEq_refl _, by ecancel⟩
    · sym => kstep; tactic =>
      apply Eventually.done
      exact Or.inr ⟨by kaddr memcpy, by omega, by grind, rfl, rfl, rfl, rfl, Reg64s.CalleeSavedEq_refl _, h_dst_len, h_src_len, by ecancel⟩
  · rintro v ⟨dst_ptr, src_ptr, dst_bs, src_bs, frame⟩ ⟨s, pc⟩
      ⟨rfl, hv, h_rdx_v, rfl, rfl, h_rax, h_rsp, h_cs, h_dst_v, h_src_v, h_mem_v⟩
    by_cases hv1 : v = 1
    · subst hv1
      kprologue memcpy at "loop" to "done" with s
      sym => kstep; tactic =>
      apply Eventually.done
      exact Or.inl ⟨by kaddr memcpy, h_rax, h_rsp, h_cs, by ecancel⟩
    · kprologue memcpy at "loop" to "done" with s
      rw [Mem.At_take_drop_sep dst_bs 1 rdi.toBitVec (by omega) (by grind),
          Mem.At_take_drop_sep src_bs 1 rsi.toBitVec (by omega) (by grind)] at h_mem_v
      sym => kstep; tactic =>
      apply Eventually.done
      refine Or.inr ⟨v - 1, (rdi.toBitVec + 1#64, rsi.toBitVec + 1#64, dst_bs.drop 1, src_bs.drop 1,
        (src_bs.take 1) @ rdi ⋆ (src_bs.take 1) @ rsi ⋆ frame),
        ⟨by kaddr memcpy, by grind, by grind, by grind, by grind, h_rax, h_rsp, h_cs,
         by simp [h_dst_v], by simp [h_src_v], by ecancel⟩,
        by omega, ?_⟩
      rintro t_s ⟨hQ_pc, hQ_rax, hQ_rsp, hQ_cs, hQ_mem⟩
      refine ⟨hQ_pc, hQ_rax, hQ_rsp, hQ_cs, ?_⟩
      rw [Mem.At_take_drop_sep src_bs 1 rdi.toBitVec (by omega) (by grind),
          Mem.At_take_drop_sep src_bs 1 rsi.toBitVec (by omega) (by grind)]
      ecancel
  · rintro ⟨st, pc⟩ ⟨rfl, h_rax, h_rsp, h_cs, h_mem_q⟩
    kprologue memcpy at "done" with st
    sym => kstep; tactic =>
    apply Eventually.done
    exact ⟨rfl, h_rax, by grind, h_cs, by ecancel⟩
