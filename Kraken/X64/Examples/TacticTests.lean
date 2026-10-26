module

/-
Regression tests for `kcall` (plain and constant-time/traced composition) on x86-64 examples.
-/

import all Kraken.X64.Examples.Examples
import Kraken.Tactics

open Kraken Kraken.X64
open Kraken.X64.Parser


-- untraced composition (was: refine (…).bind_at (by kaddr …) ?_; rintro ⟨s₂, _⟩ ⟨h_rax₂, h_dmem₂⟩)
theorem swap_and_add_correct' [layout : Layout] [Layout.Valid swap_and_add] (s₀ : MachineData)
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
  kcall swap_and_add_finish_spec s₁ with s₂ ⟨h_rax₂, h_dmem₂⟩
  apply Eventually.done
  exact ⟨by grind, h_dmem₂ ▸ h_mem₁⟩

-- traced composition
theorem swap_and_add_ct_correct' [layout : Layout] [Layout.Valid swap_and_add] (x_ptr y_ptr : BitVec 64) :
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
  kcall swap_and_add_finish_ct_spec.choose_spec s₁ with s₂ ⟨h_rax₂, h_dmem₂⟩
  kdone
  exact ⟨by grind, h_dmem₂ ▸ h_mem₁⟩

