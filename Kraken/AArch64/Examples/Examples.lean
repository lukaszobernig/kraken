module

/-
Kraken AArch64 - Example Programs

Demonstrates AArch64 proofs using the `kstep` stepping tactic.
-/

import Kraken.AArch64.OmniSemantics
import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.Eval
import Kraken.SeparationMem
import Kraken.SeparationTactics
import Kraken.Tactics


open Kraken.AArch64
open Kraken.AArch64.Parser

--------------------------------------------------------------------------------

-- Register swap example using XOR
def swap : Program := parseAArch64("
  eor x0, x0, x1
  eor x1, x0, x1
  eor x0, x0, x1")

theorem swap_correct [layout : Layout] [Layout.Valid swap] (d : MachineData) :
    (layout swap).Spec d
      (post := fun st =>
        st.data.regs.getRegOrZr .X0 = d.regs.getRegOrZr .X1 ∧
        st.data.regs.getRegOrZr .X1 = d.regs.getRegOrZr .X0) := by
  kprologue swap with d
  sym => kstep; tactic =>
  apply Eventually.done
  grind

-- Example 3: Multi-instruction arithmetic and shift pipeline
def arith_shift : Program := parseAArch64("
  add x0, x1, #42
  lsl x2, x0, #2
  sub x3, x2, x0
")

theorem arith_shift_correct [layout : Layout] [Layout.Valid arith_shift] (d : MachineData) :
    (layout arith_shift).Spec d
      (post := fun st =>
        st.data.regs.getRegOrZr .X3 = 3 * (d.regs.getRegOrZr .X1 + 42)) := by
  kprologue arith_shift with d
  sym => kstep; tactic =>
  apply Eventually.done
  simp (config := { zetaDelta := true }) only
  grind

-- Example 4: Stepping through control flow (branch not taken)
def controlflow : Program := parseAArch64("
start:
  mov x0, #1
  eor x0, x0, x0
  cbnz x0, start
  mov x1, #42
")

theorem p4_correct [layout : Layout] [Layout.Valid controlflow] (d : MachineData) :
    (layout controlflow).Spec d (post := fun st => st.data.regs.X1 = 42) := by
  kprologue controlflow with d
  sym => kstep; tactic =>
  apply Eventually.done
  rfl

-- Example 5: Storing and loading registers to/from memory
open Std
open Std.ExtHashMap

def move_2_regs_to_heap : Program := parseAArch64("
    str x0, [x2]
    str x1, [x2, #8]
    ldr x3, [x2]
    ldr x4, [x2, #8]
")

theorem move_2_regs_to_heap_correct [layout : Layout] [Layout.Valid move_2_regs_to_heap] (s₀ : MachineData)
    (v1 v2 : UInt64) (R : DataMem → Prop) :
    (layout move_2_regs_to_heap).Spec s₀
      (pre :=
        s₀.dmem =⋆ v1 @ s₀.regs.X2 ⋆ v2 @ s₀.regs.X2 + 8 ⋆ R)
      (post := fun st =>
        st.data.regs.X3 = s₀.regs.X0 ∧
        st.data.regs.X4 = s₀.regs.X1 ∧
        st.data.regs.X2 = s₀.regs.X2) := by
  kprologue move_2_regs_to_heap with s₀
  sym => kstep; tactic =>
  apply Eventually.done
  exact ⟨rfl, rfl, rfl⟩

-- Example 6: Memory access with shifted register offset [x1, x2, lsl #3]
def reg_offset_example : Program := parseAArch64("
    mov x0, #42
    str x0, [x1, x2, lsl #3]
    mov x0, #0
    ldr x3, [x1, x2, lsl #3]
")

theorem reg_offset_example_correct [layout : Layout] [Layout.Valid reg_offset_example] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop) :
    (layout reg_offset_example).Spec s₀
      (pre :=
        s₀.dmem =⋆ v @ s₀.regs.X1.toBitVec + BitVec.ofInt 64 (s₀.regs.X2.toBitVec.toNat <<< 3) ⋆ R)
      (post := fun st => st.data.regs.X3 = 42) := by
  kprologue reg_offset_example with s₀
  sym => kstep; tactic =>
  apply Eventually.done
  rfl
