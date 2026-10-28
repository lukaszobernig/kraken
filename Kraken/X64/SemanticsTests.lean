module

import Kraken.X64.Semantics
meta import Kraken.X64.Semantics

/-!
# Semantics Shape and Evaluator Tests (x86-64)

Regression tests for the `grind`/`omega`/`simp`-friendliness of x86-64 flag projections,
condition codes, carry-chain limb identities, and the concrete evaluator.
-/

/-! ### Flag Projections (`@[kcond]`) and Condition Codes -/

example (a b : BitVec 64) : (StatusFlags.sub a b).cf = decide (a.toNat < b.toNat) := by simp
example (a b : BitVec 64) : (StatusFlags.sub a b).zf = decide (a = b) := by simp
example (a b : BitVec 64) : (StatusFlags.add a b).cf = decide (2 ^ 64 ≤ a.toNat + b.toNat) := by simp
example (a b : BitVec 64) (c : Bool) :
    (StatusFlags.adc a b c).cf = decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat) := by simp
example (a b : BitVec 64) (c : Bool) :
    (StatusFlags.sbb a b c).cf = decide (a.toNat < b.toNat + c.toNat) := by simp
example (a : BitVec 64) (cf : Bool) : (StatusFlags.dec a cf).zf = decide (a = 1#64) := by simp
example (a : BitVec 64) (cf : Bool) : (StatusFlags.dec a cf).cf = cf := by simp
example (v : BitVec 64) (af : Bool) : (StatusFlags.logical v af).zf = decide (v = 0#64) := by simp

-- Branch conditions after `cmp a, b` simplify directly to value-level comparisons.
example (a b : BitVec 64) : CondCode.interp .c (StatusFlags.sub a b) = decide (a.toNat < b.toNat) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .be (StatusFlags.sub a b) = decide (a.toNat ≤ b.toNat) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .a (StatusFlags.sub a b) = decide (b.toNat < a.toNat) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .l (StatusFlags.sub a b) = decide (a.toInt < b.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .ge (StatusFlags.sub a b) = decide (b.toInt ≤ a.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .g (StatusFlags.sub a b) = decide (b.toInt < a.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .le (StatusFlags.sub a b) = decide (a.toInt ≤ b.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .z (StatusFlags.sub a b) = decide (a = b) := by
  simp [CondCode.interp]

/-! ### Carry-Chain Limb Identities -/

example (a0 b0 a1 b1 : BitVec 64) (c : Bool) :
    ((a0 + b0 + BitVec.ofNat 64 c.toNat).toNat : Int) +
      2 ^ 64 * (a1 + b1 + BitVec.ofNat 64 ((StatusFlags.adc a0 b0 c).cf).toNat).toNat +
      2 ^ 128 * ((StatusFlags.adc a1 b1 (StatusFlags.adc a0 b0 c).cf).cf).toNat =
      a0.toNat + 2 ^ 64 * a1.toNat + (b0.toNat + 2 ^ 64 * b1.toNat) + c.toNat := by
  have h0 := StatusFlags.adc_toNat a0 b0 c (by decide)
  have h1 := StatusFlags.adc_toNat a1 b1 (StatusFlags.adc a0 b0 c).cf (by decide)
  simp only [Nat.reducePow] at h0 h1
  omega

/-! ### Concrete Evaluator Tests -/

/-- info: Except.ok 42 -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr (.regular .W64 .W64 (.lea (.low .rax .W64) (.mk .none .none (.int64 41)))),
    .instr (.regular .W64 .W64 (.inc (.reg (.low .rax .W64)))),
    .instr (.regular .W64 .W64 .ret) ]
  let start := exe.labels.label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x100 8 0x1337, regs := { rsp := 0x100 } }
  (exe.eval { data, pc := start } (fun st => st.pc = 0x1337)).bind (fun s => .ok s.1.regs.rax)
