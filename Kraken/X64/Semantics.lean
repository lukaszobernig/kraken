module

-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html

import Kraken.Attribute
public import Kraken.Layout
public import Kraken.Mem
meta import Kraken.Mem
public import Kraken.Semantics
meta import Kraken.Semantics
public import Kraken.Frame
public import Kraken.X64.Syntax
meta import Kraken.X64.Syntax
public import Lean.ToExpr
meta import Lean.Elab.Deriving.ToExpr

@[expose] public section

attribute [kstep] BitVec.extractLsb'

def BitVec.replaceLow {w n} (old : BitVec w) (new : BitVec n) : BitVec w :=
  (BitVec.append (old.drop n) new).setWidth _

theorem BitVec.setWidth_replaceLow {w n : Nat} (old : BitVec w) (v : BitVec n) (h : n ≤ w := by decide) :
    BitVec.setWidth n (old.replaceLow v) = v := by
  ext i hi
  simp [BitVec.replaceLow, BitVec.drop, BitVec.getLsbD_append]
  grind

@[simp, ksimp]
theorem BitVec.setWidth_8_replaceLow_8 (old : BitVec 64) (v : BitVec 8) :
    BitVec.setWidth 8 (old.replaceLow v) = v :=
  BitVec.setWidth_replaceLow old v

@[simp, ksimp]
theorem BitVec.setWidth_16_replaceLow_16 (old : BitVec 64) (v : BitVec 16) :
    BitVec.setWidth 16 (old.replaceLow v) = v :=
  BitVec.setWidth_replaceLow old v

namespace Reg
@[kstep] def base {w} (r : Reg w) : Reg64 := match r with
  | .low r _ => r
  | .ah => .rax | .bh => .rbx | .ch => .rcx | .dh => .rdx

@[kstep] def offset {w} (r : Reg w) : Nat := match r with
  | .low _ _ => 0
  | .ah | .bh | .ch | .dh => 8
end Reg

namespace AvxReg
def base {w} (r : AvxReg w) : RegMm := match r with
  | .xmm r => r
  | .ymm r => r
  | .zmm r => r
end AvxReg

structure Reg64s where
  rax : UInt64 := 0
  rbx : UInt64 := 0
  rcx : UInt64 := 0
  rdx : UInt64 := 0
  rsi : UInt64 := 0
  rdi : UInt64 := 0
  rsp : UInt64 := 0
  rbp : UInt64 := 0
  r8  : UInt64 := 0
  r9  : UInt64 := 0
  r10 : UInt64 := 0
  r11 : UInt64 := 0
  r12 : UInt64 := 0
  r13 : UInt64 := 0
  r14 : UInt64 := 0
  r15 : UInt64 := 0
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

@[kstep] def Reg64s.get64 (s : Reg64s) (r : Reg64) : Width.W64.type := UInt64.toBitVec (match r with
  | .rax => s.rax | .rbx => s.rbx | .rcx => s.rcx | .rdx => s.rdx
  | .rsi => s.rsi | .rdi => s.rdi | .rsp => s.rsp | .rbp => s.rbp
  | .r8  => s.r8  | .r9  => s.r9  | .r10 => s.r10 | .r11 => s.r11
  | .r12 => s.r12 | .r13 => s.r13 | .r14 => s.r14 | .r15 => s.r15)

@[kstep] def Reg64s.set64 (regs : Reg64s) (r : Reg64) (v : Width.W64.type) : Reg64s :=
  match r with
  | .rax => { regs with rax := UInt64.ofBitVec v } | .rbx => { regs with rbx := UInt64.ofBitVec v }
  | .rcx => { regs with rcx := UInt64.ofBitVec v } | .rdx => { regs with rdx := UInt64.ofBitVec v }
  | .rsi => { regs with rsi := UInt64.ofBitVec v } | .rdi => { regs with rdi := UInt64.ofBitVec v }
  | .rsp => { regs with rsp := UInt64.ofBitVec v } | .rbp => { regs with rbp := UInt64.ofBitVec v }
  | .r8  => { regs with r8  := UInt64.ofBitVec v } | .r9  => { regs with r9  := UInt64.ofBitVec v }
  | .r10 => { regs with r10 := UInt64.ofBitVec v } | .r11 => { regs with r11 := UInt64.ofBitVec v }
  | .r12 => { regs with r12 := UInt64.ofBitVec v } | .r13 => { regs with r13 := UInt64.ofBitVec v }
  | .r14 => { regs with r14 := UInt64.ofBitVec v } | .r15 => { regs with r15 := UInt64.ofBitVec v }

@[kstep] def Reg64s.get (s : Reg64s) {w} (r : Reg w) : w.type :=
  ((s.get64 r.base).drop r.offset).take w.bits
  -- BitVec because it may be signed or unsigned depending on context

@[kstep] def Reg64s.set (s : Reg64s) {w} (r : Reg w) (v : w.type) : Reg64s := match r with
  | .low r .W64 => s.set64 r v
  | .low r .W32 => s.set64 r (v.zeroExtend _)
  | .low r w => s.set64 r ((s.get64 r).replaceLow v)
  | .ah | .bh | .ch | .dh => let old := s.get64 r.base;
    s.set64 r.base (old.replaceLow (BitVec.append v (s.get (.low r.base .W8))))

/-- Register file view of `Reg64s` for frame ("modifies") clauses: `r' ≡ r except [rax, rcx]`. -/
instance : Kraken.RegFile Reg64s where
  Name := Reg64
  get r n := match n with
    | .rax => r.rax | .rbx => r.rbx | .rcx => r.rcx | .rdx => r.rdx
    | .rsi => r.rsi | .rdi => r.rdi | .rsp => r.rsp | .rbp => r.rbp
    | .r8 => r.r8 | .r9 => r.r9 | .r10 => r.r10 | .r11 => r.r11
    | .r12 => r.r12 | .r13 => r.r13 | .r14 => r.r14 | .r15 => r.r15
  names := [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rsp, .rbp,
    .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]
  mem_names n := by cases n <;> simp

/-- System V AMD64 ABI callee-saved general-purpose registers (`rbx`, `rbp`, `r12`–`r15`). -/
@[grind]
def Reg64s.CalleeSavedEq (r r₀ : Reg64s) : Prop :=
  r.rbx = r₀.rbx ∧
  r.rbp = r₀.rbp ∧
  r.r12 = r₀.r12 ∧
  r.r13 = r₀.r13 ∧
  r.r14 = r₀.r14 ∧
  r.r15 = r₀.r15

@[simp, ksimp, grind .]
theorem Reg64s.CalleeSavedEq_refl (r : Reg64s) : r.CalleeSavedEq r :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Reg64s.CalleeSavedEq.symm {r₁ r₂ : Reg64s} (h : r₁.CalleeSavedEq r₂) :
    r₂.CalleeSavedEq r₁ := by
  grind

theorem Reg64s.CalleeSavedEq.trans {r₁ r₂ r₃ : Reg64s}
    (h₁ : r₁.CalleeSavedEq r₂) (h₂ : r₂.CalleeSavedEq r₃) :
    r₁.CalleeSavedEq r₃ := by
  grind

def ZmmValue : Type := BitVec 512
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

def zmmZero : ZmmValue := 0#512

structure RegZmms where
  zmm0  : ZmmValue := zmmZero
  zmm1  : ZmmValue := zmmZero
  zmm2  : ZmmValue := zmmZero
  zmm3  : ZmmValue := zmmZero
  zmm4  : ZmmValue := zmmZero
  zmm5  : ZmmValue := zmmZero
  zmm6  : ZmmValue := zmmZero
  zmm7  : ZmmValue := zmmZero
  zmm8  : ZmmValue := zmmZero
  zmm9  : ZmmValue := zmmZero
  zmm10 : ZmmValue := zmmZero
  zmm11 : ZmmValue := zmmZero
  zmm12 : ZmmValue := zmmZero
  zmm13 : ZmmValue := zmmZero
  zmm14 : ZmmValue := zmmZero
  zmm15 : ZmmValue := zmmZero
  zmm16 : ZmmValue := zmmZero
  zmm17 : ZmmValue := zmmZero
  zmm18 : ZmmValue := zmmZero
  zmm19 : ZmmValue := zmmZero
  zmm20 : ZmmValue := zmmZero
  zmm21 : ZmmValue := zmmZero
  zmm22 : ZmmValue := zmmZero
  zmm23 : ZmmValue := zmmZero
  zmm24 : ZmmValue := zmmZero
  zmm25 : ZmmValue := zmmZero
  zmm26 : ZmmValue := zmmZero
  zmm27 : ZmmValue := zmmZero
  zmm28 : ZmmValue := zmmZero
  zmm29 : ZmmValue := zmmZero
  zmm30 : ZmmValue := zmmZero
  zmm31 : ZmmValue := zmmZero
  deriving Repr, BEq, DecidableEq, Hashable, Hashable, Lean.ToExpr

def RegZmms.get512 (s : RegZmms) (r : RegMm) : AvxWidth.W512.type := (match r with
  | .mm0  => s.zmm0  | .mm1  => s.zmm1  | .mm2  => s.zmm2  | .mm3  => s.zmm3
  | .mm4  => s.zmm4  | .mm5  => s.zmm5  | .mm6  => s.zmm6  | .mm7  => s.zmm7
  | .mm8  => s.zmm8  | .mm9  => s.zmm9  | .mm10 => s.zmm10 | .mm11 => s.zmm11
  | .mm12 => s.zmm12 | .mm13 => s.zmm13 | .mm14 => s.zmm14 | .mm15 => s.zmm15
  | .mm16 => s.zmm16 | .mm17 => s.zmm17 | .mm18 => s.zmm18 | .mm19 => s.zmm19
  | .mm20 => s.zmm20 | .mm21 => s.zmm21 | .mm22 => s.zmm22 | .mm23 => s.zmm23
  | .mm24 => s.zmm24 | .mm25 => s.zmm25 | .mm26 => s.zmm26 | .mm27 => s.zmm27
  | .mm28 => s.zmm28 | .mm29 => s.zmm29 | .mm30 => s.zmm30 | .mm31 => s.zmm31)

def RegZmms.set512 (regs : RegZmms) (r : RegMm) (v : AvxWidth.W512.type) : RegZmms :=
  match r with
  | .mm0  => { regs with zmm0  := v } | .mm1  => { regs with zmm1  := v }
  | .mm2  => { regs with zmm2  := v } | .mm3  => { regs with zmm3  := v }
  | .mm4  => { regs with zmm4  := v } | .mm5  => { regs with zmm5  := v }
  | .mm6  => { regs with zmm6  := v } | .mm7  => { regs with zmm7  := v }
  | .mm8  => { regs with zmm8  := v } | .mm9  => { regs with zmm9  := v }
  | .mm10 => { regs with zmm10 := v } | .mm11 => { regs with zmm11 := v }
  | .mm12 => { regs with zmm12 := v } | .mm13 => { regs with zmm13 := v }
  | .mm14 => { regs with zmm14 := v } | .mm15 => { regs with zmm15 := v }
  | .mm16 => { regs with zmm16 := v } | .mm17 => { regs with zmm17 := v }
  | .mm18 => { regs with zmm18 := v } | .mm19 => { regs with zmm19 := v }
  | .mm20 => { regs with zmm20 := v } | .mm21 => { regs with zmm21 := v }
  | .mm22 => { regs with zmm22 := v } | .mm23 => { regs with zmm23 := v }
  | .mm24 => { regs with zmm24 := v } | .mm25 => { regs with zmm25 := v }
  | .mm26 => { regs with zmm26 := v } | .mm27 => { regs with zmm27 := v }
  | .mm28 => { regs with zmm28 := v } | .mm29 => { regs with zmm29 := v }
  | .mm30 => { regs with zmm30 := v } | .mm31 => { regs with zmm31 := v }

def RegZmms.get (s : RegZmms) {w} (r : AvxReg w) : w.type :=
  (s.get512 r.base).take w.bits

def RegZmms.set (s : RegZmms) {w} (r : AvxReg w) (v : w.type) : RegZmms := match r with
  | .zmm r => s.set512 r v
  | .ymm r => s.set512 r (v.zeroExtend _)
  | .xmm r => s.set512 r (v.zeroExtend _)

def RegZmms.setLegacy (s : RegZmms) {w} (r : AvxReg w) (v : w.type) : RegZmms := match r with
  | .zmm r => s.set512 r v  -- impossible
  | .ymm r => s.set512 r ((s.get512 r).replaceLow v)  -- impossible
  | .xmm r => s.set512 r ((s.get512 r).replaceLow v)

@[kstep]
def BitVec.toAddressSize [address_size: AddressSize] (w: BitVec 64): BitVec address_size.address_size.bits :=
  w.take address_size.address_size.bits

-- TODO: consider adding a `split` helper to switch representations between
-- u128, 4xu32, etc.
def BitVec.packedBinOp {w : Nat} (c : Nat) (op : BitVec c → BitVec c → BitVec c) (a b : BitVec w) : BitVec w :=
  if _ : c = 0 ∨ w < c then
    a -- Fallback/Base case (w = 0 or invalid chunk size)
  else
    -- Extract the lowest chunk
    let a_low := a.take c
    let b_low := b.take c
    let res_low := op a_low b_low

    -- Recursively process the remaining high bits
    let a_high := a.drop c
    let b_high := b.drop c
    let res_high := BitVec.packedBinOp c op a_high b_high

    -- Recombine: res_high is the high part, res_low is the low part
    (BitVec.append res_high res_low).setWidth _
termination_by w
decreasing_by omega

def BitVec.toFloat32 (v : BitVec 32) : Float32 :=
  Float32.ofBits (UInt32.ofBitVec v)

def Float32.toBitVec (f : Float32) : BitVec 32 :=
  UInt32.toBitVec (Float32.toBits f)

/-- An SSE single-precision operation on one lane: a NaN operand propagates (quieted, the first
operand winning), and an invalid operation gives the default NaN ("QNaN floating-point
indefinite"). In binary32, `0x400000` is bit 22, the most significant fraction bit, which makes a
NaN quiet; `0xffc00000` (sign set, exponent all ones, fraction `100…0`) is the default NaN.
Lean's `Float32` can't express this: its logical model has a single NaN (all NaNs are equal), so
every NaN result reads back as `0x7fc00000`. -/
def sseBinOp (op : Float32 → Float32 → Float32) (a b : BitVec 32) : BitVec 32 :=
  if a.toFloat32.isNaN then a ||| 0x400000#32
  else if b.toFloat32.isNaN then b ||| 0x400000#32
  else let r := op a.toFloat32 b.toFloat32; if r.isNaN then 0xffc00000#32 else r.toBitVec

structure StatusFlags where
  cf : Bool
  pf : Bool
  af : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

structure MachineData where -- does not include code or program position
  regs : Reg64s := {}
  zmms : RegZmms := {}
  status : StatusFlags := .mk false false false false false false
  dmem : DataMem := ∅
  deriving Repr, BEq, DecidableEq

@[reducible]
instance : HasDataMem MachineData where
  dmem s := s.dmem
  withDmem s dmem := { s with dmem }

instance (w : AvxWidth) : NondetSupportingType w.type where
  from_hash h := h.toBitVec.setWidth w.bits

instance : NondetSupportingType StatusFlags where
  from_hash h := let h := h.toBitVec; (.mk h[0] h[1] h[2] h[3] h[4] h[5])

abbrev MachineState := Kraken.MachineState MachineData
abbrev Effects := Kraken.Effects MachineData

-- the unused `Std.Rco Int64` argument and the unmodified `MachineData` return
-- value are present for uniformity with RegOrMem.interp
@[kstep] def Reg.interp {w} (r : Reg w) (s : MachineData) (_ : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) : Effects :=
  ret (s.regs.get r) s

-- Alternatively, we could define this in terms of BitVecs without %:
-- (addr &&& BitVec.ofNat 64 (bytes - 1)) == 0#64
def isAligned (bytes : Nat) (addr : BitVec 64) : Bool :=
  addr.toNat % bytes == 0

-- Legacy SSE instructions are generally stricter about alignment requirements,
-- while AVX (VEX-encoded) instructions can mostly deal with unaligned
-- addresses (https://discourse.llvm.org/t/memory-alignment-model-on-avx-avx2-and-avx-512-targets/34705).
-- For this reason we default checkAlign to false.
def MachineData.loadAvx
  (s : MachineData) (addr : BitVec 64) (w : AvxWidth)
  (ret : w.type → MachineData → Effects) (checkAlign : Bool := false) : Effects :=
  if checkAlign && !(isAligned w.bytes addr) then
    .unaligned addr w.bytes
  else
    require_read_access addr .W64 (fun _unit =>
  match Mem.loadInt s.dmem addr w.bytes with
      | .some i => ret (.ofInt _ i) s
      | .none => unimplemented "AVX nonmem load not supported")

def MachineData.storeAvx (s : MachineData) (addr : BitVec 64) {w : AvxWidth} (v : w.type) (ret: MachineData → Effects) (checkAlign : Bool := false) : Effects :=
  if checkAlign && !(isAligned w.bytes addr) then
    .unaligned addr w.bytes
  else
    require_write_access addr .W64 (fun _unit =>
  match Mem.loadInt s.dmem addr w.bytes with
      | .some _ =>
          ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
      | .none => unimplemented "AVX nonmem store not supported")

@[kstep] def ConstExpr.interp [Labels] : ConstExpr → Std.Rco _root_.Int64 → _root_.Int64
  | .label l, _ => Labels.label l
  | .int64 i, _ => i
  | .before_current_instruction, r => r.lower
  | .after_current_instruction, r => r.upper
  | .add e1 e2, p => e1.interp p + e2.interp p
  | .sub e1 e2, p => e1.interp p - e2.interp p

@[kstep] def AddrExpr.interp [Labels] [address_size : AddressSize] (a : AddrExpr) (s : Reg64s) (p : Std.Rco Int64) :=
  let base := match a.base with
              | .some (.reg r) => (s.get64 r).toAddressSize.signed
              | .some .rip => p.upper.toInt
              | .none => 0
  let idx := match a.idx with
             | .some ⟨r, c⟩ => (s.get64 r).toAddressSize.signed * c.bytes
             | .none => 0
  BitVec.ofInt address_size.address_size.bits (base + idx + (a.disp.interp p).toInt)

@[kstep] def RegOrMem.interp {w} [Labels] [AddressSize]
  (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) :=
match o with
  | .reg r => ret (s.regs.get r) s
  | .mem a => MachineData.load s ((a.interp s.regs p).zeroExtend _) w ret

def AvxRegOrMem.interp {w} [Labels] [AddressSize]
  (o : AvxRegOrMem w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) (checkAlign : Bool := false) :=
match o with
  | .avx r => ret (s.zmms.get r) s
  | .mem a => s.loadAvx ((a.interp s.regs p).zeroExtend _) w ret checkAlign

@[kstep]
def MachineData.setReg (s : MachineData) {w} (r : Reg w) (v : w.type) : MachineData :=
  { s with regs := s.regs.set r v }

def MachineData.setAvxReg (s : MachineData) {w : AvxWidth} (r : AvxReg w) (v : w.type) : MachineData :=
  { s with zmms := s.zmms.set r v }

def MachineData.setAvxLegacyReg (s : MachineData) {w : AvxWidth} (r : AvxReg w) (v : w.type) : MachineData :=
  { s with zmms := s.zmms.setLegacy r v }

@[kstep]
def MachineData.set {w} [Labels] [AddressSize] (s : MachineData) (d : Dst w) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects) : Effects :=
  match d with
  | .reg r => ret (s.setReg r v)
  | .mem a => MachineData.store s ((a.interp s.regs p).zeroExtend _) v ret

def MachineData.setAvx {aw} [Labels] [AddressSize] (s : MachineData) (d : AvxDst aw) (v : aw.type) (p : Std.Rco Int64) (ret : MachineData → Effects) (checkAlign : Bool := false) : Effects :=
match d with
  | .avx r => ret (s.setAvxReg r v)
  | .mem a => s.storeAvx ((a.interp s.regs p).zeroExtend _) v ret checkAlign

def MachineData.setAvxLegacy {w} [Labels] [AddressSize] (s : MachineData) (d : AvxDst w) (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects) (checkAlign : Bool := false) : Effects :=
match d with
  | .avx r => ret (s.setAvxLegacyReg r v)
  | .mem a => s.storeAvx ((a.interp s.regs p).zeroExtend _) v ret checkAlign

@[kstep] def Operand.interp {w} [Labels] [AddressSize]
  (o : Operand w) (s : MachineData) (p : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) :=
  match o with
  | regOrMem rm => rm.interp s p ret
  | .imm v => ret ((v.interp p).toBitVec.truncate _) s
  -- we rely on assemblers erroring out on too-large immediates in uniform ops

def AvxOperand.interp {aw} [Labels] [AddressSize]
  (o : AvxOperand aw) (s : MachineData) (p : Std.Rco Int64)
  (ret : aw.type → MachineData → Effects) (checkAlign : Bool := false) :=
match o with
  | regOrMem rm => rm.interp s p ret checkAlign

@[kstep]
def CondCode.interp (cc : CondCode) (s : StatusFlags) : Bool := match cc with
  | .o  => s.of | .no => !s.of
  | .c  => s.cf | .nc => !s.cf
  | .z  => s.zf | .nz => !s.zf
  | .be => s.cf || s.zf | .a  => !s.cf && !s.zf
  | .s  => s.sf | .ns => !s.sf
  | .p  => s.pf | .np => !s.pf
  | .l  => s.sf != s.of | .ge => s.sf == s.of
  | .le => (s.sf != s.of) || s.zf | .g  => !s.zf && (s.sf == s.of)

@[kstep] def ShiftCountExpr.interp [Labels] (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) := match c with
  | .cl => s.regs.rcx.toBitVec.take 8
  | .imm8 v => (v.interp p).toBitVec.take _
@[kstep] def ShiftCountExpr.interpMasked [Labels] (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) (w : Width) : Nat :=
  (c.interp s p).toNat &&& match w with | .W64 => 0x3f | _ => 0x1f -- "masked to 5 bits (or 6 bits with a 64-bit operand)"

@[kstep] def RelRegOrMem.interp [Labels] [AddressSize]
  (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64)
  (ret : BitVec 64 → MachineData → Effects) :=
  match o with
  | .rel c => ret (p.upper + c.interp p).toBitVec s
  | .reg r => ret (s.regs.get r) s
  | .mem a => MachineData.load s ((a.interp s.regs p).zeroExtend _) .W64 ret

structure StatusFlags.from_result.Remaining where
  cf : Bool
  af : Bool
  of : Bool
  deriving Repr, BEq, DecidableEq

-- TEMPORARY: definitions stolen from Lean 4.28's standard library, but with a
-- different name so that this file builds with both 4.27 and 4.28
namespace BitVec
def cpopNatRec_ {w} (x : BitVec w) (pos acc : Nat) : Nat :=
  match pos with
  | 0 => acc
  | n + 1 => x.cpopNatRec_ n (acc + (x.getLsbD n).toNat)

def cpop_ {w} (x : BitVec w) : BitVec w := BitVec.ofNat w (cpopNatRec_ x w 0)
end BitVec

@[kstep] def StatusFlags.from_result {w} (result : BitVec w) (f : from_result.Remaining) : StatusFlags :=
  { pf := (result.take 8).cpop_ % 2 == BitVec.zero _
    zf := result == BitVec.zero _
    sf := result.msb, cf := f.cf, af := f.af, of := f.of }

/-! ### Flag-setting arithmetic

The flag functions below are the abstraction boundary for symbolic execution: `kstep` does not
unfold them (they are deliberately not `@[kstep]`/`@[simp]`), so a state after `cmp %rbx, %rax`
reads `status := StatusFlags.sub rax rbx`, and the projection lemmas at the end of this file
(`StatusFlags.sub_cf : (sub a b).cf = decide (a.toNat < b.toNat)`, …) present the individual
flags as decided value-level facts when a condition code or a carry-in reads them.

The definitions follow the architecture reference: a flag is set iff the wrapped result differs
from the exact (unbounded) result. -/

/-- Flags of `add`: `v = a + b`. -/
def StatusFlags.add {w} (a b : BitVec w) : StatusFlags :=
  let v := a + b
  StatusFlags.from_result v {
    cf := v.unsigned != a.unsigned + b.unsigned
    af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
    of := v.signed != a.signed + b.signed }

/-- Flags of `adc`: `v = a + b + c`. -/
def StatusFlags.adc {w} (a b : BitVec w) (c : Bool) : StatusFlags :=
  let v := a + b + BitVec.ofNat w c.toNat
  StatusFlags.from_result v {
    cf := v.unsigned != a.unsigned + b.unsigned + c
    af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
    of := v.signed != a.signed + b.signed + c }

/-- Flags of `sub`/`cmp`: `v = a - b`. -/
def StatusFlags.sub {w} (a b : BitVec w) : StatusFlags :=
  let v := a - b
  StatusFlags.from_result v {
    cf := v.unsigned != a.unsigned - b.unsigned
    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
    of := v.signed != a.signed - b.signed }

/-- Flags of `sbb`: `v = a - b - c`. -/
def StatusFlags.sbb {w} (a b : BitVec w) (c : Bool) : StatusFlags :=
  let v := a - b - BitVec.ofNat w c.toNat
  StatusFlags.from_result v {
    cf := v.unsigned != a.unsigned - b.unsigned - c
    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned - c,
    of := v.signed != a.signed - b.signed - c }

/-- Flags of `inc`: `v = a + 1`, `cf` unchanged. -/
def StatusFlags.inc {w} (a : BitVec w) (cf : Bool) : StatusFlags :=
  let v := a + 1
  StatusFlags.from_result v {
    cf := cf
    af := (v.take 4).unsigned != (a.take 4).unsigned + 1,
    of := v.signed != a.signed + 1 }

/-- Flags of `dec`: `v = a - 1`, `cf` unchanged. -/
def StatusFlags.dec {w} (a : BitVec w) (cf : Bool) : StatusFlags :=
  let v := a - 1
  StatusFlags.from_result v {
    cf := cf
    af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
    of := v.signed != a.signed - 1 }

/-- Flags of `neg`: `v = -b`. -/
def StatusFlags.neg {w} (b : BitVec w) : StatusFlags :=
  let v := -b
  StatusFlags.from_result v {
    cf := b != 0
    af := (b.take 4) != 0,
    of := v.signed != - b.signed }

/-- Flags of the logical operations (`and`, `or`, `xor`, `test`): `cf = of = 0`, `af` undefined. -/
def StatusFlags.logical {w} (v : BitVec w) (af : Bool) : StatusFlags :=
  StatusFlags.from_result v { cf := false, af, of := false }



set_option maxHeartbeats 1000000
@[kstep] def Operation.interp [Labels] [address_size : AddressSize]
  {w} (i : Operation w) (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match (generalizing := false) (motive := Operation w → Effects) i with
  | .mov dst src => src.interp s p (fun val s => s.set dst val p next)
  | .movsx dst src => src.interp s p (fun val s => s.set dst (val.signExtend _) p next)
  | .movzx dst src => src.interp s p (fun val s => s.set dst (val.zeroExtend _) p next)
  | .push src =>
    src.interp s p (fun v s =>
    let rsp := s.regs.get64 .rsp - w.bytesv
    MachineData.store { s with regs := s.regs.set64 .rsp rsp } rsp v next)
  | .pop dst =>
    let rsp := s.regs.get64 .rsp
    MachineData.load s rsp w (fun val s =>
    let s := { s with regs := s.regs.set64 .rsp (rsp + w.bytesv) }
    s.set dst val p next)
  | .setcc cc dst =>
    s.set dst (cc.interp s.status) p next
  | .cmovcc cc dst src =>
    src.interp s p (fun src s =>
    let v := if cc.interp s.status then src else s.regs.get dst
    next (s.setReg dst v))
-- Arithmetic
  | .lea dst src => next (s.setReg dst ((src.interp s.regs p).zeroExtend _))
  | .add dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := a + b
    { s with status := StatusFlags.add a b }.set dst v p next))
  | .adc dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let c := s.status.cf
    let v := a + b + c
    { s with status := StatusFlags.adc a b c }.set dst v p next))
  | .adcx dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := a + b + s.status.cf
    let cf := (StatusFlags.adc a b s.status.cf).cf
    next { s with regs := s.regs.set dst v, status := { s.status with cf := cf }}))
  | .adox dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := a + b + s.status.of
    let of := (StatusFlags.adc a b s.status.of).cf
    next { s with regs := s.regs.set dst v, status := { s.status with of := of }}))
  | .inc dst =>
    dst.interp s p (fun a s =>
    let v := a + 1
    { s with status := StatusFlags.inc a s.status.cf }.set dst v p next)
  | .dec dst =>
    dst.interp s p (fun a s =>
    let v := a - 1
    { s with status := StatusFlags.dec a s.status.cf }.set dst v p next)
  | .neg dst =>
    dst.interp s p (fun b s =>
    let v := -b
    { s with status := StatusFlags.neg b }.set dst v p next)
  | .sub dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let v := b - a
    { s with status := StatusFlags.sub b a }.set dst v p next))
  | .sbb dst src =>
    src.interp s p (fun a s =>
    dst.interp s p (fun b s =>
    let c := s.status.cf
    let v := b - a - c
    { s with status := StatusFlags.sbb b a c }.set dst v p next))
  | .cmp a b =>
    a.interp s p (fun a s =>
    b.interp s p (fun b s =>
    next { s with status := StatusFlags.sub a b }))
  | .mul src =>
    let a := s.regs.get (Reg.low .rax w)
    src.interp s p (fun b s =>
    let v := a * b
    let vn := a.unsigned * b.unsigned
    let s := if w == .W8
      then s.setReg (.low .rax .W16) (.ofInt _ vn)
      else (s.setReg (.low .rax w) v).setReg (.low .rdx w) (.ofInt _ (vn >>> w.bits))
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    next { s with status := { cf := v.unsigned != vn, pf, af, zf, sf, of := v.unsigned != vn }})))))
  | .mulx r_hi r_lo src1 =>
    src1.interp s p (fun a s =>
    let b := s.regs.get (.low .rdx w)
    let v := a.unsigned * b.unsigned
    let s := s.setReg r_lo (.ofInt _ v) -- if r_hi = r_li, hi is written:
    let s := s.setReg r_hi (.ofInt _ (v >>> w.bits))
    next s)
  -- imul1 and imul collectively describe variants of the same
  -- syntax level `imul` instruction, where imul1 is the 1-operand case
  | .imul1 src =>
    let a := s.regs.get (Reg.low .rax w)
    src.interp s p (fun b s =>
    let v := a.toInt * b.toInt
    let s := if w == .W8 then
      s.setReg (.low .rax .W16) (BitVec.ofInt 16 v)
    else
      let result := BitVec.ofInt (w.bits * 2) v
      let low := result.take w.bits
      let high := (result.drop w.bits).setWidth _
      (s.setReg (.low .rax w) low).setReg (.low .rdx w) high
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    let low := BitVec.ofInt w.bits v
    let cf := v != low.toInt
    next { s with status := { cf := cf, pf, af, zf, sf, of := cf }})))))
  | .imul dst src1 src2 =>
    src1.interp s p (fun a s =>
    src2.interp s p (fun b s =>
    let v := a * b
    s.set (match (generalizing := false) (motive := Option (RegOrMem w) → RegOrMem w)
             dst with | .some dst => dst | _ => src1) v p (fun s =>
    let cf := v.signed != a.signed * b.signed
    undefined (λ sf => undefined (λ zf => undefined (λ af => undefined (λ pf =>
    next { s with status := { cf := cf, pf, af, zf, sf, of := cf }})))))))
-- Bitwise
  | .test a b =>
    a.interp s p (fun a s =>
    b.interp s p (fun b s =>
    let v := a &&& b
    undefined (fun af =>
    next { s with status := StatusFlags.logical v af })))
  | .and dst src | .or dst src | .xor dst src =>
    dst.interp s p (fun a s =>
    src.interp s p (fun b s =>
    let v := match i with | .and _ _ => a &&& b | .or _ _ => a ||| b | _ => a ^^^ b
    undefined (fun af =>
    { s with status := StatusFlags.logical v af }.set dst v p next)))
  | .not dst =>
    dst.interp s p (fun a s =>
    let v := ~~~a
    s.set dst v p next)
  | .shl dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    -- A zero count leaves flags unchanged but still writes dst, zero-extending 32-bit registers.
    if count == 0 then s.set dst a p next else
    let v := a <<< count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a <<< (count-1)).msb else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .shr dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let v := a.ushiftRight count
    undefined (λ af =>
    (λ setcf => if count < w.bits then setcf (a.getLsbD (count-1)) else undefined setcf) (λ cf =>
    (λ setof => if count == 1 then setof a.msb else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next))))
  | .sar dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let v := a.sshiftRight count
    let cf := (a.sshiftRight (count-1)).getLsbD 0
    undefined (λ af =>
    (λ setof => if count == 1 then setof false else undefined setof) (λ of =>
    { s with status := .from_result v { s.status with cf, af, of } }.set dst v p next)))
  | .shrd dst src count =>
    dst.interp s p (fun a s =>
    src.interp s p (fun b s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let v := (((b.append a) >>> count).take w.bits).setWidth _
    (λ setstatus => if count > w.bits then undefined setstatus else
      let cf := a.getLsbD (count-1)
      undefined (λ af =>
      (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
      setstatus (.from_result v { cf, af, of})))) (λ status =>
    -- The result is undefined if the count exceeds the operand size (only possible for 16 bits).
    (λ setv => if count > w.bits then undefined setv else setv v) (λ v =>
    { s with status }.set dst v p next))))
  | .shld dst src count =>
    dst.interp s p (fun a s =>
    src.interp s p (fun b s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let v := (((a.append b) <<< count).drop w.bits).setWidth _
    (λ setstatus => if count > w.bits then undefined setstatus else
      let cf := (a <<< (count-1)).msb
      undefined (λ af =>
      (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
      setstatus (.from_result v { cf, af, of})))) (λ status =>
    (λ setv => if count > w.bits then undefined setv else setv v) (λ v =>
    { s with status }.set dst v p next))))
  | .rol dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let v := a.rotateLeft count
    let cf := v.getLsbD 0
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .ror dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let v := a.rotateRight count
    let cf := v.msb
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .rcr dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let t := (BitVec.ofBool s.status.cf ++ a).rotateRight count
    let (cf, v) := (t.msb, t.take w.bits)
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .rcl dst count =>
    dst.interp s p (fun a s =>
    let count := count.interpMasked s p w
    if count == 0 then s.set dst a p next else
    let t := (BitVec.ofBool s.status.cf ++ a).rotateLeft count
    let (cf, v) := (t.msb, t.take w.bits)
    (λ setof => if count == 1 then setof (v.msb != a.msb) else undefined setof) (λ of =>
    { s with status := { s.status with cf, of } }.set dst v p next))
  | .bswap dst =>
    let a := s.regs.get dst
    match (generalizing := false) (motive := Width → Effects) w with
    | .W32 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.drop 24
      next (s.setReg dst (v.setWidth _))
    | .W64 =>
      let v := a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8
            ++ a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.drop 56
      next (s.setReg dst (v.setWidth _))
    | _ => undefined (fun v => next (s.setReg dst v))
  | .jcc cc l =>
    if cc.interp s.status
    then jmp (label l) s
    else next s
  | .jmp tgt =>
    tgt.interp s p (fun a s =>
    jmp (.ofBitVec a) s)
  | .call tgt =>
    tgt.interp s p (fun a s =>
    let rsp := s.regs.get64 .rsp - Width.W64.bytesv
    MachineData.store { s with regs := s.regs.set64 .rsp rsp } rsp (w:=.W64) p.upper.toBitVec (jmp (.ofBitVec a)))
  | .ret =>
    let rsp := s.regs.get64 .rsp
    MachineData.load s rsp .W64 (fun ra s =>
    jmp (.ofBitVec ra) { s with regs := s.regs.set64 .rsp (rsp + 8) })
  | nop _ | nopalign _ _ => next s

-- AVX Operations Interpreter
def AvxOperation.interp [Labels] [address_size : AddressSize]
  {w} (i : AvxOperation w) (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → Effects) : Effects :=
match i with
  | .movups dst src => src.interp s p (fun val s => s.setAvxLegacy dst val p next)
  | .vmovups dst src => src.interp s p (fun val s => s.setAvx dst val p next)
  | .movaps dst src =>
    src.interp s p (checkAlign := true)
      (fun val s => s.setAvxLegacy dst val p (checkAlign := true) next)
  -- TODO: MXCSR
  | .subps dst src =>
    src.interp s p (checkAlign := true) (fun a s =>
    dst.interp s p (fun b s =>
      s.setAvxLegacy dst (BitVec.packedBinOp 32 (sseBinOp (· - ·)) b a) p next))
  | .addps dst src =>
    src.interp s p (checkAlign := true) (fun a s =>
    dst.interp s p (fun b s =>
      s.setAvxLegacy dst (BitVec.packedBinOp 32 (sseBinOp (· + ·)) b a) p next))

@[kstep]
def Instr.interp [Labels]
  (i : Instr) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  require_exec_access p (fun _unit =>
    match i with
      | .regular addr_sz op_sz op =>
          Operation.interp (w := op_sz) (address_size := .mk addr_sz) op p s next jmp
      | .avx addr_sz op_sz op =>
          AvxOperation.interp (w := op_sz) (address_size := .mk addr_sz) op p s next
  )

@[kstep] def Directive.interp [Labels]
  (d : Directive) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match d with
  | .label _ => next s
  | .instr i => i.interp s p next jmp
  | .byteArray _ => .unimplemented s!"Unimplemented: execution reached data block at {p.1}"

@[reducible]
instance : ArchDirective Directive MachineData where
  label?
    | .label l => some l
    | _ => none
  interp := Directive.interp
  undefSeed s := hash s.regs

abbrev Layout := Kraken.Layout Directive

@[simp, ksimp]
theorem Executable.labels_start [layout : Layout] (l : Label) (rest : List Directive) :
    @Labels.label (Kraken.Executable.labels (layout (.label l :: rest))) l = layout.start := by
  dsimp [Labels.label, Kraken.Executable.labels, Kraken.Layout.apply, ArchDirective.label?]
  rw [List.mapIdx_cons, Kraken.Executable.withAddresses.eq_def]
  simp

@[simp, ksimp]
theorem Executable.labels_start' [layout : Layout] (l : Label) (rest : List Directive) :
    ((layout.apply (.label l :: rest)).withAddresses.findSome?
      (fun x => if (match x.directive with | .label l' => some l' | _ => none) = some l then some x.addr else none)).getD (-1) =
    layout.start :=
  Executable.labels_start l rest

/-! ## Flags at the value level

The projection lemmas of the flag functions (`@[kcond]`: used by `kstep` when deciding branch
conditions and by `kfinish`) and the limb identities for carry chains. The compare idiom
(`cmp` followed by a condition code) is covered by the architecture-independent `BitVec.cmp_*`
lemmas in `Kraken.BitVecArith`. -/

namespace StatusFlags
section
variable {w : Nat} (a b : BitVec w) (c : Bool)

/-! ### Projections -/

@[simp, kcond] theorem logical_pf (v : BitVec w) (af : Bool) :
    (logical v af).pf = ((v.take 8).cpop_ % 2 == BitVec.zero 8) := rfl
@[simp, kcond, grind =] theorem logical_zf (v : BitVec w) (af : Bool) :
    (logical v af).zf = decide (v = 0#w) := by
  simp [logical, from_result, Bool.beq_eq_decide_eq]
@[simp, kcond, grind =] theorem logical_sf (v : BitVec w) (af : Bool) : (logical v af).sf = v.msb := rfl
@[simp, kcond, grind =] theorem logical_cf (v : BitVec w) (af : Bool) : (logical v af).cf = false := rfl
@[simp, kcond, grind =] theorem logical_af (v : BitVec w) (af : Bool) : (logical v af).af = af := rfl
@[simp, kcond, grind =] theorem logical_of (v : BitVec w) (af : Bool) : (logical v af).of = false := rfl

@[simp, kcond] theorem add_pf : (add a b).pf = (((a + b).take 8).cpop_ % 2 == BitVec.zero 8) := rfl
@[simp, kcond, grind =] theorem add_zf : (add a b).zf = decide (a + b = 0#w) := by
  simp [add, from_result, Bool.beq_eq_decide_eq]
@[simp, kcond, grind =] theorem add_sf : (add a b).sf = (a + b).msb := rfl
@[simp, kcond, grind =] theorem add_cf : (add a b).cf = decide (2 ^ w ≤ a.toNat + b.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [add, from_result, BitVec.unsigned, bne_iff_ne, decide_eq_true_eq]
  have := BitVec.toNat_add_cases a b
  omega
@[simp, kcond] theorem add_af :
    (add a b).af = (((a + b).take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned) := rfl
@[simp, kcond, grind =] theorem add_of : (add a b).of = BitVec.saddOverflow a b := by
  rw [BitVec.saddOverflow_eq_decide]
  rcases w with _ | w
  · simp [add, from_result, BitVec.signed, BitVec.of_length_zero]
  · rw [Bool.eq_iff_iff]
    simp only [add, from_result, BitVec.signed, bne_iff_ne, decide_eq_true_eq,
      BitVec.toInt_add, ne_eq, Int.bmod_two_pow_eq_self_iff (w := w + 1) (by omega)]
    omega

@[simp, kcond] theorem adc_pf :
    (adc a b c).pf = (((a + b + BitVec.ofNat w c.toNat).take 8).cpop_ % 2 == BitVec.zero 8) := rfl
@[simp, kcond, grind =] theorem adc_zf :
    (adc a b c).zf = decide (a + b + BitVec.ofNat w c.toNat = 0#w) := by
  simp [adc, from_result, Bool.beq_eq_decide_eq]
@[simp, kcond, grind =] theorem adc_sf : (adc a b c).sf = (a + b + BitVec.ofNat w c.toNat).msb := rfl
@[simp, kcond, grind =] theorem adc_cf :
    (adc a b c).cf = decide (2 ^ w ≤ a.toNat + b.toNat + c.toNat) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · cases c <;> simp [adc, from_result, BitVec.unsigned, BitVec.of_length_zero]
  rw [Bool.eq_iff_iff]
  simp only [adc, from_result, BitVec.unsigned, bne_iff_ne, decide_eq_true_eq]
  have h1 := BitVec.toNat_add_cases a b
  have h2 := BitVec.toNat_add_cases (a + b) (BitVec.ofNat w c.toNat)
  rw [BitVec.toNat_ofNat_toNat_bool hw] at h2
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Int.natCast_zero, Int.natCast_one,
    Int.add_zero] at h2 ⊢ <;> omega
@[simp, kcond] theorem adc_af :
    (adc a b c).af = (((a + b + BitVec.ofNat w c.toNat).take 4).unsigned !=
      (a.take 4).unsigned + (b.take 4).unsigned + c) := rfl
@[simp, kcond, grind =] theorem adc_of (hw : 1 < w) :
    (adc a b c).of = decide (a.toInt + b.toInt + c.toNat < -2 ^ (w - 1) ∨
      2 ^ (w - 1) ≤ a.toInt + b.toInt + c.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [adc, from_result, BitVec.signed, bne_iff_ne, decide_eq_true_eq, BitVec.toInt_add,
    Int.bmod_add_bmod, BitVec.toInt_ofNat_toNat_bool hw, ne_eq]
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Int.natCast_zero, Int.natCast_one,
    Int.add_zero, Int.bmod_two_pow_eq_self_iff (w := w) (by omega)] <;> omega

@[simp, kcond] theorem sub_pf : (sub a b).pf = (((a - b).take 8).cpop_ % 2 == BitVec.zero 8) := rfl
@[simp, kcond, grind =] theorem sub_zf : (sub a b).zf = decide (a = b) := by
  have : a - b = 0#w ↔ a = b := by grind
  simp [sub, from_result, Bool.beq_eq_decide_eq, this]
@[simp, kcond, grind =] theorem sub_sf : (sub a b).sf = (a - b).msb := rfl
@[simp, kcond, grind =] theorem sub_cf : (sub a b).cf = decide (a.toNat < b.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [sub, from_result, BitVec.unsigned, bne_iff_ne, decide_eq_true_eq]
  have := BitVec.toNat_sub_cases a b
  have := a.isLt; have := b.isLt
  omega
@[simp, kcond] theorem sub_af :
    (sub a b).af = (((a - b).take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned) := rfl
@[simp, kcond, grind =] theorem sub_of : (sub a b).of = BitVec.ssubOverflow a b := by
  rw [BitVec.ssubOverflow_eq_decide]
  rcases w with _ | w
  · simp [sub, from_result, BitVec.signed, BitVec.of_length_zero]
  · rw [Bool.eq_iff_iff]
    simp only [sub, from_result, BitVec.signed, bne_iff_ne, decide_eq_true_eq,
      BitVec.toInt_sub, ne_eq, Int.bmod_two_pow_eq_self_iff (w := w + 1) (by omega)]
    omega

@[simp, kcond] theorem sbb_pf :
    (sbb a b c).pf = (((a - b - BitVec.ofNat w c.toNat).take 8).cpop_ % 2 == BitVec.zero 8) := rfl
@[simp, kcond, grind =] theorem sbb_zf :
    (sbb a b c).zf = decide (a - b - BitVec.ofNat w c.toNat = 0#w) := by
  simp [sbb, from_result, Bool.beq_eq_decide_eq]
@[simp, kcond, grind =] theorem sbb_sf : (sbb a b c).sf = (a - b - BitVec.ofNat w c.toNat).msb := rfl
@[simp, kcond, grind =] theorem sbb_cf :
    (sbb a b c).cf = decide (a.toNat < b.toNat + c.toNat) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · cases c <;> simp [sbb, from_result, BitVec.unsigned, BitVec.of_length_zero]
  rw [Bool.eq_iff_iff]
  simp only [sbb, from_result, BitVec.unsigned, bne_iff_ne, decide_eq_true_eq]
  have h1 := BitVec.toNat_sub_cases a b
  have h2 := BitVec.toNat_sub_cases (a - b) (BitVec.ofNat w c.toNat)
  rw [BitVec.toNat_ofNat_toNat_bool hw] at h2
  have := a.isLt; have := b.isLt
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Int.natCast_zero, Int.natCast_one,
    Int.sub_zero] at h2 ⊢ <;> omega
@[simp, kcond] theorem sbb_af :
    (sbb a b c).af = (((a - b - BitVec.ofNat w c.toNat).take 4).unsigned !=
      (a.take 4).unsigned - (b.take 4).unsigned - c) := rfl
@[simp, kcond, grind =] theorem sbb_of (hw : 1 < w) :
    (sbb a b c).of = decide (a.toInt - b.toInt - c.toNat < -2 ^ (w - 1) ∨
      2 ^ (w - 1) ≤ a.toInt - b.toInt - c.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [sbb, from_result, BitVec.signed, bne_iff_ne, decide_eq_true_eq, BitVec.toInt_sub,
    Int.bmod_sub_bmod, BitVec.toInt_ofNat_toNat_bool hw, ne_eq]
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Int.natCast_zero, Int.natCast_one,
    Int.sub_zero, Int.bmod_two_pow_eq_self_iff (w := w) (by omega)] <;> omega

@[simp, kcond] theorem inc_pf (cf : Bool) :
    (inc a cf).pf = (((a + 1#w).take 8).cpop_ % 2 == BitVec.zero 8) := rfl
@[simp, kcond, grind =] theorem inc_zf (cf : Bool) : (inc a cf).zf = decide (a + 1#w = 0#w) := by
  simp [inc, from_result, Bool.beq_eq_decide_eq]
@[simp, kcond, grind =] theorem inc_sf (cf : Bool) : (inc a cf).sf = (a + 1#w).msb := rfl
@[simp, kcond, grind =] theorem inc_cf (cf : Bool) : (inc a cf).cf = cf := rfl
@[simp, kcond] theorem inc_af (cf : Bool) :
    (inc a cf).af = (((a + 1#w).take 4).unsigned != (a.take 4).unsigned + 1) := rfl
@[simp, kcond, grind =] theorem inc_of (cf : Bool) (hw : 1 < w) :
    (inc a cf).of = decide (2 ^ (w - 1) ≤ a.toInt + 1) := by
  rw [Bool.eq_iff_iff]
  have := BitVec.le_toInt a
  simp only [inc, from_result, BitVec.signed, bne_iff_ne, decide_eq_true_eq, BitVec.toInt_add,
    BitVec.ofNat_eq_ofNat, BitVec.toInt_one_of_lt hw, ne_eq,
    Int.bmod_two_pow_eq_self_iff (w := w) (by omega)]
  omega

@[simp, kcond] theorem dec_pf (cf : Bool) :
    (dec a cf).pf = (((a - 1#w).take 8).cpop_ % 2 == BitVec.zero 8) := rfl
@[simp, kcond, grind =] theorem dec_zf (cf : Bool) : (dec a cf).zf = decide (a = 1#w) := by
  have : a - 1#w = 0#w ↔ a = 1#w := by grind
  simp [dec, from_result, Bool.beq_eq_decide_eq, this]
@[simp, kcond, grind =] theorem dec_sf (cf : Bool) : (dec a cf).sf = (a - 1#w).msb := rfl
@[simp, kcond, grind =] theorem dec_cf (cf : Bool) : (dec a cf).cf = cf := rfl
@[simp, kcond] theorem dec_af (cf : Bool) :
    (dec a cf).af = (((a - 1#w).take 4).unsigned != (a.take 4).unsigned - 1) := rfl
@[simp, kcond, grind =] theorem dec_of (cf : Bool) (hw : 1 < w) :
    (dec a cf).of = decide (a.toInt - 1 < -2 ^ (w - 1)) := by
  rw [Bool.eq_iff_iff]
  have := BitVec.toInt_lt (x := a)
  simp only [dec, from_result, BitVec.signed, bne_iff_ne, decide_eq_true_eq, BitVec.toInt_sub,
    BitVec.ofNat_eq_ofNat, BitVec.toInt_one_of_lt hw, ne_eq,
    Int.bmod_two_pow_eq_self_iff (w := w) (by omega)]
  omega

@[simp, kcond] theorem neg_pf : (neg b).pf = (((-b).take 8).cpop_ % 2 == BitVec.zero 8) := rfl
@[simp, kcond, grind =] theorem neg_zf : (neg b).zf = decide (b = 0#w) := by
  simp [neg, from_result, Bool.beq_eq_decide_eq, BitVec.neg_eq_zero_iff]
@[simp, kcond, grind =] theorem neg_sf : (neg b).sf = (-b).msb := rfl
@[simp, kcond, grind =] theorem neg_cf : (neg b).cf = !decide (b = 0#w) := by
  simp [neg, from_result, bne, Bool.beq_eq_decide_eq]
@[simp, kcond] theorem neg_af : (neg b).af = (b.take 4 != 0) := rfl
@[simp, kcond, grind =] theorem neg_of : (neg b).of = decide (b.toInt = -2 ^ (w - 1)) := by
  rcases w with _ | w
  · simp [neg, from_result, BitVec.signed, BitVec.of_length_zero]
  · rw [Bool.eq_iff_iff]
    have h1 := BitVec.le_toInt b
    have h2 := BitVec.toInt_lt (x := b)
    simp only [neg, from_result, BitVec.signed, bne_iff_ne, decide_eq_true_eq, BitVec.toInt_neg,
      ne_eq, Int.bmod_two_pow_eq_self_iff (w := w + 1) (by omega)]
    simp only [Nat.add_one_sub_one] at h1 h2 ⊢
    omega

/-! ### Limb identities for carry chains: wrapped result + carry weight = exact result -/

theorem add_toNat :
    ((a + b).toNat : Int) + ((add a b).cf).toNat * (2 ^ w : Nat) = a.toNat + b.toNat := by
  rw [add_cf]
  have := BitVec.toNat_add_cases a b
  by_cases h : 2 ^ w ≤ a.toNat + b.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

theorem adc_toNat (hw : 0 < w) :
    ((a + b + BitVec.ofNat w c.toNat).toNat : Int) + ((adc a b c).cf).toNat * (2 ^ w : Nat) =
      a.toNat + b.toNat + c.toNat := by
  rw [adc_cf]
  have h1 := BitVec.toNat_add_cases a b
  have h2 := BitVec.toNat_add_cases (a + b) (BitVec.ofNat w c.toNat)
  rw [BitVec.toNat_ofNat_toNat_bool hw] at h2
  have := a.isLt; have := b.isLt
  have hc : c.toNat ≤ 1 := by cases c <;> simp
  by_cases h : 2 ^ w ≤ a.toNat + b.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

theorem sub_toNat :
    ((a - b).toNat : Int) - ((sub a b).cf).toNat * (2 ^ w : Nat) = a.toNat - b.toNat := by
  rw [sub_cf]
  have := BitVec.toNat_sub_cases a b
  by_cases h : a.toNat < b.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

theorem sbb_toNat (hw : 0 < w) :
    ((a - b - BitVec.ofNat w c.toNat).toNat : Int) - ((sbb a b c).cf).toNat * (2 ^ w : Nat) =
      a.toNat - b.toNat - c.toNat := by
  rw [sbb_cf]
  have h1 := BitVec.toNat_sub_cases a b
  have h2 := BitVec.toNat_sub_cases (a - b) (BitVec.ofNat w c.toNat)
  rw [BitVec.toNat_ofNat_toNat_bool hw] at h2
  have := a.isLt; have := b.isLt
  have hc : c.toNat ≤ 1 := by cases c <;> simp
  by_cases h : a.toNat < b.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

end
end StatusFlags

def Directive.fakeSize (hashOfProgram : UInt64) (d : Directive) : Nat :=
  match d with
  | .label _ => 0
  | .instr (.regular _ _ (.nop sz)) => sz -- may be zero
  | .instr i => (1 + hash (hashOfProgram, i) % 15).toNat
  | .byteArray bs => bs.size

def Program.fakeLayout (prog : Program) : Executable :=
  let : Inhabited Directive := .mk (.byteArray (.mk #[]))
  let h := hash prog;
  let layout : Layout := { start := h.toInt64<<<16, size i := prog[i]!.fakeSize h }
  layout prog

/-- info: Except.ok 42 -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr (.regular .W64 .W64 (.lea (.low .rax .W64) (.mk .none .none (.int64 41)))),
    .instr (.regular .W64 .W64 (.inc (.reg (.low .rax .W64)))),
    .instr (.regular .W64 .W64 .ret) ]
  let start := exe.labels.label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x100 8 0x1337, regs := {rsp := 0x100} }
  (exe.eval {data, pc := start} (fun st => st.pc = 0x1337)).bind (fun s => .ok s.1.regs.rax)
