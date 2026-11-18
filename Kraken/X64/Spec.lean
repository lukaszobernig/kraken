module

/-
`bedrock2`-style Function Specification Helpers for X64 (`RetSlot`, `StackBelow`, `CallX64At`, `CallX64`).
-/

public import Kraken.X64.OmniSemantics
public import Kraken.X64.Sep

@[expose] public section

open Std Std.ExtHashMap

/-- 8-byte return-address stack slot at `sp` holding `retAddr`. -/
def RetSlot (retAddr : Int64) (sp : UInt64) : DataMem → Prop :=
  Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At sp.toBitVec)

theorem RetSlot.bytes_length (retAddr : Int64) :
    (Int.toBytes 8 retAddr.toBitVec.toInt).length = 8 :=
  Int.toBytes_length 8 _

theorem RetSlot.addr_roundtrip (retAddr : Int64) :
    Int64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 retAddr.toBitVec.toInt))) = retAddr := by
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  rfl

/-- `frames.length` 8-byte scratch stack slots immediately below `sp`, framed around `R`. -/
def StackBelow : List (List UInt8) → BitVec 64 → (DataMem → Prop) → DataMem → Prop
  | [], _, R => R
  | bs :: rest, sp, R => Eq (bs.At (sp - 8#64)) ⋆ StackBelow rest (sp - 8#64) R

theorem StackBelow_push_inner (P : DataMem → Prop) :
    ∀ (frames : List (List UInt8)) (sp : BitVec 64) (R : DataMem → Prop),
      (P ⋆ StackBelow frames sp R) = StackBelow frames sp (P ⋆ R)
  | [], _, _ => rfl
  | _ :: rest, sp, R => by
    dsimp only [StackBelow]
    rw [← StackBelow_push_inner P rest (sp - 8#64) R]
    ac_rfl

/-- Standard X64 `call`/`ret` contract at a resolved code address `entry`:
for any return address `retAddr` stored at `%rsp` and disjoint frame `R`,
execution returns to `retAddr` with `%rsp` popped by 8 and `post` holding. -/
abbrev CallX64At (e : Executable) (entry : Int64) (s : MachineData)
    (preMem : (DataMem → Prop) → DataMem → Prop)
    (post : MachineData → (DataMem → Prop) → Prop) : Prop :=
  ∀ (retAddr : Int64) (R : DataMem → Prop),
    preMem (RetSlot retAddr s.regs.rsp ⋆ R) s.dmem →
    WPCallAt e entry s fun st =>
      st.pc = retAddr ∧
      st.1.regs.rsp = s.regs.rsp + 8 ∧
      post st.1 (RetSlot retAddr s.regs.rsp ⋆ R)

/-- Named X64 `call`/`ret` contract (`bedrock2`'s `fnspec!` analogue for X64). -/
def CallX64 (e : Executable) (fn : Label) (s : MachineData)
    (preMem : (DataMem → Prop) → DataMem → Prop)
    (post : MachineData → (DataMem → Prop) → Prop) : Prop :=
  FnSpec e fn fun entry => CallX64At e entry s preMem post

end
