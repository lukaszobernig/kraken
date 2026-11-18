module

/-
`bedrock2`-style Function Specification Helpers for AArch64 (`CallBLAt`, `CallBL`).
-/

public import Kraken.AArch64.OmniSemantics
public import Kraken.AArch64.Sep

@[expose] public section

/-- Standard AArch64 `bl`/`ret` contract at a resolved code address `entry`:
execution returns to the link-register address in `X30` with `post` holding. -/
abbrev CallBLAt (e : Executable) (entry : Int64) (s : MachineData)
    (post : MachineData → Prop) : Prop :=
  WPCallAt e entry s fun st =>
    st.pc = Int64.ofBitVec s.regs.X30.toBitVec ∧
    post st.1

/-- Named AArch64 `bl`/`ret` contract (`bedrock2`'s `fnspec!` analogue for AArch64). -/
def CallBL (e : Executable) (fn : Label) (s : MachineData)
    (post : MachineData → Prop) : Prop :=
  FnSpec e fn fun entry => CallBLAt e entry s post

end
