module

import Kraken.Attribute
public import Kraken.Layout
public import Kraken.Mem
meta import Kraken.Mem

@[expose] public section

/-
Common Kraken execution semantics: effects, machine state, memory access, and directive stepping.
-/

-- injective coercions only
attribute [-instance] BitVec.instNatCast
attribute [-instance] BitVec.instIntCast
instance : Coe Bool Nat where coe := Bool.toNat

namespace BitVec
@[kstep] def unsigned {w} (x : BitVec w) : Int := x.toNat
@[kstep] def signed {w} (x : BitVec w) : Int := x.toInt
@[kstep] def take {w} (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n
@[kstep] def drop {w} (x : BitVec w) (n : Nat) : BitVec (w - n) := x.extractLsb' n (w-n)
end BitVec

attribute [kstep]
  BitVec.ofInt_add
  BitVec.ofInt_toInt
  BitVec.truncate

abbrev DataMem := Mem 64
instance : Repr DataMem where reprPrec _ _ := "<opaque memory>"

/-- Types that support nondeterministic choices in `Effects.undefined`. -/
class NondetSupportingType (α : Type) where
  from_hash : UInt64 → α

instance {n : Nat} : NondetSupportingType (BitVec n) where
  from_hash h := h.toBitVec.setWidth n

instance (w : Width) : NondetSupportingType w.type where
  from_hash h := h.toBitVec.setWidth w.bits

instance : NondetSupportingType Bool where
  from_hash h := h % 2 != 0

namespace Kraken

structure MachineState (MachineData : Type) where
  data : MachineData
  pc : Int64

inductive Effects (MachineData : Type)
  | done (a : MachineState MachineData)
  | unimplemented (msg : String)
  | unaligned (addr : BitVec 64) (align : Nat)
  -- loads and stores *outside* the data memory, eg. MMIO, might still affect the data memory:
  -- for instance, MMIO reads/writes at certain device register addresses might change what
  -- data memory the process logically owns vs what memory is owned by devices
  | nonmem_load (dmem : DataMem) (addr : BitVec 64) (w : Width) (ret : w.type → DataMem → Effects MachineData)
  | nonmem_store (dmem : DataMem) (addr : BitVec 64) {w : Width} (v : w.type) (ret : DataMem → Effects MachineData)
  | undefined {α : Type} [NondetSupportingType α] (ret : α → Effects MachineData)
  | require_read_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects MachineData)
  | require_write_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects MachineData)
  | require_exec_access (p : Std.Rco Int64) (ok : Unit → Effects MachineData)

end Kraken

export Kraken.Effects (unimplemented unaligned nonmem_load nonmem_store undefined require_read_access require_write_access require_exec_access)

class HasDataMem (MachineData : Type) where
  dmem : MachineData → DataMem
  withDmem : MachineData → DataMem → MachineData

attribute [reducible, kstep] HasDataMem.dmem HasDataMem.withDmem

-- Since MMIO can cause devices to do arbitrary actions, a load might actually
-- *modify* memory. For instance:
-- A TEST instruction might load a flag from an MMIO address and bitwise-and it with
-- an immediate, and if the result is non-zero, it might mean that some device has
-- finished processing a buffer and therefore now passes ownership of that buffer
-- to the CPU.
-- Note that `ret` takes a whole `MachineData` instead of only `DataMem`, which
-- provides a bit more flexibility than we need: MachineData.load might change
-- dmem, but will not change the registers or status flags.
-- But this superfluous flexibility helps us simplify the state-threading:
-- Instead of writing `fun v dmem => ... { s with dmem } ...` everywhere, we
-- can just write `fun v s => ...` and the new `s` will shadow the old `s`.
def MachineData.load {MD : Type} [HasDataMem MD]
    (s : MD) (addr : BitVec 64) (w : Width)
    (ret : w.type → MD → Kraken.Effects MD) : Kraken.Effects MD :=
  require_read_access addr w (fun _unit =>
    match Mem.loadInt (HasDataMem.dmem s) addr w.bytes with
    | .some i => ret (.ofInt _ i) s
    | .none => nonmem_load (HasDataMem.dmem s) addr w (fun v dmem => ret v (HasDataMem.withDmem s dmem)))

def MachineData.store {MD : Type} [HasDataMem MD]
    (s : MD) (addr : BitVec 64) {w : Width} (v : w.type)
    (ret : MD → Kraken.Effects MD) : Kraken.Effects MD :=
  require_write_access addr w (fun _unit =>
    match Mem.loadInt (HasDataMem.dmem s) addr w.bytes with
    | .some _ =>
        ret (HasDataMem.withDmem s (Mem.storeInt (HasDataMem.dmem s) addr w.bytes v.toInt))
    | .none => nonmem_store (HasDataMem.dmem s) addr v (fun dmem' => ret (HasDataMem.withDmem s dmem')))

class ArchDirective (D : Type) (MD : outParam Type) where
  label? : D → Option Label
  interp : [Labels] → (d : D) → (s : MD) → (p : Std.Rco Int64) →
    (next : MD → Kraken.Effects MD) →
    (jmp : Int64 → MD → Kraken.Effects MD) →
    Kraken.Effects MD
  undefSeed : MD → UInt64 := fun _ => 0

attribute [simp] ArchDirective.label?
attribute [kstep] ArchDirective.interp

def Directives.interp {D MD : Type} [ArchDirective D MD] [Labels]
    (ds : List (Kraken.Sized D)) (s : MD) (pc : Int64)
    (ret : Int64 → MD → Kraken.Effects MD) : Kraken.Effects MD :=
  match ds with
  | [] => ret pc s
  | {directive, size := sz} :: ds =>
    ArchDirective.interp directive s (.mk pc (pc + .ofNat sz)) (jmp := ret) (next := fun s =>
      interp ds s (pc + .ofNat sz) ret)

namespace Kraken.Executable

@[reducible]
def labels {D MD : Type} [ArchDirective D MD]
    (e : Kraken.Executable D) : Labels :=
  { label l := (e.withAddresses.findSome?
      (fun {directive, addr, ..} => if ArchDirective.label? directive = some l then .some addr else .none)).getD (-1) }

def label {D MD : Type} [ArchDirective D MD]
    (e : Kraken.Executable D) (l : Label) : Int64 :=
  (e.labels).label l

def directivesFromLabel {D MD : Type} [ArchDirective D MD]
    (e : Kraken.Executable D) (l : Label) : List (Kraken.Sized D) :=
  e.program.dropWhile (fun x => ArchDirective.label? x.directive != some l)

def step {D MD : Type} [ArchDirective D MD]
    (e : Kraken.Executable D) (s : Kraken.MachineState MD)
    (ret : Kraken.MachineState MD → Kraken.Effects MD) : Kraken.Effects MD :=
  let := e.labels
  Directives.interp (e.directivesAtAddress s.pc) s.data s.pc (fun pc s => ret ⟨s, pc⟩)

-- Concrete evaluators for expedient testing
partial def eval {D MD : Type} [ArchDirective D MD]
    (e : Kraken.Executable D) (s : Kraken.MachineState MD)
    (until_ : Kraken.MachineState MD → Bool) : Except String (Kraken.MachineState MD) :=
  if until_ s then .ok s else handleEffects (e.step s .done)
where
  handleEffects es :=
    match es with
    | .done s => eval e s until_
    | .unimplemented msg => .error msg
    | .unaligned addr w => .error s!"Unaligned memory access at {repr addr} (required {w}-byte alignment)"
    | .require_read_access _ _ ok => handleEffects (ok ())
    | .require_write_access _ _ ok => handleEffects (ok ())
    | .require_exec_access _ ok => handleEffects (ok ())
    | .nonmem_load _ addr _ _ => .error s!"Load at unmapped address {repr addr}"
    | .nonmem_store _ addr _ _ => .error s!"Store at unmapped address {repr addr}"
    | @Kraken.Effects.undefined _ _ t cont =>
        handleEffects (cont (t.from_hash (ArchDirective.undefSeed (D := D) s.data)))

end Kraken.Executable

abbrev eval {D MD : Type} [ArchDirective D MD]
    [layout : Kraken.Layout D] (prog : List D) :=
  Kraken.Executable.eval (layout prog)
