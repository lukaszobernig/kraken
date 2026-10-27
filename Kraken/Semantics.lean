module

import Kraken.Attribute
public import Kraken.BitVecArith
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

/-- Observable microarchitectural events for constant-time verification. -/
inductive LeakageEvent where
  | exec (p : Std.Rco Int64)
  | read (addr : BitVec 64) (w : Width)
  | write (addr : BitVec 64) (w : Width)
  | var_time (vals : List (BitVec 64))

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
  | require_const_time (vals : List (BitVec 64)) (ok : Unit → Effects MachineData)

end Kraken

export Kraken (LeakageEvent)
export Kraken.Effects (unimplemented unaligned nonmem_load nonmem_store undefined require_read_access require_write_access require_exec_access require_const_time)

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

@[instance_reducible]
def labels {D MD : Type} [ArchDirective D MD]
    (e : Kraken.Executable D) : Labels :=
  { label l := (e.withAddresses.findSome?
      (fun {directive, addr, ..} => if ArchDirective.label? directive = some l then .some addr else .none)).getD (-1) }

@[reducible]
def label {D MD : Type} [ArchDirective D MD]
    (e : Kraken.Executable D) (l : Label) : Int64 :=
  (e.labels).label l

private theorem findSome?_eq_of_getElem? {α β : Type _} {xs : List α} (p : α → Prop) [DecidablePred p]
    (f : α → β) {k : Nat} {x : α} (hget : xs[k]? = some x) (hpk : p x)
    (hprior : ∀ j < k, ∀ y, xs[j]? = some y → ¬p y) :
    xs.findSome? (fun a => if p a then some (f a) else none) = some (f x) := by
  induction xs generalizing k with
  | nil => simp at hget
  | cons a xs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp [hpk]
    | succ k =>
      have hp0 := hprior 0 (Nat.zero_lt_succ k) a rfl
      simp only [List.findSome?_cons, hp0, ↓reduceIte]
      exact ih hget (fun j hj y hy => hprior (j + 1) (Nat.succ_lt_succ hj) y hy)

private theorem findIdx?_eq_some_elim {α : Type _} {p : α → Bool} {xs : List α} {k : Nat}
    (h : xs.findIdx? p = some k) :
    ∃ x, xs[k]? = some x ∧ p x = true ∧ (∀ j < k, ∀ y, xs[j]? = some y → p y = false) ∧ k < xs.length := by
  induction xs generalizing k with
  | nil => simp at h
  | cons a xs ih =>
    rw [List.findIdx?_cons] at h
    by_cases hp : p a
    · simp only [hp, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨a, rfl, hp, fun j hj => by omega, Nat.zero_lt_succ _⟩
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨k', hk', rfl⟩ := h
      obtain ⟨x, hx, hpx, hprior, hlt⟩ := ih hk'
      refine ⟨x, hx, hpx, fun j hj y hy => ?_, Nat.succ_lt_succ hlt⟩
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
        subst hy
        simpa using hp
      | succ j => exact hprior j (Nat.lt_of_succ_lt_succ hj) y hy

theorem label_eq_layout_addrOf {D MD : Type} [ArchDirective D MD]
    (prog : List D) (l : Label) (k : Nat)
    (h : prog.findIdx? (fun d => ArchDirective.label? d == some l) = some k)
    (layout : Kraken.Layout D) :
    (layout prog).label l = layout.addrOf k := by
  obtain ⟨d, hd, hpd, hprior, hlt⟩ := findIdx?_eq_some_elim h
  have hget : (layout prog).withAddresses[k]? =
      some {directive := d, size := layout.size k, addr := (layout prog).addrOf k} := by
    rw [Kraken.Executable.getElem?_withAddresses_eq, Kraken.Layout.apply_getElem?, hd]; rfl
  have hfind : (layout prog).withAddresses.findSome?
      (fun {directive, addr, ..} => if ArchDirective.label? directive = some l then some addr else none) =
      some ((layout prog).addrOf k) := by
    refine findSome?_eq_of_getElem? (fun x => ArchDirective.label? x.directive = some l)
      (fun x => x.addr) hget (beq_iff_eq.mp hpd) (fun j hj y hy => ?_)
    rw [Kraken.Executable.getElem?_withAddresses_eq, Kraken.Layout.apply_getElem?] at hy
    simp only [Option.map_eq_some_iff] at hy
    obtain ⟨_, ⟨d', hd', rfl⟩, rfl⟩ := hy
    exact beq_eq_false_iff_ne.mp (hprior j hj d' hd')
  change ((layout prog).withAddresses.findSome?
    (fun {directive, addr, ..} => if ArchDirective.label? directive = some l then some addr else none)).getD (-1) =
    layout.addrOf k
  rw [hfind, Option.getD_some, Kraken.Executable.addrOf_apply_eq layout prog k (Nat.le_of_lt hlt)]

theorem labels_label_eq_layout_addrOf {D MD : Type} [ArchDirective D MD]
    (prog : List D) (l : Label) (k : Nat)
    (h : prog.findIdx? (fun d => ArchDirective.label? d == some l) = some k)
    (layout : Kraken.Layout D) :
    ((layout prog).labels).label l = layout.addrOf k :=
  label_eq_layout_addrOf prog l k h layout

theorem withAddresses_label_eq_layout_addrOf {D MD : Type} [ArchDirective D MD]
    (prog : List D) (l : Label) (k : Nat)
    (h : prog.findIdx? (fun d => ArchDirective.label? d == some l) = some k)
    (layout : Kraken.Layout D) :
    ((layout prog).withAddresses.findSome?
      (fun {directive, addr, ..} => if ArchDirective.label? directive = some l then .some addr else .none)).getD (-1) =
      layout.addrOf k :=
  label_eq_layout_addrOf prog l k h layout

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
    | .require_const_time _ ok => handleEffects (ok ())
    | .nonmem_load _ addr _ _ => .error s!"Load at unmapped address {repr addr}"
    | .nonmem_store _ addr _ _ => .error s!"Store at unmapped address {repr addr}"
    | @Kraken.Effects.undefined _ _ t cont =>
        handleEffects (cont (t.from_hash (ArchDirective.undefSeed (D := D) s.data)))

end Kraken.Executable

abbrev eval {D MD : Type} [ArchDirective D MD]
    [layout : Kraken.Layout D] (prog : List D) :=
  Kraken.Executable.eval (layout prog)
