module

import Kraken.Attribute
public import Lean.ToExpr
meta import Lean.Elab.Deriving.ToExpr

@[expose] public section

/-
Common Kraken widths, labels, and executable layout.
-/

inductive Width | W8 | W16 | W32 | W64
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance : ToString Width where
  toString | .W8 => "w8" | .W16 => "w16" | .W32 => "w32" | .W64 => "w64"

namespace Width
@[kstep, simp, reducible] def bits : Width → Nat | W8 => 8 | W16 => 16 | W32 => 32 | W64 => 64
@[kstep, simp, reducible] def bytes : Width → Nat | W8 => 1 | W16 => 2 | W32 => 4 | W64 => 8
@[kstep] abbrev bytesv (w : Width) {n} : BitVec n := BitVec.ofNat n w.bytes
@[kstep] abbrev type (w : Width) : Type := BitVec w.bits
instance {w : Width} : Coe Bool w.type where coe := fun b : Bool => BitVec.ofNat _ b.toNat
end Width

unif_hint (w : Width) where
  w =?= Width.W8 |- Width.type w =?= BitVec 8

unif_hint (w : Width) where
  w =?= Width.W16 |- Width.type w =?= BitVec 16

unif_hint (w : Width) where
  w =?= Width.W32 |- Width.type w =?= BitVec 32

unif_hint (w : Width) where
  w =?= Width.W64 |- Width.type w =?= BitVec 64

abbrev Label := String

class Labels where label : Label → Int64
export Labels (label)

namespace Kraken


abbrev Label := String
instance : Repr ByteArray where reprPrec _ _ := "<opaque byte array>"

deriving instance Lean.ToExpr for ByteArray

inductive Directive (Instr : Type)
  | instr (_ : Instr)
  | label (_ : Label)
  | byteArray (_ : ByteArray)
  deriving BEq, DecidableEq, Repr, Hashable, Lean.ToExpr

structure Sized Directive where
  directive : Directive
  size : Nat

abbrev Program Instr := List (Directive Instr)

structure Executable (Instr : Type) where
  startAddr : Int64
  program : List (Sized (Directive Instr))

-- JP: why is `size` not `Directive → Nat`?
class Layout (Instr : Type) where
  start : Int64
  size : Nat → Nat

variable {Instr : Type}

def Layout.apply (l : Layout Instr) (prog : Program Instr) : Executable Instr :=
  {startAddr := l.start, program := prog.mapIdx (fun i directive => {directive, size := l.size i})}

-- NOTE: We write `List (Kraken.Directive Instr)` here, and not `Kraken.Program Instr`, because architecture
-- specific `Program` types are written as `List Directive` which desugar to `List (Kraken.Directive Instr)`,
-- and so otherwise the typeclass synthesis algorithm would not find this instance.
-- Architecture specific programs are written as `List Directive` for architecture-specific `Directive`
-- instead of `Kraken.Directive Instr` so that `ls[i].foo` searches for `Directive.foo` first, instead of
-- going directly to `Kraken.Directive.foo` (which contains less information)
instance : CoeFun (Layout Instr) (fun _ => List (Directive Instr) → Executable Instr) where
  coe := Layout.apply

structure Addressable (Directive : Type) extends Sized Directive where (addr : Int64)

-- Returns each directive paired with its start address and size.
-- TODO: tail-recursive version for efficiency?
def Executable.withAddresses {Instr : Type} (e : Executable Instr) : List (Addressable (Directive Instr)) :=
  let {startAddr, program} := e
  match program with
  | [] => []
  | instr :: program =>
    {instr with addr := startAddr} :: Executable.withAddresses {startAddr := startAddr + .ofNat instr.size, program}
termination_by e.2

@[simp] theorem Executable.withAddresses_nil {Directive : Type} (startAddr : Int64) :
    Executable.withAddresses (Directive := Directive) {startAddr, program := []} = [] := by
  unfold Executable.withAddresses; rfl

@[simp] theorem Executable.withAddresses_cons {Directive : Type} (startAddr : Int64)
    (instr : Sized Directive) (program : List (Sized Directive)) :
    Executable.withAddresses {startAddr, program := instr :: program} =
      {instr with addr := startAddr} ::
        Executable.withAddresses {startAddr := startAddr + .ofNat instr.size, program} := by
  conv => lhs; unfold Executable.withAddresses

def Executable.directivesAtAddress {Directive : Type} (e : Executable Directive) (a : Int64) : List (Sized Directive) :=
  let starts_at_a := e.withAddresses.dropWhile (·.addr ≠ a)
  (starts_at_a.takeWhile (·.addr = a)).map (·.toSized)

def Executable.directivesFromAddress {Instr : Type} (e : Executable Instr) (a : Int64) : List (Sized (Directive Instr)) :=
  let starts_at_a := e.withAddresses.dropWhile (·.addr ≠ a)
  starts_at_a.map (·.toSized)

theorem Executable.withAddresses_map_snd {Instr : Type} (program : List (Sized (Directive Instr))) (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).map (·.toSized) = program := by
  induction program generalizing startAddr <;> grind [Executable.withAddresses]

theorem Executable.withAddresses_dropWhile_start {Instr : Type} (program : List (Sized (Directive Instr))) (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).dropWhile (fun x => x.addr ≠ startAddr) =
      Executable.withAddresses {startAddr, program} := by
  cases program <;> grind [Executable.withAddresses, List.dropWhile_cons, List.dropWhile_nil]

theorem Executable.directivesFromStart {Instr : Type} [layout : Layout Instr] (prog : Program Instr) :
    (layout prog).directivesFromAddress layout.start =
      prog.mapIdx (fun i directive => {directive, size := layout.size i}) := by
  grind [Executable.withAddresses_dropWhile_start, Executable.withAddresses_map_snd, Executable.directivesFromAddress, Layout.apply]

@[simp] theorem Executable.startAddr_apply {Directive : Type} [layout : Layout Directive] (prog : List Directive) :
    (layout prog).startAddr = layout.start := rfl

theorem Executable.program_apply {Directive : Type} [layout : Layout Directive] (prog : List Directive) :
    (layout prog).program =
      prog.mapIdx (fun i directive => {directive, size := layout.size i}) := rfl

theorem directivesAtFromPrefix {Directive : Type} (e: Executable Directive) (a: Int64):
  ∃ rest, e.directivesFromAddress a = e.directivesAtAddress a ++ rest := by
  dsimp [Executable.directivesFromAddress, Executable.directivesAtAddress]
  refine ⟨((e.withAddresses.dropWhile (·.addr ≠ a)).dropWhile (·.addr = a)).map (·.toSized), ?_⟩
  rw [← List.map_append]
  rw [List.takeWhile_append_dropWhile]

theorem Executable.mem_of_mem_directivesAtAddress {Instr : Type} {e : Executable Instr}
    {a : Int64} {c : Sized (Directive Instr)} (h : c ∈ e.directivesAtAddress a) : c ∈ e.program := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  rw [← Executable.withAddresses_map_snd e.program e.startAddr]
  exact List.mem_map_of_mem
    ((List.dropWhile_sublist _).subset ((List.takeWhile_sublist _).subset hx))

@[grind hom] theorem Int64.toBitVec_ofNat_grind (a : Nat) :
    (Int64.ofNat a).toBitVec = OfNat.ofNat a := by
  rw [Int64.toBitVec_ofNat']; rfl

/-- The sum of sizes of the first `n` directives of `e`. -/
def Executable.sizeBefore {Instr : Type} (e : Executable Instr) (n : Nat) : Nat :=
  ((e.program.take n).map (·.size)).sum

/--
The address of the `n`-th directive of `e`: the start address of `e` plus the sum of sizes of the
first `n` directives.
-/
def Executable.addrOf {Instr : Type} (e : Executable Instr) (n : Nat) : Int64 :=
  e.startAddr + .ofNat (e.sizeBefore n)

@[simp] theorem Executable.addrOf_zero {Instr : Type} (e : Executable Instr) : e.addrOf 0 = e.startAddr := by
  grind [sizeBefore, addrOf]

@[grind →] theorem Executable.sizeBefore_succ {Instr : Type} (e : Executable Instr) {n : Nat}
    {c : Sized (Directive Instr)} (hc : e.program[n]? = some c) : e.sizeBefore (n + 1) = e.sizeBefore n + c.size := by
  simp [sizeBefore, List.take_add_one, hc]

theorem Executable.sizeBefore_add {Instr : Type} (e : Executable Instr) (j i : Nat) :
    e.sizeBefore (j + i) = e.sizeBefore j + (((e.program.drop j).take i).map (·.size)).sum := by
  simp [sizeBefore, List.take_add]

theorem Executable.sizeBefore_mono {Instr : Type} (e : Executable Instr) {j k : Nat}
    (h : j ≤ k) : e.sizeBefore j ≤ e.sizeBefore k := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
  simp [sizeBefore_add]

theorem Executable.addrOf_succ {Instr : Type} (e : Executable Instr) {n : Nat} {c : Sized (Directive Instr)}
    (hc : e.program[n]? = some c) : e.addrOf (n + 1) = e.addrOf n + .ofNat c.size := by
  grind [addrOf]

theorem Executable.getElem?_withAddresses_mk {Instr : Type} :
    ∀ (program : List (Sized (Directive Instr))) (startAddr : Int64) (k : Nat),
      (Executable.withAddresses {startAddr, program})[k]?
        = program[k]?.map (fun c => {c with addr := Executable.addrOf {startAddr, program} k})
  | [], a, k => by rw [Executable.withAddresses]; simp
  | c :: program, a, 0 => by
    rw [Executable.withAddresses]
    simp
  | c :: program, a, k + 1 => by
    rw [Executable.withAddresses]
    simp only [List.getElem?_cons_succ, getElem?_withAddresses_mk program _ k]
    congr 2
    funext c'
    simp only [addrOf, sizeBefore, List.take_succ_cons, List.map_cons, List.sum_cons]
    grind

theorem Executable.getElem?_withAddresses_eq {Instr : Type} (e : Executable Instr) (k : Nat) :
    e.withAddresses[k]? = e.program[k]?.map (fun c => {c with addr := e.addrOf k}) :=
  getElem?_withAddresses_mk e.program e.startAddr k


private theorem dropWhile_eq_drop_of {α : Type _} {p : α → Bool} {l : List α} {j : Nat}
    (hprior : ∀ k, k < j → ∀ c, l[k]? = some c → p c = true)
    (hhead : ∀ c, l[j]? = some c → p c = false) :
    l.dropWhile p = l.drop j := by
  rw [List.dropWhile_eq_drop_findIdx_not]
  by_cases hj : j < l.length
  · rw [(List.findIdx_eq hj).mpr ⟨by simp [hhead _ (List.getElem?_eq_getElem hj)],
      fun k hk => by simp [hprior k hk _ (List.getElem?_eq_getElem (by omega))]⟩]
  · rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hj), List.drop_eq_nil_iff]
    refine Nat.le_of_eq (List.findIdx_eq_length.mpr fun x hx => ?_).symm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp [hprior i (by omega) _ (List.getElem?_eq_getElem hi)]

theorem Executable.withAddresses_dropWhile_addrOf {Instr : Type} (e : Executable Instr) (j n : Nat)
    (hj : e.addrOf j = e.addrOf n)
    (hfresh : ∀ k, k < j → e.addrOf k ≠ e.addrOf n) :
    e.withAddresses.dropWhile (·.addr ≠ e.addrOf n)
      = e.withAddresses.drop j := by
  apply dropWhile_eq_drop_of
  · intro k hk c hc
    rw [Executable.getElem?_withAddresses_eq] at hc
    obtain ⟨dz, -, rfl⟩ := Option.map_eq_some_iff.mp hc
    simpa using hfresh k hk
  · intro c hc
    rw [Executable.getElem?_withAddresses_eq] at hc
    obtain ⟨dz, -, rfl⟩ := Option.map_eq_some_iff.mp hc
    simpa using hj

theorem Executable.directivesFromAddress_addrOf {Directive : Type} (e : Executable Directive) (j n : Nat)
    (hj : e.addrOf j = e.addrOf n)
    (hfresh : ∀ k, k < j → e.addrOf k ≠ e.addrOf n) :
    e.directivesFromAddress (e.addrOf n) = e.program.drop j := by
  dsimp [Executable.directivesFromAddress]
  rw [Executable.withAddresses_dropWhile_addrOf e j n hj hfresh, List.map_drop, Executable.withAddresses_map_snd]

theorem Executable.directivesFromAddress_eq_nil_of {Directive : Type} (e : Executable Directive) (pc : Int64)
    (h : ∀ k, k < e.program.length → e.addrOf k ≠ pc) :
    e.directivesFromAddress pc = [] := by
  dsimp [Executable.directivesFromAddress]
  rw [dropWhile_eq_drop_of (j := e.withAddresses.length)]
  · simp
  · intro k hk c hc
    rw [Executable.getElem?_withAddresses_eq] at hc
    obtain ⟨dz, hdz, rfl⟩ := Option.map_eq_some_iff.mp hc
    have hlt : k < e.program.length := by
      by_cases h' : k < e.program.length
      · exact h'
      · rw [List.getElem?_eq_none (by omega)] at hdz; cases hdz
    simpa using h k hlt
  · intro c hc
    rw [List.getElem?_eq_none (Nat.le_refl _)] at hc
    cases hc

private theorem takeWhile_eq_take_of {α : Type _} {p : α → Bool} {l : List α} {n : Nat}
    (hprior : ∀ k, k < n → ∀ c, l[k]? = some c → p c = true)
    (hhead : ∀ c, l[n]? = some c → p c = false) :
    l.takeWhile p = l.take n := by
  rw [List.takeWhile_eq_take_findIdx_not]
  by_cases hn : n < l.length
  · rw [(List.findIdx_eq hn).mpr ⟨by simp [hhead _ (List.getElem?_eq_getElem hn)],
      fun k hk => by simp [hprior k hk _ (List.getElem?_eq_getElem (by omega))]⟩]
  · rw [(List.take_of_length_le (Nat.le_of_not_lt hn) : l.take n = l), List.take_of_length_le]
    refine Nat.le_of_eq (List.findIdx_eq_length.mpr fun x hx => ?_).symm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp [hprior i (by omega) _ (List.getElem?_eq_getElem hi)]

private theorem exists_least_le {P : Nat → Prop} {n : Nat} (h : P n) :
    ∃ j, j ≤ n ∧ P j ∧ ∀ k, k < j → ¬P k := by
  induction n using Nat.strongRecOn with
  | ind n ih => grind

theorem Layout.apply_getElem? {Directive : Type} [layout : Layout Directive] (p : List Directive) (i : Nat) :
    (layout p).program[i]? = (p[i]?).map (fun d => {directive := d, size := layout.size i}) := by
  simp [Layout.apply, List.getElem?_mapIdx]

/-- Shift a `Layout` to start at index `k` of `prog`. -/
@[reducible] def Layout.shift {Directive : Type} (l : Layout Directive) (prog : List Directive) (k : Nat) : Layout Directive where
  start := (l prog).addrOf k
  size i := l.size (k + i)

@[simp] theorem Layout.start_shift {Directive : Type} (l : Layout Directive) (prog : List Directive) (k : Nat) :
    (l.shift prog k).start = (l prog).addrOf k := rfl

@[simp] theorem Layout.size_shift {Directive : Type} (l : Layout Directive) (prog : List Directive) (k i : Nat) :
    (l.shift prog k).size i = l.size (k + i) := rfl

theorem Layout.program_shift {Directive : Type} (l : Layout Directive) (prog : List Directive) (k n : Nat) :
    ((l.shift prog k) ((prog.drop k).take n)).program = ((l prog).program.drop k).take n := by
  ext i c
  by_cases hi : i < n <;>
    simp [Layout.apply, List.getElem?_take, List.getElem?_drop, hi]

theorem Executable.program_apply_drop {Directive : Type} [layout : Layout Directive] (prog : List Directive) (k : Nat) :
    (layout prog).program.drop k =
      (prog.drop k).mapIdx (fun i directive => {directive, size := layout.size (k + i)}) := by
  ext i c
  simp [Layout.apply, List.getElem?_drop]

theorem Executable.program_apply_slice {Directive : Type} [layout : Layout Directive] (prog : List Directive) (k n : Nat) :
    ((layout prog).program.drop k).take n =
      ((prog.drop k).take n).mapIdx (fun i directive => {directive, size := layout.size (k + i)}) := by
  rw [← Layout.program_shift layout prog k n]; rfl

theorem Layout.program_shift_of_slice {Directive : Type} (l : Layout Directive)
    {prog sub : List Directive} {k : Nat} (hsub : (prog.drop k).take sub.length = sub) :
    ((l.shift prog k) sub).program = ((l prog).program.drop k).take sub.length := by
  conv => lhs; rw [← hsub]
  exact Layout.program_shift l prog k sub.length

theorem Layout.addrOf_shift_of_slice {Directive : Type} (l : Layout Directive)
    {prog sub : List Directive} {k i : Nat}
    (hsub : (prog.drop k).take sub.length = sub) (hi : i ≤ sub.length) :
    ((l.shift prog k) sub).addrOf i = (l prog).addrOf (k + i) := by
  have h_add := (l prog).sizeBefore_add k i
  have h_sb : ((l.shift prog k) sub).sizeBefore i =
      ((((l prog).program.drop k).take i).map (·.size)).sum := by
    simp [Executable.sizeBefore, Layout.program_shift_of_slice l hsub, List.take_take, Nat.min_eq_left hi]
  grind [Executable.addrOf, Layout.apply]

theorem Executable.addrOf_apply_succ {Directive : Type} [layout : Layout Directive] {prog : List Directive}
    {k : Nat} {d : Directive} (hd : prog[k]? = some d) :
    (layout prog).addrOf (k + 1) = (layout prog).addrOf k + .ofNat (layout.size k) :=
  Executable.addrOf_succ _ (c := {directive := d, size := layout.size k})
    (by rw [Layout.apply_getElem?, hd]; rfl)

theorem Executable.directivesAtAddress_addrOf {Directive : Type} (e : Executable Directive)
    (h_offset : ∀ j k, e.addrOf j = e.addrOf k → e.sizeBefore j = e.sizeBefore k)
    {k : Nat} {c : Sized Directive} (hc : e.program[k]? = some c) (hz : 0 < c.size) :
    ∃ pre, e.directivesAtAddress (e.addrOf k) = pre ++ [c] ∧
      ∀ c ∈ pre, c.size = 0 := by
  obtain ⟨j, hjk, hj, hmin⟩ :=
    exists_least_le (P := fun i => e.addrOf i = e.addrOf k) rfl
  have hsize := h_offset j k hj
  have hpre : ∀ c ∈ (e.program.drop j).take (k - j), c.size = 0 := by
    have := e.sizeBefore_add j (k - j)
    rw [Nat.add_sub_cancel' hjk] at this
    have hsum : (((e.program.drop j).take (k - j)).map (·.size)).sum = 0 := by omega
    exact fun c hc => List.sum_eq_zero_iff_forall_eq_nat.mp hsum _ (List.mem_map_of_mem hc)
  have haddr : ∀ m, j ≤ m → m ≤ k → e.addrOf m = e.addrOf k := fun m hjm hmk => by
    grind [Executable.addrOf, e.sizeBefore_mono hjm, e.sizeBefore_mono hmk]
  have hnext : e.addrOf (k + 1) ≠ e.addrOf k := fun h => by
    grind [h_offset (k + 1) k h]
  refine ⟨(e.program.drop j).take (k - j), ?_, hpre⟩
  show ((e.withAddresses.dropWhile
    (·.addr ≠ e.addrOf k)).takeWhile (·.addr = e.addrOf k)).map (·.toSized) = _
  rw [Executable.withAddresses_dropWhile_addrOf _ j k hj hmin,
    takeWhile_eq_take_of (n := k - j + 1)]
  · rw [List.map_take, List.map_drop, Executable.withAddresses_map_snd, List.take_add_one,
      List.getElem?_drop, Nat.add_sub_cancel' hjk, hc]
    rfl
  · intro m hm c hc
    have := haddr (j + m) (by omega) (by omega)
    grind [Executable.getElem?_withAddresses_eq]
  · intro c hc
    grind [Executable.getElem?_withAddresses_eq]

theorem Executable.directivesFromAddress_cases {Directive : Type} (e : Executable Directive) (pc : Int64) :
    e.directivesFromAddress pc = [] ∨
    ∃ j < e.program.length, e.addrOf j = pc ∧ e.directivesFromAddress pc = e.program.drop j := by
  by_cases h : ∃ n < e.program.length, e.addrOf n = pc
  · obtain ⟨n, hn, hpc⟩ := h
    obtain ⟨j, hjn, hj, hmin⟩ := exists_least_le (P := fun i => e.addrOf i = pc) hpc
    refine Or.inr ⟨j, Nat.lt_of_le_of_lt hjn hn, hj, ?_⟩
    rw [← hj]
    exact Executable.directivesFromAddress_addrOf e j j rfl (fun k hk => by simpa [hj] using hmin k hk)
  · refine Or.inl (Executable.directivesFromAddress_eq_nil_of e pc fun k hk hpc => h ⟨k, hk, hpc⟩)

end Kraken
