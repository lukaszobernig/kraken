module

public import Lean.ToExpr

@[expose] public section

/-
Common Kraken executable layout, label extraction, dynamic alignment, and function-spec primitives.

Architecture:
1. Surface AST: `Program := List (Directive Instr Const)` retains inline `.label` and `.align`.
2. Pure syntactic preprocessing:
   - `Program.stripLabels : Program → Program` removes `.label` directives, and
   - `Program.extractLabels : Program → List (Label × Nat)` maps each label to its index
     `0 ≤ idx ≤ p.stripLabels.length`.
3. Layout (`Layout.apply`): threads `(addr, idx)` left-to-right over `p.stripLabels`, resolving
   dynamic `.align` padding (`alignPad curAddr log2Align`) and emitting only strictly positive-size
   `Sized (Directive Instr Const)` entries into `Executable.program`, alongside the resolved
   `Executable.labels : Labels`.
-/

namespace Kraken

abbrev Label := String
instance : Repr ByteArray where reprPrec _ _ := "<opaque byte array>"

deriving instance Lean.ToExpr for ByteArray

/-- Partial mapping from assembly labels to their resolved 64-bit addresses. -/
structure Labels where
  label? : Label → Option Int64

instance : CoeFun Labels (fun _ => Label → Option Int64) := ⟨Labels.label?⟩

/-- `L₁ ⊆ L₂` means every label resolved in `L₁` resolves to the same address in `L₂`. -/
instance : HasSubset Labels where
  Subset L₁ L₂ := ∀ l a, L₁.label? l = some a → L₂.label? l = some a

@[simp] theorem Labels.subset_refl (L : Labels) : L ⊆ L := fun _ _ h => h

theorem Labels.subset_trans {L₁ L₂ L₃ : Labels} (h₁ : L₁ ⊆ L₂) (h₂ : L₂ ⊆ L₃) : L₁ ⊆ L₃ :=
  fun l a h => h₂ l a (h₁ l a h)

/-- Look up a label that is known to exist (for `#eval` tests or closed-program specs). -/
def Labels.label! (L : Labels) (l : Label) : Int64 :=
  match L.label? l with
  | some a => a
  | none => panic! s!"unresolved label: {l}"

/-! ## Dynamic Alignment Padding -/

/-- Number of padding bytes in `[0, 2 ^ log2Align)` needed to align `addr` to a `2 ^ log2Align`-byte
boundary. -/
def alignPad (addr : Int64) (log2Align : Nat) : Nat :=
  let a := 2 ^ log2Align
  (a - addr.toUInt64.toNat % a) % a

theorem alignPad_lt (addr : Int64) (k : Nat) : alignPad addr k < 2 ^ k := by
  unfold alignPad
  exact Nat.mod_lt _ (Nat.two_pow_pos k)

theorem alignPad_zero_iff (addr : Int64) (k : Nat) :
    alignPad addr k = 0 ↔ addr.toUInt64.toNat % 2 ^ k = 0 := by
  unfold alignPad
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hlt : addr.toUInt64.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt _ hpos
  constructor
  · intro h
    by_cases hm : addr.toUInt64.toNat % 2 ^ k = 0
    · exact hm
    · have hsub_lt : 2 ^ k - addr.toUInt64.toNat % 2 ^ k < 2 ^ k := by omega
      rw [Nat.mod_eq_of_lt hsub_lt] at h
      omega
  · intro hm
    simp [hm]

theorem alignPad_aligned (addr : Int64) {k : Nat} (hk : k ≤ 64) :
    (addr + .ofNat (alignPad addr k)).toUInt64.toNat % 2 ^ k = 0 := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdvd : 2 ^ k ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hk
  have htoNat : (addr + .ofNat (alignPad addr k)).toUInt64.toNat =
      (addr.toUInt64.toNat + alignPad addr k) % 2 ^ 64 := by
    have hbv : (addr + .ofNat (alignPad addr k)).toBitVec =
        addr.toBitVec + BitVec.ofNat 64 (alignPad addr k) := by
      simp [Int64.toBitVec_add]
    change (addr + .ofNat (alignPad addr k)).toBitVec.toNat = _
    rw [hbv, BitVec.toNat_add, BitVec.toNat_ofNat]
    change (addr.toUInt64.toNat + alignPad addr k % 2 ^ 64) % 2 ^ 64 = _
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [htoNat, Nat.mod_mod_of_dvd _ hdvd]
  unfold alignPad
  have hlt : addr.toUInt64.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt _ hpos
  by_cases hm : addr.toUInt64.toNat % 2 ^ k = 0
  · simp [hm]
  · have hsub_lt : 2 ^ k - addr.toUInt64.toNat % 2 ^ k < 2 ^ k := by omega
    rw [Nat.mod_eq_of_lt hsub_lt, Nat.add_mod]
    have : addr.toUInt64.toNat % 2 ^ k + (2 ^ k - addr.toUInt64.toNat % 2 ^ k) % 2 ^ k = 2 ^ k := by
      rw [Nat.mod_eq_of_lt hsub_lt]; omega
    rw [this, Nat.mod_self]

/-! ## Core Types (`Directive`, `Sized`, `Addressable`, `Program`, `Executable`, `Layout`) -/

inductive Directive (Instr Const : Type) where
  | instr (_ : Instr)
  | label (_ : Label)
  | byteArray (arr : ByteArray)
  /-- A data word of `bytes` bytes whose value is a symbolic constant, e.g. a label or a
  difference of labels (a relocation). It is never executed. Jump tables (`.long .Lcase - .Ltable`)
  and pointer tables (`.quad fn`) are the typical uses. -/
  | word (bytes : Nat) (e : Const)
  /-- Dynamic alignment to a `2 ^ log2Align`-byte boundary (`.p2align`).
  When `executable := true`, any non-zero padding executes as a no-op (multi-byte NOP);
  when `executable := false` (data section), executing padding fails. -/
  | align (log2Align : Nat) (executable : Bool := true)
  deriving DecidableEq, Repr, Hashable, BEq, Lean.ToExpr

structure Sized (Directive : Type) where
  directive : Directive
  size : Nat

structure Addressable (Directive : Type) extends Sized Directive where
  addr : Int64

abbrev Program Instr Const := List (Directive Instr Const)

structure Executable (Instr Const : Type) where
  startAddr : Int64
  program : List (Sized (Directive Instr Const))
  labels : Labels
  program_pos : ∀ c ∈ program, 0 < c.size

class Layout (Instr Const : Type) where
  start : Int64
  instrSize : Nat → Nat
  instrSize_pos : ∀ i, 0 < instrSize i

variable {Instr Const : Type}

/-! ## Label Extraction on `Program` -/

def Program.definedLabels (p : Program Instr Const) : List Label :=
  p.filterMap fun | .label l => some l | _ => none

abbrev _root_.List.definedLabels (p : List (Directive Instr Const)) : List Label :=
  Program.definedLabels p

@[simp] theorem Program.mem_definedLabels {p : Program Instr Const} {l : Label} :
    l ∈ p.definedLabels ↔ .label l ∈ p := by
  simp only [Program.definedLabels, List.mem_filterMap]
  grind

@[simp] theorem Program.definedLabels_append (p q : Program Instr Const) :
    (p ++ q).definedLabels = p.definedLabels ++ q.definedLabels := by
  simp [Program.definedLabels, List.filterMap_append]

/-- Remove all `.label` directives from a `Program`. -/
def Program.stripLabels : Program Instr Const → Program Instr Const
  | [] => []
  | .label _ :: rest => stripLabels rest
  | d :: rest => d :: stripLabels rest

abbrev _root_.List.stripLabels (p : List (Directive Instr Const)) : Program Instr Const :=
  Program.stripLabels p

/-- Extract `(label, idx)` pairs where `idx` is the position in `p.stripLabels`
(`0 ≤ idx ≤ p.stripLabels.length`). -/
def Program.extractLabels : Program Instr Const → List (Label × Nat)
  | [] => []
  | .label l :: rest => (l, 0) :: extractLabels rest
  | _ :: rest => (extractLabels rest).map fun (l, idx) => (l, idx + 1)

abbrev _root_.List.extractLabels (p : List (Directive Instr Const)) : List (Label × Nat) :=
  Program.extractLabels p

@[simp] theorem Program.stripLabels_nil :
    Program.stripLabels ([] : Program Instr Const) = [] := rfl

@[simp] theorem Program.stripLabels_append (p q : Program Instr Const) :
    (p ++ q).stripLabels = p.stripLabels ++ q.stripLabels := by
  induction p with
  | nil => rfl
  | cons d rest ih =>
    cases d <;> simp [Program.stripLabels, ih]

@[simp] theorem Program.extractLabels_nil :
    Program.extractLabels ([] : Program Instr Const) = [] := rfl

@[simp] theorem Program.extractLabels_append (p q : Program Instr Const) :
    (p ++ q).extractLabels =
      p.extractLabels ++ q.extractLabels.map fun (l, idx) => (l, p.stripLabels.length + idx) := by
  induction p with
  | nil => simp
  | cons d rest ih =>
    cases d <;> simp [Program.extractLabels, Program.stripLabels, ih,
      List.map_append, List.map_map, Function.comp_def] <;> omega

theorem Program.definedLabels_eq_map_fst (p : Program Instr Const) :
    p.definedLabels = p.extractLabels.map Prod.fst := by
  induction p with
  | nil => rfl
  | cons d rest ih =>
    cases d with
    | label l =>
      simp only [Program.definedLabels, List.filterMap_cons, Program.extractLabels, List.map_cons]
      exact congrArg (l :: ·) ih
    | instr _ | byteArray _ | word _ _ | align _ _ =>
      simp only [Program.definedLabels, List.filterMap_cons, Program.extractLabels,
        List.map_map, Function.comp_def]
      exact ih

theorem Program.extractLabels_le (p : Program Instr Const) :
    ∀ x ∈ p.extractLabels, x.2 ≤ p.stripLabels.length := by
  induction p with
  | nil => simp
  | cons d rest ih =>
    cases d with
    | label l =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Nat.zero_le _
      · exact ih x hx'
    | instr _ | byteArray _ | word _ _ | align _ _ =>
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact Nat.succ_le_succ (ih y hy)

/-! ## Sized Directives Address Map & Strict Positivity Invariants -/

abbrev Directives.size (ds : List (Sized (Directive Instr Const))) : Nat :=
  (ds.map (·.size)).sum

@[simp] theorem Directives.size_nil :
    Directives.size ([] : List (Sized (Directive Instr Const))) = 0 := rfl

@[simp] theorem Directives.size_cons (c : Sized (Directive Instr Const))
    (cs : List (Sized (Directive Instr Const))) :
    Directives.size (c :: cs) = c.size + Directives.size cs := rfl

@[simp] theorem Directives.size_append (xs ys : List (Sized (Directive Instr Const))) :
    Directives.size (xs ++ ys) = Directives.size xs + Directives.size ys := by
  simp [Directives.size]

@[grind hom] theorem Int64.toBitVec_ofNat_grind (a : Nat) :
    (Int64.ofNat a).toBitVec = OfNat.ofNat a := by
  rw [Int64.toBitVec_ofNat']; rfl

/-- Pair each sized directive with its resolved 64-bit start address. -/
def Directives.withAddresses (a : Int64) :
    List (Sized (Directive Instr Const)) → List (Addressable (Directive Instr Const))
  | [] => []
  | c :: cs => { c with addr := a } :: withAddresses (a + .ofNat c.size) cs

theorem Directives.withAddresses_append (a : Int64) (xs ys : List (Sized (Directive Instr Const))) :
    Directives.withAddresses a (xs ++ ys) =
      Directives.withAddresses a xs ++
        Directives.withAddresses (a + .ofNat (Directives.size xs)) ys := by
  induction xs generalizing a with
  | nil => simp [withAddresses]
  | cons c cs ih =>
    simp only [List.cons_append, withAddresses, size_cons, Int64.ofNat_add]
    rw [← Int64.add_assoc]
    congr 1
    exact ih (a + .ofNat c.size)

theorem Directives.withAddresses_map_toSized (a : Int64) (xs : List (Sized (Directive Instr Const))) :
    (Directives.withAddresses a xs).map (·.toSized) = xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons c cs ih => simp [withAddresses, ih]

/-- Every entry in `Directives.withAddresses a xs` (with strictly positive sizes) sits at `a + off`
with `off < Directives.size xs`. -/
theorem Directives.mem_withAddresses_offset {a : Int64} {xs : List (Sized (Directive Instr Const))}
    (hpos : ∀ c ∈ xs, 0 < c.size)
    {x : Addressable (Directive Instr Const)} (hx : x ∈ Directives.withAddresses a xs) :
    ∃ off : Nat, off < Directives.size xs ∧ x.addr = a + .ofNat off := by
  induction xs generalizing a with
  | nil => simp [withAddresses] at hx
  | cons c cs ih =>
    simp only [withAddresses, List.mem_cons] at hx
    have hc : 0 < c.size := hpos c List.mem_cons_self
    have hcs : ∀ c' ∈ cs, 0 < c'.size := fun c' hc' => hpos c' (List.mem_cons_of_mem _ hc')
    rcases hx with rfl | hx'
    · exact ⟨0, Nat.lt_of_lt_of_le hc (Nat.le_add_right _ _), by simp⟩
    · obtain ⟨off, hoff, haddr⟩ := ih hcs hx'
      refine ⟨c.size + off, by simp; omega, ?_⟩
      rw [haddr, Int64.ofNat_add, Int64.add_assoc]

/-- Unique directive (if any) starting at address `pc`. Because every entry in an `Executable`
has `0 < size`, at most one directive occupies `pc` whenever `Directives.size ds < 2 ^ 64`. -/
def Directives.at? (a : Int64) (ds : List (Sized (Directive Instr Const))) (pc : Int64) :
    Option (Sized (Directive Instr Const)) :=
  (Directives.withAddresses a ds).findSome? fun d => if d.addr == pc then some d.toSized else none

private theorem findSome?_eq_some_mem {α β : Type} {f : α → Option β} {xs : List α} {b : β}
    (h : xs.findSome? f = some b) : ∃ x ∈ xs, f x = some b := by
  induction xs with
  | nil => simp at h
  | cons a rest ih =>
    simp only [List.findSome?_cons] at h
    cases ha : f a with
    | some v =>
      rw [ha] at h
      exact ⟨a, List.mem_cons_self, by simpa [ha] using h⟩
    | none =>
      rw [ha] at h
      obtain ⟨x, hx, hfx⟩ := ih h
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-- Directive lookup is preserved under arbitrary prefix/suffix embedding `Q₁ ++ P ++ Q₂`
whenever all entries have positive size and the combined size fits in 64-bit address space. -/
theorem Directives.at?_infix (a : Int64) (Q₁ P Q₂ : List (Sized (Directive Instr Const)))
    (hpos₁ : ∀ c ∈ Q₁, 0 < c.size) (hposP : ∀ c ∈ P, 0 < c.size)
    (hfit : Directives.size (Q₁ ++ P ++ Q₂) < 2 ^ 64)
    {pc : Int64} {c : Sized (Directive Instr Const)}
    (h : Directives.at? (a + .ofNat (Directives.size Q₁)) P pc = some c) :
    Directives.at? a (Q₁ ++ P ++ Q₂) pc = some c := by
  dsimp only [Directives.at?] at h ⊢
  obtain ⟨y, hy_mem, hy_some⟩ := findSome?_eq_some_mem h
  have hpc_eq : y.addr = pc := by
    split at hy_some
    · exact eq_of_beq ‹_›
    · simp at hy_some
  obtain ⟨off₂, hoff₂, hy_addr⟩ := Directives.mem_withAddresses_offset hposP hy_mem
  have hQ₁_none : (Directives.withAddresses a Q₁).findSome?
      (fun d => if d.addr == pc then some d.toSized else none) = none := by
    rw [List.findSome?_eq_none_iff]
    intro x hx
    obtain ⟨off₁, hoff₁, hx_addr⟩ := Directives.mem_withAddresses_offset hpos₁ hx
    have hne : x.addr ≠ pc := by
      intro heq
      have h1 : a + .ofNat off₁ = a + .ofNat (Directives.size Q₁ + off₂) := by
        rw [← hx_addr, heq, ← hpc_eq, hy_addr, Int64.ofNat_add, Int64.add_assoc]
      have h2 := congrArg Int64.toBitVec h1
      simp only [Int64.toBitVec_add, Int64.toBitVec_ofNat_grind] at h2
      simp only [Directives.size_append] at hfit
      bv_omega
    simp [hne]
  rw [List.append_assoc,
    Directives.withAddresses_append a Q₁ (P ++ Q₂),
    Directives.withAddresses_append (a + .ofNat (Directives.size Q₁)) P Q₂,
    List.findSome?_append, List.findSome?_append, hQ₁_none, h]
  rfl

def Executable.withAddresses (e : Executable Instr Const) : List (Addressable (Directive Instr Const)) :=
  Directives.withAddresses e.startAddr e.program

def Executable.directiveAt? (e : Executable Instr Const) (pc : Int64) :
    Option (Sized (Directive Instr Const)) :=
  Directives.at? e.startAddr e.program pc

def Executable.directivesFromAddress (e : Executable Instr Const) (a : Int64) :
    List (Sized (Directive Instr Const)) :=
  (e.withAddresses.dropWhile (·.addr ≠ a)).map (·.toSized)

theorem Executable.directivesFromStart (e : Executable Instr Const) :
    e.directivesFromAddress e.startAddr = e.program := by
  rcases e with ⟨a, xs, L, hpos⟩
  cases xs with
  | nil => rfl
  | cons c cs =>
    simp [directivesFromAddress, withAddresses, Directives.withAddresses,
      Directives.withAddresses_map_toSized]

/-! ## Layout of `Program` -/

/-- Size in bytes of a `Directive` placed at `(addr, idx)` under layout `l`. -/
def Layout.dirSize (l : Layout Instr Const) (addr : Int64) (idx : Nat) :
    Directive Instr Const → Nat
  | .instr _ => l.instrSize idx
  | .label _ => 0
  | .byteArray arr => arr.size
  | .word bytes _ => bytes
  | .align log2Align _ => alignPad addr log2Align

/-- Legacy size helper kept for `⸨dir n | ... ⸩` syntax compatibility. -/
abbrev Layout.size [l : Layout Instr Const] (d : Directive Instr Const) (idx : Nat) : Nat :=
  l.dirSize l.start idx d

/-- Emit strictly positive-size `Sized (Directive Instr Const)` entries, threading `(addr, idx)`
left-to-right. `.instr` emits directly with zero `ite` wrappers, keeping straight-line layout fast. -/
def Layout.layoutGo (l : Layout Instr Const) (addr : Int64) (idx : Nat) :
    Program Instr Const → List (Sized (Directive Instr Const))
  | [] => []
  | .instr i :: rest =>
    let sz := l.instrSize idx
    { directive := .instr i, size := sz } :: l.layoutGo (addr + .ofNat sz) (idx + 1) rest
  | d :: rest =>
    let sz := l.dirSize addr idx d
    if 0 < sz then
      { directive := d, size := sz } :: l.layoutGo (addr + .ofNat sz) (idx + 1) rest
    else
      l.layoutGo addr (idx + 1) rest

/-- Total byte size of `p` under layout `l`. -/
def Layout.totalSize (l : Layout Instr Const) (p : Program Instr Const) : Nat :=
  Directives.size (l.layoutGo l.start 0 p.stripLabels)

/-- Resolved 64-bit address of the `k`-th non-label directive (`p.stripLabels[k]?`). -/
def Layout.addrOf (l : Layout Instr Const) (p : Program Instr Const) (k : Nat) : Int64 :=
  l.start + .ofNat (Directives.size (l.layoutGo l.start 0 (p.stripLabels.take k)))

/-- Shift layout `l` by an arbitrary `(addr, idx)` offset. -/
@[instance_reducible]
def Layout.shift (l : Layout Instr Const) (addr : Int64) (idx : Nat) : Layout Instr Const where
  start := addr
  instrSize i := l.instrSize (i + idx)
  instrSize_pos i := l.instrSize_pos (i + idx)

@[simp] theorem Layout.instrSize_shift (l : Layout Instr Const) (a : Int64) (idx i : Nat) :
    @Layout.instrSize _ _ (l.shift a idx) i = l.instrSize (i + idx) := rfl

/-- Layout shifted past program `p`. -/
@[instance_reducible]
def Layout.after (l : Layout Instr Const) (p : Program Instr Const) : Layout Instr Const :=
  l.shift (l.start + .ofNat (l.totalSize p)) p.stripLabels.length

@[simp] theorem Layout.start_after (l : Layout Instr Const) (p : Program Instr Const) :
    @Layout.start _ _ (l.after p) = l.start + .ofNat (l.totalSize p) := rfl

@[simp] theorem Layout.instrSize_after (l : Layout Instr Const) (p : Program Instr Const) (i : Nat) :
    @Layout.instrSize _ _ (l.after p) i = l.instrSize (i + p.stripLabels.length) := rfl

private theorem Layout.dirSize_shift (l : Layout Instr Const) (a a' : Int64) (idx i : Nat)
    (d : Directive Instr Const) :
    (l.shift a idx).dirSize a' i d = l.dirSize a' (i + idx) d := by
  cases d <;> rfl

theorem Layout.layoutGo_pos (l : Layout Instr Const) (addr : Int64) (idx : Nat)
    (p : Program Instr Const) :
    ∀ c ∈ l.layoutGo addr idx p, 0 < c.size := by
  induction p generalizing addr idx with
  | nil => simp [layoutGo]
  | cons d rest ih =>
    cases d with
    | instr i =>
      intro c hc
      simp only [layoutGo, List.mem_cons] at hc
      rcases hc with rfl | hc'
      · exact l.instrSize_pos idx
      · exact ih _ _ c hc'
    | label _ | byteArray _ | word _ _ | align _ _ =>
      intro c hc
      simp only [layoutGo] at hc
      split at hc
      · rcases List.mem_cons.mp hc with rfl | hc'
        · assumption
        · exact ih _ _ c hc'
      · exact ih _ _ c hc

private theorem Layout.layoutGo_shift (l : Layout Instr Const) (a a' : Int64) (idx i : Nat)
    (p : Program Instr Const) :
    (l.shift a idx).layoutGo a' i p = l.layoutGo a' (i + idx) p := by
  induction p generalizing a' i with
  | nil => rfl
  | cons d rest ih =>
    cases d with
    | instr ins =>
      simp only [layoutGo, instrSize_shift]
      congr 1
      simpa [Nat.succ_add] using ih (a' + .ofNat (l.instrSize (i + idx))) (i + 1)
    | label _ | byteArray _ | word _ _ | align _ _ =>
      simp only [layoutGo, dirSize_shift]
      split
      · congr 1
        simpa [Nat.succ_add] using ih _ (i + 1)
      · simpa [Nat.succ_add] using ih a' (i + 1)

private theorem Layout.layoutGo_singleton_size (l : Layout Instr Const) (addr : Int64) (idx : Nat)
    (d : Directive Instr Const) :
    Directives.size (l.layoutGo addr idx [d]) = l.dirSize addr idx d := by
  cases d with
  | instr i => simp [layoutGo, dirSize]
  | label _ | byteArray _ | word _ _ | align _ _ =>
    simp only [layoutGo]
    split
    · simp
    · simp only [Directives.size, List.map_nil, List.sum_nil]; omega

private theorem Layout.layoutGo_append (l : Layout Instr Const) (addr : Int64) (idx : Nat)
    (p q : Program Instr Const) :
    l.layoutGo addr idx (p ++ q) =
      l.layoutGo addr idx p ++
        l.layoutGo (addr + .ofNat (Directives.size (l.layoutGo addr idx p))) (idx + p.length) q := by
  induction p generalizing addr idx with
  | nil => simp [layoutGo]
  | cons d rest ih =>
    have hidx : idx + 1 + rest.length = idx + (rest.length + 1) := by omega
    have hstep (sz : Nat) (xs : List (Sized (Directive Instr Const))) :
        addr + .ofNat sz + .ofNat (Directives.size xs) =
          addr + .ofNat (sz + Directives.size xs) := by
      rw [Int64.ofNat_add, Int64.add_assoc]
    cases d with
    | instr i =>
      simp only [List.cons_append, layoutGo, List.length_cons, Directives.size_cons]
      congr 1
      rw [ih, hstep, hidx]
    | label _ | byteArray _ | word _ _ | align _ _ =>
      simp only [List.cons_append, layoutGo, List.length_cons]
      split
      · simp only [List.cons_append, Directives.size_cons]
        congr 1
        rw [ih, hstep, hidx]
      · rw [ih, hidx]

/-- Lay out a `Program` into an `Executable` (stripping `.label` and zero-size directives). -/
def Layout.apply (l : Layout Instr Const) (p : Program Instr Const) : Executable Instr Const :=
  { startAddr := l.start
    program := l.layoutGo l.start 0 p.stripLabels
    labels := { label? lbl := (p.extractLabels.lookup lbl).map (l.addrOf p) }
    program_pos := l.layoutGo_pos l.start 0 p.stripLabels }

-- NOTE: We write `List (Kraken.Directive Instr Const)` here, and not `Kraken.Program Instr Const`,
-- so Lean's typeclass synthesis matches architecture-specific `Program := List Directive`.
instance : CoeFun (Layout Instr Const) (fun _ => List (Directive Instr Const) → Executable Instr Const) where
  coe := Layout.apply

@[simp] theorem Layout.apply_startAddr (l : Layout Instr Const) (p : Program Instr Const) :
    (l p).startAddr = l.start := rfl

@[simp] theorem Layout.directives_size_apply (l : Layout Instr Const) (p : Program Instr Const) :
    Directives.size (l p).program = l.totalSize p := rfl

theorem Layout.directivesFromStart [l : Layout Instr Const] (p : Program Instr Const) :
    (l p).directivesFromAddress l.start = l.layoutGo l.start 0 p.stripLabels :=
  Executable.directivesFromStart (l p)

theorem Layout.apply_program_append (l : Layout Instr Const) (p q : Program Instr Const) :
    (l (p ++ q)).program = (l p).program ++ ((l.after p) q).program := by
  dsimp only [Layout.apply]
  rw [Program.stripLabels_append, l.layoutGo_append, start_after]
  congr 1
  exact (l.layoutGo_shift (l.start + .ofNat (l.totalSize p))
    (l.start + .ofNat (l.totalSize p)) p.stripLabels.length 0 q.stripLabels).symm

theorem Layout.totalSize_append (l : Layout Instr Const) (p q : Program Instr Const) :
    l.totalSize (p ++ q) = l.totalSize p + (l.after p).totalSize q := by
  simpa only [directives_size_apply, Directives.size_append] using
    congrArg Directives.size (l.apply_program_append p q)

@[simp] theorem Layout.after_nil (l : Layout Instr Const) : l.after [] = l := by
  rcases l with ⟨s, sz, hpos⟩
  simp [Layout.after, Layout.shift, Layout.totalSize, Layout.layoutGo]

theorem Layout.after_append (l : Layout Instr Const) (p q : Program Instr Const) :
    l.after (p ++ q) = (l.after p).after q := by
  rcases l with ⟨s, sz, hpos⟩
  simp only [Layout.after, Layout.shift, Program.stripLabels_append, Layout.totalSize_append,
    List.length_append, start_after]
  congr 1
  · rw [Int64.ofNat_add, ← Int64.add_assoc]
  · funext i; congr 1; omega

theorem Layout.size_left_lt (l : Layout Instr Const) {p q : Program Instr Const}
    (h : l.totalSize (p ++ q) < 2 ^ 64) :
    l.totalSize p < 2 ^ 64 := by
  rw [l.totalSize_append] at h; omega

theorem Layout.size_after_lt (l : Layout Instr Const) {p q : Program Instr Const}
    (h : l.totalSize (p ++ q) < 2 ^ 64) :
    (l.after p).totalSize q < 2 ^ 64 := by
  rw [l.totalSize_append] at h; omega

@[simp] theorem Layout.addrOf_zero (l : Layout Instr Const) (p : Program Instr Const) :
    l.addrOf p 0 = l.start := by
  simp [addrOf, layoutGo]

@[simp] theorem Layout.addrOf_length (l : Layout Instr Const) (p : Program Instr Const) :
    l.addrOf p p.stripLabels.length = @Layout.start _ _ (l.after p) := by
  simp [addrOf, totalSize]

theorem Layout.addrOf_infix (l : Layout Instr Const) (q₁ p q₂ : Program Instr Const)
    {k : Nat} (hk : k ≤ p.stripLabels.length) :
    l.addrOf (q₁ ++ p ++ q₂) (q₁.stripLabels.length + k) = (l.after q₁).addrOf p k := by
  have htake : (q₁ ++ p ++ q₂).stripLabels.take (q₁.stripLabels.length + k) =
      q₁.stripLabels ++ p.stripLabels.take k := by
    rw [Program.stripLabels_append, Program.stripLabels_append, List.append_assoc,
      List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.take_append_of_le_length hk]
  dsimp only [addrOf]
  rw [htake, l.layoutGo_append, Directives.size_append, Int64.ofNat_add, ← Int64.add_assoc,
    start_after]
  congr 2
  exact congrArg Directives.size
    (l.layoutGo_shift (l.start + .ofNat (l.totalSize q₁))
      (l.start + .ofNat (l.totalSize q₁)) q₁.stripLabels.length 0 (p.stripLabels.take k)).symm

theorem Layout.addrOf_succ (l : Layout Instr Const) (p : Program Instr Const)
    {k : Nat} {d : Directive Instr Const} (hd : p.stripLabels[k]? = some d) :
    l.addrOf p (k + 1) =
      l.addrOf p k + .ofNat (l.dirSize (l.addrOf p k) k d) := by
  have hlt : k < p.stripLabels.length := (List.getElem?_eq_some_iff.mp hd).1
  have hlen : (p.stripLabels.take k).length = k := List.length_take_of_le (Nat.le_of_lt hlt)
  have htake : p.stripLabels.take (k + 1) = p.stripLabels.take k ++ [d] := by
    rw [List.take_add_one, hd, Option.toList_some]
  dsimp only [addrOf]
  rw [htake, l.layoutGo_append, Directives.size_append, Int64.ofNat_add, ← Int64.add_assoc,
    Nat.zero_add, hlen, l.layoutGo_singleton_size]

/-- After stepping past `.align log2Align`, the resulting address is aligned to `2 ^ log2Align` bytes. -/
theorem Layout.addrOf_align (l : Layout Instr Const) (p : Program Instr Const)
    {k log2Align : Nat} {ex : Bool} (hd : p.stripLabels[k]? = some (.align log2Align ex))
    (hle : log2Align ≤ 64) :
    (l.addrOf p (k + 1)).toUInt64.toNat % 2 ^ log2Align = 0 := by
  rw [l.addrOf_succ p hd]
  exact alignPad_aligned (l.addrOf p k) hle

/-- Single-directive lookup in a laid-out program whenever the `k`-th non-label directive
has positive size. -/
theorem Layout.directiveAt?_addrOf (l : Layout Instr Const) (p : Program Instr Const)
    (hfit : l.totalSize p < 2 ^ 64)
    {k : Nat} {d : Directive Instr Const} (hd : p.stripLabels[k]? = some d)
    (hpos : 0 < l.dirSize (l.addrOf p k) k d) :
    (l p).directiveAt? (l.addrOf p k) =
      some { directive := d, size := l.dirSize (l.addrOf p k) k d } := by
  have hlt : k < p.stripLabels.length := (List.getElem?_eq_some_iff.mp hd).1
  have hlen : (p.stripLabels.take k).length = k := List.length_take_of_le (Nat.le_of_lt hlt)
  have hsplit : p.stripLabels = p.stripLabels.take k ++ [d] ++ p.stripLabels.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append]
    have hdrop : p.stripLabels.drop k = d :: p.stripLabels.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      simp [(List.getElem?_eq_some_iff.mp hd).2]
    rw [← hdrop, List.take_append_drop]
  have hprog : (l p).program =
      l.layoutGo l.start 0 (p.stripLabels.take k) ++
        l.layoutGo (l.addrOf p k) k [d] ++
        l.layoutGo (l.addrOf p k + .ofNat (Directives.size (l.layoutGo (l.addrOf p k) k [d])))
          (k + 1) (p.stripLabels.drop (k + 1)) := by
    change l.layoutGo l.start 0 p.stripLabels = _
    conv => lhs; rw [hsplit]
    rw [l.layoutGo_append, l.layoutGo_append]
    simp only [addrOf, List.length_append, List.length_singleton, Nat.zero_add, hlen,
      Directives.size_append, Int64.ofNat_add, Int64.add_assoc]
  have hsingle : l.layoutGo (l.addrOf p k) k [d] =
      [{ directive := d, size := l.dirSize (l.addrOf p k) k d }] := by
    cases d with
    | instr i => rfl
    | label _ | byteArray _ | word _ _ | align _ _ =>
      simp only [layoutGo, hpos, ↓reduceIte]
  have hfit' : Directives.size
      (l.layoutGo l.start 0 (p.stripLabels.take k) ++
        l.layoutGo (l.addrOf p k) k [d] ++
        l.layoutGo (l.addrOf p k + .ofNat (Directives.size (l.layoutGo (l.addrOf p k) k [d])))
          (k + 1) (p.stripLabels.drop (k + 1))) < 2 ^ 64 := by
    rw [← hprog]
    exact hfit
  dsimp only [Executable.directiveAt?, Layout.apply]
  change Directives.at? l.start (l p).program (l.addrOf p k) = _
  rw [hprog]
  refine Directives.at?_infix l.start _ _ _
    (l.layoutGo_pos _ _ _) (l.layoutGo_pos _ _ _) hfit' ?_
  change Directives.at? (l.addrOf p k) (l.layoutGo (l.addrOf p k) k [d]) (l.addrOf p k) = _
  rw [hsingle]
  simp [Directives.at?, Directives.withAddresses]

theorem Layout.directiveAt?_infix (l : Layout Instr Const) (q₁ p q₂ : Program Instr Const)
    (hfit : l.totalSize (q₁ ++ p ++ q₂) < 2 ^ 64)
    {pc : Int64} {c : Sized (Directive Instr Const)}
    (h : ((l.after q₁) p).directiveAt? pc = some c) :
    (l (q₁ ++ p ++ q₂)).directiveAt? pc = some c := by
  have hprog : (l (q₁ ++ p ++ q₂)).program =
      (l q₁).program ++ ((l.after q₁) p).program ++ ((l.after (q₁ ++ p)) q₂).program := by
    rw [l.apply_program_append, l.apply_program_append]
  have hfit' : Directives.size
      ((l q₁).program ++ ((l.after q₁) p).program ++ ((l.after (q₁ ++ p)) q₂).program) < 2 ^ 64 := by
    rw [← hprog]
    exact hfit
  dsimp only [Executable.directiveAt?] at h ⊢
  rw [apply_startAddr, hprog]
  exact Directives.at?_infix l.start (l q₁).program ((l.after q₁) p).program
    ((l.after (q₁ ++ p)) q₂).program (l q₁).program_pos ((l.after q₁) p).program_pos hfit' h

/-! ## Label Resolution & Concatenation Monotonicity -/

private theorem lookup_eq_none_of_not_mem_map_fst {α : Type} {xs : List (Label × α)} {lbl : Label}
    (h : lbl ∉ xs.map Prod.fst) : xs.lookup lbl = none := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : (lbl == hd.1) = false := beq_false_of_ne h.1
    simp [List.lookup, hne, ih h.2]

private theorem lookup_append_eq_or {α : Type} (xs ys : List (Label × α)) (lbl : Label) :
    (xs ++ ys).lookup lbl = (xs.lookup lbl).or (ys.lookup lbl) := by
  induction xs with
  | nil => simp [List.lookup]
  | cons hd tl ih =>
    simp only [List.cons_append, List.lookup]
    cases lbl == hd.1 <;> simp [ih]

private theorem lookup_map_snd {α β : Type} (f : α → β) (xs : List (Label × α)) (lbl : Label) :
    (xs.map fun (l, v) => (l, f v)).lookup lbl = (xs.lookup lbl).map f := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.lookup]
    cases lbl == hd.1 <;> simp [ih]

private theorem mem_of_lookup_eq_some {α : Type} {xs : List (Label × α)} {lbl : Label} {v : α}
    (h : xs.lookup lbl = some v) : (lbl, v) ∈ xs := by
  induction xs with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    simp only [List.lookup] at h
    cases heq : lbl == hd.1
    · simp [heq] at h
      exact List.mem_cons_of_mem _ (ih h)
    · simp [heq] at h
      rcases hd with ⟨l', v'⟩
      have hl : lbl = l' := eq_of_beq heq
      subst hl; subst h
      exact List.mem_cons_self

theorem Layout.label?_eq_some_addrOf [l : Layout Instr Const] (p : Program Instr Const)
    (lbl : Label) {k : Nat} (hk : p.extractLabels.lookup lbl = some k) :
    (l p).labels.label? lbl = some (l.addrOf p k) := by
  simp [Layout.apply, hk]

theorem Layout.label!_eq_addrOf [l : Layout Instr Const] (p : Program Instr Const)
    (lbl : Label) {k : Nat} (hk : p.extractLabels.lookup lbl = some k) :
    (l p).labels.label! lbl = l.addrOf p k := by
  simp [Labels.label!, Layout.label?_eq_some_addrOf p lbl hk]

theorem Layout.labels_sub_infix (l : Layout Instr Const) (q₁ p q₂ : Program Instr Const)
    (hdisj : ∀ lbl ∈ q₁.definedLabels, lbl ∉ p.definedLabels) :
    ((l.after q₁) p).labels ⊆ (l (q₁ ++ p ++ q₂)).labels := by
  intro lbl a h
  simp only [Layout.apply] at h ⊢
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
  have hk_mem : (lbl, k) ∈ p.extractLabels := mem_of_lookup_eq_some hk
  have hk_le : k ≤ p.stripLabels.length := p.extractLabels_le _ hk_mem
  have hnot_q₁ : lbl ∉ q₁.extractLabels.map Prod.fst := by
    rw [← q₁.definedLabels_eq_map_fst]
    intro hmem
    exact hdisj lbl hmem (by
      rw [p.definedLabels_eq_map_fst]
      exact List.mem_map.mpr ⟨(lbl, k), hk_mem, rfl⟩)
  have hq₁_none : q₁.extractLabels.lookup lbl = none :=
    lookup_eq_none_of_not_mem_map_fst hnot_q₁
  rw [Program.extractLabels_append, Program.extractLabels_append,
    lookup_append_eq_or, lookup_append_eq_or, hq₁_none, Option.none_or,
    lookup_map_snd, hk]
  simp only [Option.map_some, Option.some_or]
  congr 1
  exact l.addrOf_infix q₁ p q₂ hk_le

theorem Layout.labels_sub_append_right (l : Layout Instr Const) (p q : Program Instr Const) :
    (l p).labels ⊆ (l (p ++ q)).labels := by
  simpa using l.labels_sub_infix [] p q nofun

theorem Layout.labels_sub_append_left (l : Layout Instr Const) (q p : Program Instr Const)
    (hdisj : ∀ lbl ∈ q.definedLabels, lbl ∉ p.definedLabels) :
    ((l.after q) p).labels ⊆ (l (q ++ p)).labels := by
  simpa using l.labels_sub_infix q p [] hdisj

/-! ## `bedrock2`-Style Function Specifications (`SpecOf`, `FnSpec`) -/

/-- `bedrock2`-style `spec_of`: associates a function label `fn` with a specification
over the ambient executable `Executable Instr Const → Prop`. -/
class SpecOf (Instr Const : Type) (fn : Label) where
  spec : Executable Instr Const → Prop

instance {fn : Label} : CoeFun (SpecOf Instr Const fn) (fun _ => Executable Instr Const → Prop) :=
  ⟨fun s => s.spec⟩

/-- Named-function specification wrapper: `fn` resolves to some `entry` in `e.labels`
satisfying `contract entry`. -/
def FnSpec (e : Executable Instr Const) (fn : Label) (contract : Int64 → Prop) : Prop :=
  ∃ entry, e.labels.label? fn = some entry ∧ contract entry

theorem FnSpec.mono {e : Executable Instr Const} {fn : Label} {P Q : Int64 → Prop}
    (hPQ : ∀ a, P a → Q a) (h : FnSpec e fn P) : FnSpec e fn Q := by
  obtain ⟨entry, hlbl, hp⟩ := h
  exact ⟨entry, hlbl, hPQ entry hp⟩

/-- Lift a family of measure-indexed `FnSpec`s (e.g. from recursive/mutually-recursive induction)
into a single `FnSpec` whose `entry` is resolved once outside `∀ n`. -/
theorem FnSpec.forall_nat {e : Executable Instr Const} {fn : Label} {P : Nat → Int64 → Prop}
    (h : ∀ n, FnSpec e fn (P n)) :
    FnSpec e fn (fun entry => ∀ n, P n entry) := by
  obtain ⟨entry, hlbl, _⟩ := h 0
  refine ⟨entry, hlbl, fun n => ?_⟩
  obtain ⟨entry', hlbl', hp⟩ := h n
  cases hlbl.symm.trans hlbl'
  exact hp

/-- Instantiate a `FnSpec` on a concrete program `l p` at the known label index `k` of `fn`. -/
theorem FnSpec.at_label [l : Layout Instr Const]
    {p : Program Instr Const} {fn : Label} {k : Nat}
    (hk : p.extractLabels.lookup fn = some k)
    {contract : Int64 → Prop}
    (h : FnSpec (l p) fn contract) :
    contract (l.addrOf p k) := by
  obtain ⟨entry, hentry, hc⟩ := h
  have hk' := l.label?_eq_some_addrOf p fn hk
  cases hentry.symm.trans hk'
  exact hc

end Kraken

export Kraken (Labels FnSpec alignPad)
