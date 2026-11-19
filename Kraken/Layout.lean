module

public import Lean.ToExpr

@[expose] public section

/-
Common Kraken executable layout, label splitting, dynamic alignment, and function-spec primitives.

Architecture:
1. Surface AST: `Program := List (Directive Instr Const)` retains inline `.label` and `.align`.
2. Pure syntactic preprocessing: `Program.splitLabels` splits a `Program` into
   - `body : List (CodeDirective Instr Const)` (directives sans `.label`), and
   - `labels : List (Label × Nat)` (each label mapped to its index `0 ≤ idx ≤ body.length`).
3. Layout (`Layout.apply`): threads the current address left-to-right over `body`, resolving
   dynamic `.align` padding (`alignPad curAddr log2Align`) and emitting only strictly positive-size
   `SizedItem`s into `Executable.items`, alongside the resolved `Executable.labels : Labels`.
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

/-! ## Surface AST (`Directive`, `Program`) and Label Splitting (`CodeDirective`, `SplitProgram`) -/

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

structure Sized Directive where
  directive : Directive
  size : Nat

structure Addressable (Directive : Type) extends Sized Directive where
  addr : Int64

abbrev Program Instr Const := List (Directive Instr Const)

/-- A directive after stripping `.label` entries out of a `Program`. -/
inductive CodeDirective (Instr Const : Type) where
  | instr (_ : Instr)
  | byteArray (arr : ByteArray)
  | word (bytes : Nat) (e : Const)
  | align (log2Align : Nat) (executable : Bool := true)
  deriving DecidableEq, Repr, Hashable, BEq, Lean.ToExpr

/-- A `Program` preprocessed into label-free `body` and `(label, bodyIdx)` table (`0 ≤ idx ≤ body.length`). -/
structure SplitProgram (Instr Const : Type) where
  body : List (CodeDirective Instr Const)
  labels : List (Label × Nat)
  deriving DecidableEq, Repr

/-- An emitted machine-level item occupying a strictly positive number of bytes in `Executable`. -/
inductive Item (Instr Const : Type) where
  | instr (_ : Instr)
  | byteArray (arr : ByteArray)
  | word (bytes : Nat) (e : Const)
  /-- Non-zero alignment padding emitted by `.align`. -/
  | alignPad (executable : Bool)
  deriving DecidableEq, Repr, Hashable, BEq, Lean.ToExpr

structure SizedItem (Instr Const : Type) where
  item : Item Instr Const
  size : Nat
  size_pos : 0 < size

structure Executable (Instr Const : Type) where
  startAddr : Int64
  items : List (SizedItem Instr Const)
  labels : Labels

class Layout (Instr Const : Type) where
  start : Int64
  instrSize : Nat → Nat
  instrSize_pos : ∀ i, 0 < instrSize i

variable {Instr Const : Type}

def CodeDirective.toItem : CodeDirective Instr Const → Item Instr Const
  | .instr i => .instr i
  | .byteArray bs => .byteArray bs
  | .word n c => .word n c
  | .align _ ex => .alignPad ex

def Directive.isLabel (lbl : Label) : Directive Instr Const → Bool
  | .label l => l == lbl
  | _ => false

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

/-- Preprocess a `Program` (`List Directive`) into label-free `CodeDirective`s and a `(label, idx)` table. -/
def Program.splitLabels : Program Instr Const → SplitProgram Instr Const
  | [] => ⟨[], []⟩
  | .label l :: rest =>
    let sp := splitLabels rest
    ⟨sp.body, (l, 0) :: sp.labels⟩
  | .instr i :: rest =>
    let sp := splitLabels rest
    ⟨.instr i :: sp.body, sp.labels.map fun (l, idx) => (l, idx + 1)⟩
  | .byteArray bs :: rest =>
    let sp := splitLabels rest
    ⟨.byteArray bs :: sp.body, sp.labels.map fun (l, idx) => (l, idx + 1)⟩
  | .word n c :: rest =>
    let sp := splitLabels rest
    ⟨.word n c :: sp.body, sp.labels.map fun (l, idx) => (l, idx + 1)⟩
  | .align k ex :: rest =>
    let sp := splitLabels rest
    ⟨.align k ex :: sp.body, sp.labels.map fun (l, idx) => (l, idx + 1)⟩

abbrev _root_.List.splitLabels (p : List (Directive Instr Const)) : SplitProgram Instr Const :=
  Program.splitLabels p

@[simp] theorem Program.splitLabels_nil :
    Program.splitLabels ([] : Program Instr Const) = ⟨[], []⟩ := rfl

@[simp] theorem Program.splitLabels_cons_label (l : Label) (rest : Program Instr Const) :
    Program.splitLabels (.label l :: rest) =
      ⟨(Program.splitLabels rest).body, (l, 0) :: (Program.splitLabels rest).labels⟩ := rfl

@[simp] theorem Program.splitLabels_cons_instr (i : Instr) (rest : Program Instr Const) :
    Program.splitLabels (.instr i :: rest) =
      ⟨.instr i :: (Program.splitLabels rest).body,
       (Program.splitLabels rest).labels.map fun (l, idx) => (l, idx + 1)⟩ := rfl

@[simp] theorem Program.splitLabels_cons_byteArray (bs : ByteArray) (rest : Program Instr Const) :
    Program.splitLabels (.byteArray bs :: rest) =
      ⟨.byteArray bs :: (Program.splitLabels rest).body,
       (Program.splitLabels rest).labels.map fun (l, idx) => (l, idx + 1)⟩ := rfl

@[simp] theorem Program.splitLabels_cons_word (n : Nat) (c : Const) (rest : Program Instr Const) :
    Program.splitLabels (.word n c :: rest) =
      ⟨.word n c :: (Program.splitLabels rest).body,
       (Program.splitLabels rest).labels.map fun (l, idx) => (l, idx + 1)⟩ := rfl

@[simp] theorem Program.splitLabels_cons_align (k : Nat) (ex : Bool) (rest : Program Instr Const) :
    Program.splitLabels (.align k ex :: rest) =
      ⟨.align k ex :: (Program.splitLabels rest).body,
       (Program.splitLabels rest).labels.map fun (l, idx) => (l, idx + 1)⟩ := rfl

@[simp] theorem Program.splitLabels_body_append (p q : Program Instr Const) :
    (Program.splitLabels (p ++ q)).body =
      (Program.splitLabels p).body ++ (Program.splitLabels q).body := by
  induction p with
  | nil => rfl
  | cons d rest ih =>
    cases d <;> simp [ih]

@[simp] theorem Program.splitLabels_labels_append (p q : Program Instr Const) :
    (Program.splitLabels (p ++ q)).labels =
      (Program.splitLabels p).labels ++
      (Program.splitLabels q).labels.map fun (l, idx) => (l, (Program.splitLabels p).body.length + idx) := by
  induction p with
  | nil => simp
  | cons d rest ih =>
    cases d <;> simp [ih, List.map_append, List.map_map, Function.comp_def] <;> omega

theorem Program.definedLabels_eq_map_fst (p : Program Instr Const) :
    p.definedLabels = (Program.splitLabels p).labels.map Prod.fst := by
  induction p with
  | nil => rfl
  | cons d rest ih =>
    cases d with
    | label l =>
      simp only [Program.definedLabels, List.filterMap_cons, splitLabels_cons_label, List.map_cons]
      exact congrArg (l :: ·) ih
    | instr _ | byteArray _ | word _ _ | align _ _ =>
      simp only [Program.definedLabels, List.filterMap_cons, splitLabels_cons_instr,
        splitLabels_cons_byteArray, splitLabels_cons_word, splitLabels_cons_align,
        List.map_map, Function.comp_def]
      exact ih

theorem Program.splitLabels_labels_le (p : Program Instr Const) :
    ∀ x ∈ (Program.splitLabels p).labels, x.2 ≤ (Program.splitLabels p).body.length := by
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

/-! ## `Items` Address Map & Strict Positivity Invariants -/

abbrev Items.totalSize (xs : List (SizedItem Instr Const)) : Nat :=
  (xs.map (·.size)).sum

@[simp] theorem Items.totalSize_nil : Items.totalSize ([] : List (SizedItem Instr Const)) = 0 := rfl

@[simp] theorem Items.totalSize_cons (c : SizedItem Instr Const) (cs : List (SizedItem Instr Const)) :
    Items.totalSize (c :: cs) = c.size + Items.totalSize cs := rfl

@[simp] theorem Items.totalSize_append (xs ys : List (SizedItem Instr Const)) :
    Items.totalSize (xs ++ ys) = Items.totalSize xs + Items.totalSize ys := by
  simp [Items.totalSize]

@[grind hom] theorem Int64.toBitVec_ofNat_grind (a : Nat) :
    (Int64.ofNat a).toBitVec = OfNat.ofNat a := by
  rw [Int64.toBitVec_ofNat']; rfl

/-- Pair each emitted `SizedItem` with its resolved 64-bit start address. -/
def Executable.withAddresses (e : Executable Instr Const) : List (SizedItem Instr Const × Int64) :=
  go e.startAddr e.items
where
  go (a : Int64) : List (SizedItem Instr Const) → List (SizedItem Instr Const × Int64)
    | [] => []
    | c :: cs => (c, a) :: go (a + .ofNat c.size) cs

@[simp] theorem Executable.withAddresses_nil (a : Int64) (L : Labels) :
    Executable.withAddresses (Instr := Instr) (Const := Const) ⟨a, [], L⟩ = [] := rfl

@[simp] theorem Executable.withAddresses_cons (a : Int64) (c : SizedItem Instr Const)
    (cs : List (SizedItem Instr Const)) (L : Labels) :
    Executable.withAddresses ⟨a, c :: cs, L⟩ =
      (c, a) :: Executable.withAddresses ⟨a + .ofNat c.size, cs, L⟩ := rfl

theorem Executable.withAddresses_labels_irrel (a : Int64) (xs : List (SizedItem Instr Const)) (L₁ L₂ : Labels) :
    Executable.withAddresses ⟨a, xs, L₁⟩ = Executable.withAddresses ⟨a, xs, L₂⟩ := rfl

theorem Executable.withAddresses_append (a : Int64) (xs ys : List (SizedItem Instr Const)) (L L₁ L₂ : Labels) :
    Executable.withAddresses ⟨a, xs ++ ys, L⟩ =
      Executable.withAddresses ⟨a, xs, L₁⟩ ++
        Executable.withAddresses ⟨a + .ofNat (Items.totalSize xs), ys, L₂⟩ := by
  induction xs generalizing a with
  | nil =>
    simp only [List.nil_append, withAddresses_nil, Items.totalSize_nil, Int64.reduceOfNat, Int64.add_zero]
    rfl
  | cons c cs ih =>
    simp only [List.cons_append, withAddresses_cons, Items.totalSize_cons, Int64.ofNat_add]
    rw [← Int64.add_assoc]
    congr 1
    exact ih (a + .ofNat c.size)

/-- Unique item (if any) starting at address `a`. Because every `SizedItem` has `0 < size`,
at most one item can occupy address `a` whenever `Items.totalSize e.items < 2 ^ 64`. -/
def Executable.itemAt? (e : Executable Instr Const) (a : Int64) : Option (SizedItem Instr Const) :=
  e.withAddresses.findSome? fun (c, addr) => if addr == a then some c else none

/-- All emitted items starting from address `a` onward (for straight-line execution). -/
def Executable.itemsFromAddress (e : Executable Instr Const) (a : Int64) : List (SizedItem Instr Const) :=
  (e.withAddresses.dropWhile (·.2 ≠ a)).map Prod.fst

theorem Executable.withAddresses_map_fst (a : Int64) (xs : List (SizedItem Instr Const)) (L : Labels) :
    (Executable.withAddresses ⟨a, xs, L⟩).map Prod.fst = xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons c cs ih => simp [ih]

theorem Executable.itemsFromStart (e : Executable Instr Const) :
    e.itemsFromAddress e.startAddr = e.items := by
  rcases e with ⟨a, xs, L⟩
  cases xs with
  | nil => rfl
  | cons c cs =>
    simp [itemsFromAddress, withAddresses_map_fst]

/-- Every entry `(c, addr)` in `withAddresses ⟨a, xs, L⟩` sits at `a + off` with `off < Items.totalSize xs`. -/
theorem Executable.mem_withAddresses_offset {a : Int64} {xs : List (SizedItem Instr Const)} {L : Labels}
    {x : SizedItem Instr Const × Int64} (hx : x ∈ Executable.withAddresses ⟨a, xs, L⟩) :
    ∃ off : Nat, off < Items.totalSize xs ∧ x.2 = a + .ofNat off := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons c cs ih =>
    simp only [withAddresses_cons, List.mem_cons] at hx
    rcases hx with rfl | hx'
    · exact ⟨0, Nat.lt_of_lt_of_le c.size_pos (Nat.le_add_right _ _), by simp⟩
    · obtain ⟨off, hoff, haddr⟩ := ih hx'
      refine ⟨c.size + off, by simp; omega, ?_⟩
      rw [haddr, Int64.ofNat_add, Int64.add_assoc]

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

/-- Item lookup is preserved under arbitrary prefix/suffix embedding `Q₁ ++ P ++ Q₂`
whenever the combined executable fits in 64-bit address space (`< 2 ^ 64`). -/
theorem Executable.itemAt?_infix (a : Int64) (Q₁ P Q₂ : List (SizedItem Instr Const)) (L₁ L₂ : Labels)
    (hfit : Items.totalSize (Q₁ ++ P ++ Q₂) < 2 ^ 64)
    {pc : Int64} {c : SizedItem Instr Const}
    (h : ({ startAddr := a + .ofNat (Items.totalSize Q₁), items := P, labels := L₁ } :
        Executable Instr Const).itemAt? pc = some c) :
    ({ startAddr := a, items := Q₁ ++ P ++ Q₂, labels := L₂ } :
        Executable Instr Const).itemAt? pc = some c := by
  dsimp only [Executable.itemAt?] at h ⊢
  obtain ⟨y, hy_mem, hy_some⟩ := findSome?_eq_some_mem h
  have hpc_eq : y.2 = pc := by
    split at hy_some
    · exact eq_of_beq ‹_›
    · simp at hy_some
  obtain ⟨off₂, hoff₂, hy_addr⟩ := Executable.mem_withAddresses_offset hy_mem
  have hQ₁_none : (Executable.withAddresses ⟨a, Q₁, L₂⟩).findSome?
      (fun (x : SizedItem Instr Const × Int64) => if x.2 == pc then some x.1 else none) = none := by
    rw [List.findSome?_eq_none_iff]
    intro x hx
    obtain ⟨off₁, hoff₁, hx_addr⟩ := Executable.mem_withAddresses_offset hx
    have hne : x.2 ≠ pc := by
      intro heq
      have h1 : a + .ofNat off₁ = a + .ofNat (Items.totalSize Q₁ + off₂) := by
        rw [← hx_addr, heq, ← hpc_eq, hy_addr, Int64.ofNat_add, Int64.add_assoc]
      have h2 := congrArg Int64.toBitVec h1
      simp only [Int64.toBitVec_add, Int64.toBitVec_ofNat_grind] at h2
      simp only [Items.totalSize_append] at hfit
      bv_omega
    simp [hne]
  rw [List.append_assoc,
    Executable.withAddresses_append a Q₁ (P ++ Q₂) L₂ L₂ L₂,
    Executable.withAddresses_append (a + .ofNat (Items.totalSize Q₁)) P Q₂ L₂ L₁ L₂,
    List.findSome?_append, List.findSome?_append, hQ₁_none, h]
  rfl

/-! ## Layout of `CodeDirective` & `Program` -/

/-- Legacy size helper kept for `⸨dir n | ... ⸩` syntax compatibility. -/
def Layout.size [l : Layout Instr Const] : Directive Instr Const → Nat → Nat
  | .instr _, idx => l.instrSize idx
  | .label _, _ => 0
  | .byteArray arr, _ => arr.size
  | .word bytes _, _ => bytes
  | .align k _, _ => alignPad l.start k

/-- Size in bytes of a `CodeDirective` placed at `(addr, idx)` under layout `l`. -/
def Layout.codeDirSize (l : Layout Instr Const) (addr : Int64) (idx : Nat) :
    CodeDirective Instr Const → Nat
  | .instr _ => l.instrSize idx
  | .byteArray arr => arr.size
  | .word bytes _ => bytes
  | .align log2Align _ => alignPad addr log2Align

/-- Emit strictly positive-size `SizedItem`s for `body`, threading `(addr, idx)` left-to-right.
Notice `.instr` emits directly with zero `dite` wrappers, keeping concrete straight-line layout fast. -/
def Layout.layoutBodyGo (l : Layout Instr Const) (addr : Int64) (idx : Nat) :
    List (CodeDirective Instr Const) → List (SizedItem Instr Const)
  | [] => []
  | .instr i :: rest =>
    let sz := l.instrSize idx
    ⟨.instr i, sz, l.instrSize_pos idx⟩ :: l.layoutBodyGo (addr + .ofNat sz) (idx + 1) rest
  | .byteArray bs :: rest =>
    if h : 0 < bs.size then
      ⟨.byteArray bs, bs.size, h⟩ :: l.layoutBodyGo (addr + .ofNat bs.size) (idx + 1) rest
    else
      l.layoutBodyGo addr (idx + 1) rest
  | .word n c :: rest =>
    if h : 0 < n then
      ⟨.word n c, n, h⟩ :: l.layoutBodyGo (addr + .ofNat n) (idx + 1) rest
    else
      l.layoutBodyGo addr (idx + 1) rest
  | .align k ex :: rest =>
    let sz := alignPad addr k
    if h : 0 < sz then
      ⟨.alignPad ex, sz, h⟩ :: l.layoutBodyGo (addr + .ofNat sz) (idx + 1) rest
    else
      l.layoutBodyGo addr (idx + 1) rest

def Layout.layoutBody (l : Layout Instr Const) (body : List (CodeDirective Instr Const)) :
    List (SizedItem Instr Const) :=
  l.layoutBodyGo l.start 0 body

/-- Byte offset of the `k`-th `CodeDirective` relative to `addr` starting at instruction index `idx`. -/
def Layout.sizeBeforeBodyGo (l : Layout Instr Const) (addr : Int64) (idx : Nat) :
    List (CodeDirective Instr Const) → Nat → Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | cd :: rest, k + 1 =>
    let sz := l.codeDirSize addr idx cd
    sz + l.sizeBeforeBodyGo (addr + .ofNat sz) (idx + 1) rest k

def Layout.sizeBeforeBody (l : Layout Instr Const) (body : List (CodeDirective Instr Const)) (k : Nat) : Nat :=
  l.sizeBeforeBodyGo l.start 0 body k

def Layout.totalSizeBody (l : Layout Instr Const) (body : List (CodeDirective Instr Const)) : Nat :=
  l.sizeBeforeBody body body.length

def Layout.addrOfBody (l : Layout Instr Const) (body : List (CodeDirective Instr Const)) (k : Nat) : Int64 :=
  l.start + .ofNat (l.sizeBeforeBody body k)

/-- Layout shifted past `body`. -/
@[instance_reducible]
def Layout.afterBody (l : Layout Instr Const) (body : List (CodeDirective Instr Const)) : Layout Instr Const where
  start := l.start + .ofNat (l.totalSizeBody body)
  instrSize i := l.instrSize (i + body.length)
  instrSize_pos i := l.instrSize_pos (i + body.length)

@[simp] theorem Layout.start_afterBody (l : Layout Instr Const) (body : List (CodeDirective Instr Const)) :
    @Layout.start _ _ (l.afterBody body) = l.start + .ofNat (l.totalSizeBody body) := rfl

@[simp] theorem Layout.instrSize_afterBody (l : Layout Instr Const) (body : List (CodeDirective Instr Const)) (i : Nat) :
    @Layout.instrSize _ _ (l.afterBody body) i = l.instrSize (i + body.length) := rfl

/-- Shift layout `l` by an arbitrary `(addr, idx)` offset. -/
@[instance_reducible]
private def Layout.shift (l : Layout Instr Const) (addr : Int64) (idx : Nat) : Layout Instr Const where
  start := addr
  instrSize i := l.instrSize (i + idx)
  instrSize_pos i := l.instrSize_pos (i + idx)

@[simp] private theorem Layout.instrSize_shift (l : Layout Instr Const) (a : Int64) (idx i : Nat) :
    @Layout.instrSize _ _ (l.shift a idx) i = l.instrSize (i + idx) := rfl

private theorem Layout.codeDirSize_shift (l : Layout Instr Const) (a a' : Int64) (idx i : Nat)
    (cd : CodeDirective Instr Const) :
    (l.shift a idx).codeDirSize a' i cd = l.codeDirSize a' (i + idx) cd := by
  cases cd <;> rfl

private theorem Layout.layoutBodyGo_shift (l : Layout Instr Const) (a a' : Int64) (idx i : Nat)
    (body : List (CodeDirective Instr Const)) :
    (l.shift a idx).layoutBodyGo a' i body = l.layoutBodyGo a' (i + idx) body := by
  induction body generalizing a' i with
  | nil => rfl
  | cons cd rest ih =>
    cases cd with
    | instr ins =>
      simp only [layoutBodyGo, instrSize_shift]
      congr 1
      simpa [Nat.succ_add] using ih (a' + .ofNat (l.instrSize (i + idx))) (i + 1)
    | byteArray bs =>
      simp only [layoutBodyGo]
      split
      · congr 1; simpa [Nat.succ_add] using ih (a' + .ofNat bs.size) (i + 1)
      · simpa [Nat.succ_add] using ih a' (i + 1)
    | word n c =>
      simp only [layoutBodyGo]
      split
      · congr 1; simpa [Nat.succ_add] using ih (a' + .ofNat n) (i + 1)
      · simpa [Nat.succ_add] using ih a' (i + 1)
    | align k ex =>
      simp only [layoutBodyGo]
      split
      · congr 1; simpa [Nat.succ_add] using ih (a' + .ofNat (alignPad a' k)) (i + 1)
      · simpa [Nat.succ_add] using ih a' (i + 1)

private theorem Layout.sizeBeforeBodyGo_shift (l : Layout Instr Const) (a a' : Int64) (idx i : Nat)
    (body : List (CodeDirective Instr Const)) (k : Nat) :
    (l.shift a idx).sizeBeforeBodyGo a' i body k = l.sizeBeforeBodyGo a' (i + idx) body k := by
  induction body generalizing a' i k with
  | nil => cases k <;> rfl
  | cons cd rest ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [sizeBeforeBodyGo, codeDirSize_shift]
      congr 1
      simpa [Nat.succ_add] using ih (a' + .ofNat (l.codeDirSize a' (i + idx) cd)) (i + 1) k

theorem Layout.items_totalSize_layoutBodyGo (l : Layout Instr Const) (addr : Int64) (idx : Nat)
    (body : List (CodeDirective Instr Const)) :
    Items.totalSize (l.layoutBodyGo addr idx body) = l.sizeBeforeBodyGo addr idx body body.length := by
  induction body generalizing addr idx with
  | nil => rfl
  | cons cd rest ih =>
    cases cd with
    | instr i =>
      simp only [layoutBodyGo, List.length_cons, sizeBeforeBodyGo, codeDirSize, Items.totalSize_cons]
      rw [ih]
    | byteArray bs =>
      simp only [layoutBodyGo, List.length_cons, sizeBeforeBodyGo, codeDirSize]
      split
      · simp only [Items.totalSize_cons]; rw [ih]
      · rename_i h
        have h0 : bs.size = 0 := by omega
        simp [h0, ih]
    | word n c =>
      simp only [layoutBodyGo, List.length_cons, sizeBeforeBodyGo, codeDirSize]
      split
      · simp only [Items.totalSize_cons]; rw [ih]
      · rename_i h
        have h0 : n = 0 := by omega
        simp [h0, ih]
    | align k ex =>
      simp only [layoutBodyGo, List.length_cons, sizeBeforeBodyGo, codeDirSize]
      split
      · simp only [Items.totalSize_cons]; rw [ih]
      · rename_i h
        have h0 : alignPad addr k = 0 := by omega
        simp [h0, ih]

theorem Layout.items_totalSize_layoutBody (l : Layout Instr Const) (body : List (CodeDirective Instr Const)) :
    Items.totalSize (l.layoutBody body) = l.totalSizeBody body :=
  l.items_totalSize_layoutBodyGo l.start 0 body

private theorem Layout.layoutBodyGo_append (l : Layout Instr Const) (addr : Int64) (idx : Nat)
    (b₁ b₂ : List (CodeDirective Instr Const)) :
    l.layoutBodyGo addr idx (b₁ ++ b₂) =
      l.layoutBodyGo addr idx b₁ ++
        l.layoutBodyGo (addr + .ofNat (l.sizeBeforeBodyGo addr idx b₁ b₁.length)) (idx + b₁.length) b₂ := by
  induction b₁ generalizing addr idx with
  | nil => simp [layoutBodyGo, sizeBeforeBodyGo]
  | cons cd rest ih =>
    have hstep (sz : Nat) :
        addr + .ofNat sz + .ofNat (l.sizeBeforeBodyGo (addr + .ofNat sz) (idx + 1) rest rest.length) =
          addr + .ofNat (sz + l.sizeBeforeBodyGo (addr + .ofNat sz) (idx + 1) rest rest.length) := by
      rw [Int64.ofNat_add, Int64.add_assoc]
    have hidx : idx + 1 + rest.length = idx + (rest.length + 1) := by omega
    cases cd with
    | instr i =>
      simp only [List.cons_append, layoutBodyGo, List.length_cons, sizeBeforeBodyGo, codeDirSize]
      congr 1
      rw [ih, hstep, hidx]
    | byteArray bs =>
      simp only [List.cons_append, layoutBodyGo, List.length_cons, sizeBeforeBodyGo, codeDirSize]
      split
      · simp only [List.cons_append]; congr 1; rw [ih, hstep, hidx]
      · rename_i h
        have h0 : bs.size = 0 := by omega
        simp only [h0, Int64.reduceOfNat, Int64.add_zero, Nat.zero_add]
        rw [ih, hidx]
    | word n c =>
      simp only [List.cons_append, layoutBodyGo, List.length_cons, sizeBeforeBodyGo, codeDirSize]
      split
      · simp only [List.cons_append]; congr 1; rw [ih, hstep, hidx]
      · rename_i h
        have h0 : n = 0 := by omega
        simp only [h0, Int64.reduceOfNat, Int64.add_zero, Nat.zero_add]
        rw [ih, hidx]
    | align k ex =>
      simp only [List.cons_append, layoutBodyGo, List.length_cons, sizeBeforeBodyGo, codeDirSize]
      split
      · simp only [List.cons_append]; congr 1; rw [ih, hstep, hidx]
      · rename_i h
        have h0 : alignPad addr k = 0 := by omega
        simp only [h0, Int64.reduceOfNat, Int64.add_zero, Nat.zero_add]
        rw [ih, hidx]

theorem Layout.layoutBody_append (l : Layout Instr Const) (b₁ b₂ : List (CodeDirective Instr Const)) :
    l.layoutBody (b₁ ++ b₂) = l.layoutBody b₁ ++ (l.afterBody b₁).layoutBody b₂ := by
  dsimp only [layoutBody]
  rw [layoutBodyGo_append, start_afterBody]
  congr 1
  exact (l.layoutBodyGo_shift (l.start + .ofNat (l.totalSizeBody b₁))
    (l.start + .ofNat (l.totalSizeBody b₁)) b₁.length 0 b₂).symm

private theorem Layout.sizeBeforeBodyGo_append_left (l : Layout Instr Const) (addr : Int64) (idx : Nat)
    (b₁ b₂ : List (CodeDirective Instr Const)) {k : Nat} (hk : k ≤ b₁.length) :
    l.sizeBeforeBodyGo addr idx (b₁ ++ b₂) k = l.sizeBeforeBodyGo addr idx b₁ k := by
  induction b₁ generalizing addr idx k with
  | nil =>
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst hk0; rfl
  | cons cd rest ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [List.cons_append, sizeBeforeBodyGo]
      congr 1
      exact ih _ (idx + 1) (Nat.le_of_succ_le_succ hk)

private theorem Layout.sizeBeforeBodyGo_append_right (l : Layout Instr Const) (addr : Int64) (idx : Nat)
    (b₁ b₂ : List (CodeDirective Instr Const)) (k : Nat) :
    l.sizeBeforeBodyGo addr idx (b₁ ++ b₂) (b₁.length + k) =
      l.sizeBeforeBodyGo addr idx b₁ b₁.length +
        l.sizeBeforeBodyGo (addr + .ofNat (l.sizeBeforeBodyGo addr idx b₁ b₁.length)) (idx + b₁.length) b₂ k := by
  induction b₁ generalizing addr idx with
  | nil => simp [sizeBeforeBodyGo]
  | cons cd rest ih =>
    simp only [List.cons_append, List.length_cons, Nat.succ_add, sizeBeforeBodyGo]
    rw [ih, Int64.ofNat_add, Int64.add_assoc]
    have hidx : idx + 1 + rest.length = idx + (rest.length + 1) := by omega
    rw [hidx, Nat.add_assoc]

theorem Layout.sizeBeforeBody_append_left (l : Layout Instr Const)
    (b₁ b₂ : List (CodeDirective Instr Const)) {k : Nat} (hk : k ≤ b₁.length) :
    l.sizeBeforeBody (b₁ ++ b₂) k = l.sizeBeforeBody b₁ k :=
  l.sizeBeforeBodyGo_append_left l.start 0 b₁ b₂ hk

theorem Layout.sizeBeforeBody_append_right (l : Layout Instr Const)
    (b₁ b₂ : List (CodeDirective Instr Const)) (k : Nat) :
    l.sizeBeforeBody (b₁ ++ b₂) (b₁.length + k) =
      l.totalSizeBody b₁ + (l.afterBody b₁).sizeBeforeBody b₂ k := by
  dsimp only [sizeBeforeBody]
  rw [sizeBeforeBodyGo_append_right, start_afterBody]
  congr 1
  exact (l.sizeBeforeBodyGo_shift (l.start + .ofNat (l.totalSizeBody b₁))
    (l.start + .ofNat (l.totalSizeBody b₁)) b₁.length 0 b₂ k).symm

theorem Layout.totalSizeBody_append (l : Layout Instr Const) (b₁ b₂ : List (CodeDirective Instr Const)) :
    l.totalSizeBody (b₁ ++ b₂) = l.totalSizeBody b₁ + (l.afterBody b₁).totalSizeBody b₂ := by
  simpa only [totalSizeBody, List.length_append] using l.sizeBeforeBody_append_right b₁ b₂ b₂.length

@[simp] theorem Layout.addrOfBody_zero (l : Layout Instr Const) (body : List (CodeDirective Instr Const)) :
    l.addrOfBody body 0 = l.start := by
  simp [addrOfBody, sizeBeforeBody, sizeBeforeBodyGo]

@[simp] theorem Layout.addrOfBody_length (l : Layout Instr Const) (body : List (CodeDirective Instr Const)) :
    l.addrOfBody body body.length = @Layout.start _ _ (l.afterBody body) := rfl

theorem Layout.addrOfBody_infix (l : Layout Instr Const)
    (b₁ b b₂ : List (CodeDirective Instr Const)) {k : Nat} (hk : k ≤ b.length) :
    l.addrOfBody (b₁ ++ b ++ b₂) (b₁.length + k) = (l.afterBody b₁).addrOfBody b k := by
  rw [List.append_assoc]
  unfold addrOfBody
  rw [l.sizeBeforeBody_append_right b₁ (b ++ b₂) k,
    (l.afterBody b₁).sizeBeforeBody_append_left b b₂ hk,
    Int64.ofNat_add, ← Int64.add_assoc]
  rfl

theorem Layout.addrOfBody_succ (l : Layout Instr Const) (body : List (CodeDirective Instr Const))
    {k : Nat} {cd : CodeDirective Instr Const} (hcd : body[k]? = some cd) :
    l.addrOfBody body (k + 1) =
      l.addrOfBody body k + .ofNat (l.codeDirSize (l.addrOfBody body k) k cd) := by
  have hlt : k < body.length := (List.getElem?_eq_some_iff.mp hcd).1
  have hsplit : body = body.take k ++ [cd] ++ body.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append]
    have hdrop : body.drop k = cd :: body.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      simp [(List.getElem?_eq_some_iff.mp hcd).2]
    rw [← hdrop, List.take_append_drop]
  have hlen : (body.take k).length = k := List.length_take_of_le (Nat.le_of_lt hlt)
  have ha_k : l.addrOfBody body k = @Layout.start _ _ (l.afterBody (body.take k)) := by
    conv => lhs; rw [hsplit]
    have h0 := l.addrOfBody_infix (body.take k) [cd] (body.drop (k + 1)) (k := 0) (Nat.zero_le _)
    simpa [hlen] using h0
  have ha_k1 : l.addrOfBody body (k + 1) = (l.afterBody (body.take k)).addrOfBody [cd] 1 := by
    conv => lhs; rw [hsplit]
    have h1 := l.addrOfBody_infix (body.take k) [cd] (body.drop (k + 1)) (k := 1) (Nat.le_refl 1)
    simpa [hlen] using h1
  rw [ha_k1, ha_k]
  simp only [addrOfBody, sizeBeforeBody, sizeBeforeBodyGo, Nat.add_zero, start_afterBody]
  congr 2
  cases cd <;> simp [codeDirSize, instrSize_afterBody, hlen]

/-- After stepping past `.align log2Align`, the resulting address is aligned to `2 ^ log2Align` bytes. -/
theorem Layout.addrOfBody_align (l : Layout Instr Const) (body : List (CodeDirective Instr Const))
    {k log2Align : Nat} {ex : Bool} (hcd : body[k]? = some (.align log2Align ex))
    (hle : log2Align ≤ 64) :
    (l.addrOfBody body (k + 1)).toUInt64.toNat % 2 ^ log2Align = 0 := by
  rw [l.addrOfBody_succ body hcd]
  exact alignPad_aligned (l.addrOfBody body k) hle

/-- Single-item lookup in a laid-out body whenever the `k`-th `CodeDirective` has positive size. -/
theorem Layout.itemAt?_addrOfBody (l : Layout Instr Const) (body : List (CodeDirective Instr Const))
    (L : Labels) (hfit : l.totalSizeBody body < 2 ^ 64)
    {k : Nat} {cd : CodeDirective Instr Const} (hcd : body[k]? = some cd)
    (hpos : 0 < l.codeDirSize (l.addrOfBody body k) k cd) :
    ({ startAddr := l.start, items := l.layoutBody body, labels := L } :
        Executable Instr Const).itemAt? (l.addrOfBody body k) =
      some ⟨cd.toItem, l.codeDirSize (l.addrOfBody body k) k cd, hpos⟩ := by
  have hlt : k < body.length := (List.getElem?_eq_some_iff.mp hcd).1
  have hsplit : body = body.take k ++ [cd] ++ body.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append]
    have hdrop : body.drop k = cd :: body.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      simp [(List.getElem?_eq_some_iff.mp hcd).2]
    rw [← hdrop, List.take_append_drop]
  have hlen : (body.take k).length = k := List.length_take_of_le (Nat.le_of_lt hlt)
  have ha_k : l.addrOfBody body k = l.start + .ofNat (Items.totalSize (l.layoutBody (body.take k))) := by
    rw [l.items_totalSize_layoutBody]
    conv => lhs; rw [hsplit]
    have h0 := l.addrOfBody_infix (body.take k) [cd] (body.drop (k + 1)) (k := 0) (Nat.zero_le _)
    simpa [hlen, afterBody] using h0
  have hlayout_split : l.layoutBody body =
      l.layoutBody (body.take k) ++
        (l.afterBody (body.take k)).layoutBody [cd] ++
        (l.afterBody (body.take k ++ [cd])).layoutBody (body.drop (k + 1)) := by
    conv => lhs; rw [hsplit]
    rw [l.layoutBody_append, l.layoutBody_append]
  have hfit_items : Items.totalSize
      (l.layoutBody (body.take k) ++
        (l.afterBody (body.take k)).layoutBody [cd] ++
        (l.afterBody (body.take k ++ [cd])).layoutBody (body.drop (k + 1))) < 2 ^ 64 := by
    rw [← hlayout_split, l.items_totalSize_layoutBody]
    exact hfit
  have hcd_eq : (l.afterBody (body.take k)).layoutBody [cd] =
      [⟨cd.toItem, l.codeDirSize (l.addrOfBody body k) k cd, hpos⟩] := by
    have hstart : @Layout.start _ _ (l.afterBody (body.take k)) = l.addrOfBody body k := by
      rw [ha_k, l.items_totalSize_layoutBody]; rfl
    cases cd with
    | instr i =>
      simp only [layoutBody, layoutBodyGo, codeDirSize, CodeDirective.toItem, instrSize_afterBody,
        hlen, Nat.zero_add]
    | byteArray bs =>
      simp only [layoutBody, layoutBodyGo, codeDirSize, CodeDirective.toItem] at hpos ⊢
      simp [hpos]
    | word n c =>
      simp only [layoutBody, layoutBodyGo, codeDirSize, CodeDirective.toItem] at hpos ⊢
      simp [hpos]
    | align m ex =>
      simp only [layoutBody, layoutBodyGo, codeDirSize, CodeDirective.toItem, hstart] at hpos ⊢
      simp [hpos]
  rw [hlayout_split]
  refine Executable.itemAt?_infix l.start
    (l.layoutBody (body.take k))
    ((l.afterBody (body.take k)).layoutBody [cd])
    ((l.afterBody (body.take k ++ [cd])).layoutBody (body.drop (k + 1)))
    L L hfit_items ?_
  rw [← ha_k, hcd_eq]
  simp [Executable.itemAt?]

/-! ## Program-Level Layout API (`Layout.apply`, `Layout.addrOf`, `Layout.after`, `Layout.labelsOf`) -/

def Layout.totalSize (l : Layout Instr Const) (p : Program Instr Const) : Nat :=
  l.totalSizeBody p.splitLabels.body

def Layout.addrOf (l : Layout Instr Const) (p : Program Instr Const) (k : Nat) : Int64 :=
  l.addrOfBody p.splitLabels.body k

/-- Layout shifted past program `p`. -/
@[instance_reducible]
def Layout.after (l : Layout Instr Const) (p : Program Instr Const) : Layout Instr Const :=
  l.afterBody p.splitLabels.body

/-- Label map of a `SplitProgram` resolved directly via `List.lookup` + `addrOfBody`. -/
def Layout.labelsOf (l : Layout Instr Const) (sp : SplitProgram Instr Const) : Labels :=
  { label? lbl := (sp.labels.lookup lbl).map (l.addrOfBody sp.body) }

/-- Lay out a `Program` into an `Executable` (stripping `.label` and zero-size items). -/
def Layout.apply (l : Layout Instr Const) (p : Program Instr Const) : Executable Instr Const :=
  let sp := p.splitLabels
  { startAddr := l.start, items := l.layoutBody sp.body, labels := l.labelsOf sp }

-- NOTE: We write `List (Kraken.Directive Instr Const)` here, and not `Kraken.Program Instr Const`,
-- so Lean's typeclass synthesis matches architecture-specific `Program := List Directive`.
instance : CoeFun (Layout Instr Const) (fun _ => List (Directive Instr Const) → Executable Instr Const) where
  coe := Layout.apply

@[simp] theorem Layout.apply_startAddr (l : Layout Instr Const) (p : Program Instr Const) :
    (l p).startAddr = l.start := rfl

theorem Layout.itemsFromStart [l : Layout Instr Const] (p : Program Instr Const) :
    (l p).itemsFromAddress l.start = l.layoutBody p.splitLabels.body :=
  Executable.itemsFromStart (l p)

@[simp] theorem Layout.items_totalSize_apply (l : Layout Instr Const) (p : Program Instr Const) :
    Items.totalSize (l p).items = l.totalSize p :=
  l.items_totalSize_layoutBody p.splitLabels.body

theorem Layout.apply_items_append (l : Layout Instr Const) (p q : Program Instr Const) :
    (l (p ++ q)).items = (l p).items ++ ((l.after p) q).items := by
  simp only [Layout.apply, Program.splitLabels_body_append, Layout.after]
  exact l.layoutBody_append p.splitLabels.body q.splitLabels.body

theorem Layout.totalSize_append (l : Layout Instr Const) (p q : Program Instr Const) :
    l.totalSize (p ++ q) = l.totalSize p + (l.after p).totalSize q := by
  simp only [Layout.totalSize, Program.splitLabels_body_append, Layout.after]
  exact l.totalSizeBody_append p.splitLabels.body q.splitLabels.body

@[simp] theorem Layout.after_nil (l : Layout Instr Const) : l.after [] = l := by
  rcases l with ⟨s, sz, hpos⟩
  simp [Layout.after, Layout.afterBody, Layout.totalSizeBody, Layout.sizeBeforeBody, Layout.sizeBeforeBodyGo]

theorem Layout.after_append (l : Layout Instr Const) (p q : Program Instr Const) :
    l.after (p ++ q) = (l.after p).after q := by
  rcases l with ⟨s, sz, hpos⟩
  simp only [Layout.after, Layout.afterBody, Program.splitLabels_body_append,
    Layout.totalSizeBody_append, List.length_append, start_afterBody]
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
    l.addrOf p 0 = l.start :=
  l.addrOfBody_zero p.splitLabels.body

@[simp] theorem Layout.addrOf_length (l : Layout Instr Const) (p : Program Instr Const) :
    l.addrOf p p.splitLabels.body.length = @Layout.start _ _ (l.after p) := rfl

theorem Layout.addrOf_succ (l : Layout Instr Const) (p : Program Instr Const)
    {k : Nat} {cd : CodeDirective Instr Const} (hcd : p.splitLabels.body[k]? = some cd) :
    l.addrOf p (k + 1) =
      l.addrOf p k + .ofNat (l.codeDirSize (l.addrOf p k) k cd) :=
  l.addrOfBody_succ p.splitLabels.body hcd

theorem Layout.addrOf_align (l : Layout Instr Const) (p : Program Instr Const)
    {k log2Align : Nat} {ex : Bool} (hcd : p.splitLabels.body[k]? = some (.align log2Align ex))
    (hle : log2Align ≤ 64) :
    (l.addrOf p (k + 1)).toUInt64.toNat % 2 ^ log2Align = 0 :=
  l.addrOfBody_align p.splitLabels.body hcd hle

theorem Layout.addrOf_infix (l : Layout Instr Const) (q₁ p q₂ : Program Instr Const)
    {k : Nat} (hk : k ≤ p.splitLabels.body.length) :
    l.addrOf (q₁ ++ p ++ q₂) (q₁.splitLabels.body.length + k) = (l.after q₁).addrOf p k := by
  simp only [Layout.addrOf, Program.splitLabels_body_append, Layout.after]
  exact l.addrOfBody_infix q₁.splitLabels.body p.splitLabels.body q₂.splitLabels.body hk

theorem Layout.itemAt?_addrOf (l : Layout Instr Const) (p : Program Instr Const)
    (hfit : l.totalSize p < 2 ^ 64)
    {k : Nat} {cd : CodeDirective Instr Const} (hcd : p.splitLabels.body[k]? = some cd)
    (hpos : 0 < l.codeDirSize (l.addrOf p k) k cd) :
    (l p).itemAt? (l.addrOf p k) =
      some ⟨cd.toItem, l.codeDirSize (l.addrOf p k) k cd, hpos⟩ :=
  l.itemAt?_addrOfBody p.splitLabels.body (l.labelsOf p.splitLabels) hfit hcd hpos

theorem Layout.itemAt?_infix (l : Layout Instr Const) (q₁ p q₂ : Program Instr Const)
    (hfit : l.totalSize (q₁ ++ p ++ q₂) < 2 ^ 64)
    {pc : Int64} {c : SizedItem Instr Const}
    (h : ((l.after q₁) p).itemAt? pc = some c) :
    (l (q₁ ++ p ++ q₂)).itemAt? pc = some c := by
  have hitems : (l (q₁ ++ p ++ q₂)).items =
      (l q₁).items ++ ((l.after q₁) p).items ++ ((l.after (q₁ ++ p)) q₂).items := by
    rw [l.apply_items_append, l.apply_items_append]
  have hfit' : Items.totalSize ((l q₁).items ++ ((l.after q₁) p).items ++ ((l.after (q₁ ++ p)) q₂).items) < 2 ^ 64 := by
    rw [← hitems, l.items_totalSize_apply]
    exact hfit
  have hstart : ((l.after q₁) p).startAddr = l.start + .ofNat (Items.totalSize (l q₁).items) := by
    rw [l.items_totalSize_apply]; rfl
  change ({ startAddr := l.start, items := (l (q₁ ++ p ++ q₂)).items, labels := (l (q₁ ++ p ++ q₂)).labels } :
      Executable Instr Const).itemAt? pc = some c
  rw [hitems]
  refine Executable.itemAt?_infix l.start (l q₁).items ((l.after q₁) p).items ((l.after (q₁ ++ p)) q₂).items
    ((l.after q₁) p).labels (l (q₁ ++ p ++ q₂)).labels hfit' ?_
  rw [← hstart]
  exact h

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
    (lbl : Label) {k : Nat} (hk : p.splitLabels.labels.lookup lbl = some k) :
    (l p).labels.label? lbl = some (l.addrOf p k) := by
  simp [Layout.apply, Layout.labelsOf, Layout.addrOf, hk]

theorem Layout.label!_eq_addrOf [l : Layout Instr Const] (p : Program Instr Const)
    (lbl : Label) {k : Nat} (hk : p.splitLabels.labels.lookup lbl = some k) :
    (l p).labels.label! lbl = l.addrOf p k := by
  simp [Labels.label!, Layout.label?_eq_some_addrOf p lbl hk]

theorem Layout.labels_sub_infix (l : Layout Instr Const) (q₁ p q₂ : Program Instr Const)
    (hdisj : ∀ lbl ∈ q₁.definedLabels, lbl ∉ p.definedLabels) :
    ((l.after q₁) p).labels ⊆ (l (q₁ ++ p ++ q₂)).labels := by
  intro lbl a h
  simp only [Layout.apply, Layout.labelsOf] at h ⊢
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
  have hk_mem : (lbl, k) ∈ p.splitLabels.labels := mem_of_lookup_eq_some hk
  have hk_le : k ≤ p.splitLabels.body.length := p.splitLabels_labels_le _ hk_mem
  have hnot_q₁ : lbl ∉ q₁.splitLabels.labels.map Prod.fst := by
    rw [← q₁.definedLabels_eq_map_fst]
    intro hmem
    exact hdisj lbl hmem (by
      rw [p.definedLabels_eq_map_fst]
      exact List.mem_map.mpr ⟨(lbl, k), hk_mem, rfl⟩)
  have hq₁_none : q₁.splitLabels.labels.lookup lbl = none :=
    lookup_eq_none_of_not_mem_map_fst hnot_q₁
  rw [Program.splitLabels_labels_append, Program.splitLabels_labels_append,
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
    (hk : p.splitLabels.labels.lookup fn = some k)
    {contract : Int64 → Prop}
    (h : FnSpec (l p) fn contract) :
    contract (l.addrOf p k) := by
  obtain ⟨entry, hentry, hc⟩ := h
  have hk' := l.label?_eq_some_addrOf p fn hk
  cases hentry.symm.trans hk'
  exact hc

end Kraken

export Kraken (Labels FnSpec alignPad)
