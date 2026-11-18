module

public import Lean.ToExpr

@[expose] public section

/-
Common Kraken executable layout and label resolution.
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

inductive Directive (Instr Const : Type) where
  | instr (_ : Instr)
  | label (_ : Label)
  | byteArray (arr : ByteArray)
  /-- A data word of `bytes` bytes whose value is a symbolic constant, e.g. a label or a
  difference of labels (a relocation). It is never executed. Jump tables (`.long .Lcase - .Ltable`)
  and pointer tables (`.quad fn`) are the typical uses. -/
  | word (bytes : Nat) (e : Const)
  deriving DecidableEq, Repr, Hashable, BEq, Lean.ToExpr

structure Sized Directive where
  directive : Directive
  size : Nat

abbrev Program Instr Const := List (Directive Instr Const)

structure Executable (Instr Const : Type) where
  startAddr : Int64
  program : List (Sized (Directive Instr Const))

class Layout (Instr Const : Type) where
  start : Int64
  instrSize : Nat → Nat
  instrSize_pos : ∀ i, 0 < instrSize i

variable {Instr Const : Type}

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

abbrev Directives.size (ds : List (Sized (Directive Instr Const))) : Nat :=
  (ds.map (·.size)).sum

@[simp] theorem Directives.size_append (xs ys : List (Sized (Directive Instr Const))) :
    Directives.size (xs ++ ys) = Directives.size xs + Directives.size ys := by
  simp [Directives.size]

def Layout.size [l : Layout Instr Const] : Directive Instr Const → Nat → Nat
  | .instr _, idx => l.instrSize idx
  | .label _, _ => 0
  | .byteArray arr, _ => arr.size
  | .word bytes _, _ => bytes

def Layout.apply (l : Layout Instr Const) (prog : Program Instr Const) : Executable Instr Const :=
  {startAddr := l.start, program := prog.mapIdx fun idx directive => {directive, size := @Layout.size _ _ l directive idx}}

-- NOTE: We write `List (Kraken.Directive Instr Const)` here, and not `Kraken.Program Instr Const`, because architecture
-- specific `Program` types are written as `List Directive` which desugar to `List (Kraken.Directive Instr Const)`,
-- and so otherwise the typeclass synthesis algorithm would not find this instance.
instance : CoeFun (Layout Instr Const) (fun _ => List (Directive Instr Const) → Executable Instr Const) where
  coe := Layout.apply

@[simp] theorem Layout.apply_length (l : Layout Instr Const) (p : Program Instr Const) :
    (l p).program.length = p.length := by
  simp [Layout.apply]

theorem Layout.apply_getElem? (l : Layout Instr Const) (p : Program Instr Const) (i : Nat) :
    (l p).program[i]? = (p[i]?).map (fun d => {directive := d, size := @Layout.size _ _ l d i}) := by
  simp [Layout.apply, List.getElem?_mapIdx]

@[simp] theorem Layout.apply_map_directive (l : Layout Instr Const) (p : Program Instr Const) :
    (l p).program.map (·.directive) = p :=
  List.ext_getElem? fun _ => by grind [Layout.apply]

structure Addressable (Directive : Type) extends Sized Directive where (addr : Int64)

variable (e : Executable Instr Const) (program : List (Sized (Directive Instr Const))) {c : Sized (Directive Instr Const)}

-- Returns each directive paired with its start address and size.
def Executable.withAddresses (e : Executable Instr Const) : List (Addressable (Directive Instr Const)) :=
  go e.startAddr e.program
where go (startAddr : Int64) : List (Sized (Directive Instr Const)) → List (Addressable (Directive Instr Const))
  | [] => []
  | instr :: program => {instr with addr := startAddr} :: go (startAddr + .ofNat instr.size) program

@[simp] theorem Executable.withAddresses_nil (a : Int64) :
    Executable.withAddresses (Instr := Instr) (Const := Const) ⟨a, []⟩ = [] := rfl

@[simp] theorem Executable.withAddresses_cons (a : Int64) (c : Sized (Directive Instr Const))
    (cs : List (Sized (Directive Instr Const))) :
    Executable.withAddresses ⟨a, c :: cs⟩ =
      {c with addr := a} :: Executable.withAddresses ⟨a + .ofNat c.size, cs⟩ := rfl

def Executable.directivesAtAddress (a : Int64) : List (Sized (Directive Instr Const)) :=
  (e.withAddresses.filter (·.addr = a)).map (·.toSized)

def Executable.directivesFromAddress (a : Int64) : List (Sized (Directive Instr Const)) :=
  let starts_at_a := e.withAddresses.dropWhile (·.addr ≠ a)
  starts_at_a.map (·.toSized)

def Executable.labels (e : Executable Instr Const) : Labels :=
  { label? l := e.withAddresses.findSome?
      fun {directive, addr, ..} => if directive.isLabel l then some addr else none }

theorem Executable.withAddresses_map_snd (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).map (·.toSized) = program := by
  induction program generalizing startAddr <;> simp_all

theorem Executable.withAddresses_dropWhile_start (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).dropWhile (fun x => x.addr ≠ startAddr) =
      Executable.withAddresses {startAddr, program} := by
  cases program <;> simp

theorem Executable.directivesFromStart [layout : Layout Instr Const] (prog : Program Instr Const) :
    (layout prog).directivesFromAddress layout.start =
      prog.mapIdx (fun i directive => {directive, size := layout.size directive i}) := by
  grind [Executable.withAddresses_dropWhile_start, Executable.withAddresses_map_snd, Executable.directivesFromAddress, Layout.apply]

variable {e} in
theorem Executable.mem_of_mem_directivesAtAddress
    {a : Int64} (h : c ∈ e.directivesAtAddress a) : c ∈ e.program := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  rw [← Executable.withAddresses_map_snd e.program e.startAddr]
  exact List.mem_map_of_mem (List.mem_filter.mp hx).1

@[grind hom] theorem Int64.toBitVec_ofNat_grind (a : Nat) :
    (Int64.ofNat a).toBitVec = OfNat.ofNat a := by
  rw [Int64.toBitVec_ofNat']; rfl

/-- The sum of sizes of the first `n` directives of `e`. -/
def Executable.sizeBefore (n : Nat) : Nat :=
  ((e.program.take n).map (·.size)).sum

/--
The address of the `n`-th directive of `e`: the start address of `e` plus the sum of sizes of the
first `n` directives.
-/
def Executable.addrOf (n : Nat) : Int64 :=
  e.startAddr + .ofNat (e.sizeBefore n)

@[simp] theorem Executable.addrOf_zero : e.addrOf 0 = e.startAddr := by
  grind [sizeBefore, addrOf]

@[grind →] theorem Executable.sizeBefore_succ {n : Nat}
    (hc : e.program[n]? = some c) : e.sizeBefore (n + 1) = e.sizeBefore n + c.size := by
  simp [sizeBefore, List.take_add_one, hc]

theorem Executable.sizeBefore_add (j i : Nat) :
    e.sizeBefore (j + i) = e.sizeBefore j + (((e.program.drop j).take i).map (·.size)).sum := by
  simp [sizeBefore, List.take_add]

theorem Executable.sizeBefore_mono {j k : Nat}
    (h : j ≤ k) : e.sizeBefore j ≤ e.sizeBefore k := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
  simp [sizeBefore_add]

theorem Executable.addrOf_succ {n : Nat}
    (hc : e.program[n]? = some c) : e.addrOf (n + 1) = e.addrOf n + .ofNat c.size := by
  grind [addrOf]

theorem Executable.getElem?_withAddresses_mk :
    ∀ (program : List (Sized (Directive Instr Const))) (startAddr : Int64) (k : Nat),
      (Executable.withAddresses {startAddr, program})[k]?
        = program[k]?.map (fun c => {c with addr := Executable.addrOf {startAddr, program} k})
  | [], _, _ => by simp
  | _ :: _, _, 0 => by simp
  | c :: program, a, k + 1 => by
    simp only [withAddresses_cons, List.getElem?_cons_succ, getElem?_withAddresses_mk program _ k]
    congr 2
    funext c'
    simp only [addrOf, sizeBefore, List.take_succ_cons, List.map_cons, List.sum_cons]
    grind

theorem Executable.getElem?_withAddresses_eq (k : Nat) :
    e.withAddresses[k]? = e.program[k]?.map (fun c => {c with addr := e.addrOf k}) :=
  getElem?_withAddresses_mk e.program e.startAddr k

theorem Executable.directivesAtAddress_addrOf
    (hinj : ∀ j k, e.addrOf j = e.addrOf k → e.sizeBefore j = e.sizeBefore k)
    {k : Nat} (hc : e.program[k]? = some c) (hz : 0 < c.size) :
    ∃ pre : List (Sized (Directive Instr Const)), e.directivesAtAddress (e.addrOf k) = pre ++ [c] ∧
      ∀ c' ∈ pre, c'.size = 0 := by
  have hat : ∀ j x, e.withAddresses[j]? = some x → x.addr = e.addrOf j ∧ e.program[j]? = some x.toSized := by
    grind [Executable.getElem?_withAddresses_eq]
  obtain ⟨hklt, hkx⟩ := List.getElem?_eq_some_iff.mp
    (by simp [Executable.getElem?_withAddresses_eq, hc] : e.withAddresses[k]? = some {c with addr := e.addrOf k})
  refine ⟨((e.withAddresses.take k).filter (·.addr = e.addrOf k)).map (·.toSized), ?_, ?_⟩
  · have hdrop : (e.withAddresses.drop (k + 1)).filter (·.addr = e.addrOf k) = [] :=
      List.filter_eq_nil_iff.mpr fun x hx hxa => by
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
        have := hinj _ _ ((hat _ _ (List.getElem?_drop .. ▸ hi)).1.symm.trans (of_decide_eq_true hxa))
        have := e.sizeBefore_mono (Nat.le_add_right (k + 1) i)
        have := e.sizeBefore_succ hc
        omega
    unfold Executable.directivesAtAddress
    conv => lhs; rw [← List.take_append_drop k e.withAddresses, List.drop_eq_getElem_cons hklt, hkx]
    simp [hdrop]
  · intro c' hc'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc'
    obtain ⟨hxt, hxa⟩ := List.mem_filter.mp hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hxt
    obtain ⟨hilt, hi⟩ : i + 1 ≤ k ∧ e.withAddresses[i]? = some x := by grind
    obtain ⟨ha, hp⟩ := hat _ _ hi
    have := hinj _ _ (ha.symm.trans (of_decide_eq_true hxa))
    have := e.sizeBefore_succ hp
    have := e.sizeBefore_mono hilt
    omega

variable {e} in
theorem Executable.exists_of_mem_directivesAtAddress
    {a : Int64} (h : c ∈ e.directivesAtAddress a) :
    ∃ k, e.program[k]? = some c ∧ e.addrOf k = a := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨k, _⟩ := List.mem_iff_getElem?.mp (List.mem_filter.mp hx).1
  grind [Executable.getElem?_withAddresses_eq]

theorem Executable.sizeBefore_eq_of_addrOf_eq
    (hfit : Directives.size e.program < 2 ^ 64) {j k : Nat} (h : e.addrOf j = e.addrOf k) :
    e.sizeBefore j = e.sizeBefore k := by
  have hle : ∀ n, e.sizeBefore n ≤ Directives.size e.program := fun n => by
    grind [Executable.sizeBefore, List.take_append_drop]
  have := hle j
  have := hle k
  have h' := congrArg Int64.toBitVec h
  simp only [Executable.addrOf, Int64.toBitVec_add, Int64.toBitVec_ofNat_grind] at h'
  bv_omega

theorem Executable.withAddresses_append (a : Int64) (xs ys : List (Sized (Directive Instr Const))) :
    Executable.withAddresses (⟨a, xs ++ ys⟩ : Executable Instr Const) =
      Executable.withAddresses ⟨a, xs⟩ ++
        Executable.withAddresses ⟨a + .ofNat (Directives.size xs), ys⟩ := by
  induction xs generalizing a <;>
    grind [Executable.withAddresses_nil, Executable.withAddresses_cons,
      Int64.ofNat_add, Int64.add_assoc]

theorem Executable.withAddresses_findSome?_label_mk :
    ∀ (program : List (Sized (Directive Instr Const))) (startAddr : Int64) (lbl : Label) (k : Nat),
      program.findIdx? (·.directive.isLabel lbl) = some k →
      (Executable.labels ⟨startAddr, program⟩).label? lbl =
        some (Executable.addrOf ⟨startAddr, program⟩ k)
  | [], _, _, _, hk => by simp at hk
  | c :: program, startAddr, lbl, k, hk => by
    dsimp only [Executable.labels]
    rw [Executable.withAddresses_cons, List.findSome?_cons]
    by_cases hc : c.directive.isLabel lbl
    · have hk0 : k = 0 := by simpa [List.findIdx?_cons, hc] using hk.symm
      subst hk0
      simp [hc]
    · have hk1 : (program.findIdx? (·.directive.isLabel lbl)).map (· + 1) = some k := by
        simpa [List.findIdx?_cons, hc] using hk
      obtain ⟨k', hk2, rfl⟩ := Option.map_eq_some_iff.mp hk1
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      change (Executable.labels { startAddr := startAddr + .ofNat c.size, program }).label? lbl = _
      rw [withAddresses_findSome?_label_mk program (startAddr + .ofNat c.size) lbl k' hk2]
      congr 1
      simp only [Executable.addrOf, Executable.sizeBefore, List.take_succ_cons, List.map_cons,
        List.sum_cons, Int64.ofNat_add, Int64.add_assoc]

theorem Layout.label?_eq_some_addrOf [l : Layout Instr Const] (prog : Program Instr Const)
    (lbl : Label) {k : Nat} (hk : prog.findIdx? (·.isLabel lbl) = some k) :
    ((l prog).labels).label? lbl = some ((l prog).addrOf k) := by
  apply Executable.withAddresses_findSome?_label_mk
  rw [← l.apply_map_directive prog, List.findIdx?_map] at hk
  exact hk

theorem Layout.label!_eq_addrOf [l : Layout Instr Const] (prog : Program Instr Const)
    (lbl : Label) {k : Nat} (hk : prog.findIdx? (·.isLabel lbl) = some k) :
    ((l prog).labels).label! lbl = (l prog).addrOf k := by
  simp [Labels.label!, Layout.label?_eq_some_addrOf prog lbl hk]

theorem Executable.labels_eq_none_iff {a : Int64} {cs : List (Sized (Directive Instr Const))} {l : Label} :
    (Executable.labels ⟨a, cs⟩).label? l = none ↔ l ∉ Program.definedLabels (cs.map (·.directive)) := by
  induction cs generalizing a <;>
    grind [Executable.labels, Directive.isLabel, Program.definedLabels,
      Executable.withAddresses_nil, Executable.withAddresses_cons]

theorem Executable.labels_sub_infix (a : Int64) (Q₁ P Q₂ : List (Sized (Directive Instr Const)))
    (hdisj : ∀ l ∈ Program.definedLabels (Q₁.map (·.directive)),
      l ∉ Program.definedLabels (P.map (·.directive))) :
    Executable.labels ⟨a + .ofNat (Directives.size Q₁), P⟩ ⊆
      Executable.labels ⟨a, Q₁ ++ P ++ Q₂⟩ := by
  intro l x h
  have hQ₁ : (Executable.labels ⟨a, Q₁⟩).label? l = none :=
    Executable.labels_eq_none_iff.mpr fun hl =>
      hdisj l hl (Classical.byContradiction fun hn => by
        simp [Executable.labels_eq_none_iff.mpr hn] at h)
  dsimp only [Executable.labels] at hQ₁ h ⊢
  rw [List.append_assoc, Executable.withAddresses_append, Executable.withAddresses_append,
    List.findSome?_append, List.findSome?_append, hQ₁, h]
  rfl

/-- Layout shifted past prefix program `q`. -/
@[instance_reducible]
def Layout.after (layout : Layout Instr Const) (q : Program Instr Const) : Layout Instr Const where
  start := layout.start + .ofNat (Directives.size (layout q).program)
  instrSize i := layout.instrSize (i + q.length)
  instrSize_pos i := layout.instrSize_pos (i + q.length)

@[simp] theorem Layout.size_after (layout : Layout Instr Const) (q : Program Instr Const)
    (d : Directive Instr Const) (i : Nat) :
    @Layout.size _ _ (layout.after q) d i = @Layout.size _ _ layout d (i + q.length) := by
  cases d <;> rfl

theorem Layout.apply_append (layout : Layout Instr Const) (p q : Program Instr Const) :
    layout (p ++ q) = ⟨layout.start, (layout p).program ++ ((layout.after p) q).program⟩ := by
  simp only [Layout.apply, List.mapIdx_append, Layout.size_after]

@[simp] theorem Layout.after_nil (layout : Layout Instr Const) : layout.after [] = layout := by
  cases layout
  simp [Layout.after, Layout.apply, Directives.size]

@[simp] theorem Layout.addrOf_length (layout : Layout Instr Const) (p : Program Instr Const) :
    (layout p).addrOf p.length = @Layout.start _ _ (layout.after p) := by
  have hlen : (layout p).program.length = p.length := by simp
  simp only [Executable.addrOf, Executable.sizeBefore, List.take_of_length_le (Nat.le_of_eq hlen)]
  rfl

theorem Layout.after_append (layout : Layout Instr Const) (p q : Program Instr Const) :
    layout.after (p ++ q) = (layout.after p).after q := by
  rcases layout with ⟨s, sz, hpos⟩
  simp only [Layout.after, Layout.start, Layout.apply_append, Directives.size_append,
    List.length_append]
  congr 1
  · rw [Int64.ofNat_add, Int64.add_assoc]
  · funext i; congr 1; omega

theorem Layout.size_left_lt (layout : Layout Instr Const) {p q : Program Instr Const}
    (h : Directives.size (layout (p ++ q)).program < 2 ^ 64) :
    Directives.size (layout p).program < 2 ^ 64 := by
  simp [Layout.apply_append] at h; omega

theorem Layout.size_after_lt (layout : Layout Instr Const) {p q : Program Instr Const}
    (h : Directives.size (layout (p ++ q)).program < 2 ^ 64) :
    Directives.size ((layout.after p) q).program < 2 ^ 64 := by
  simp [Layout.apply_append] at h; omega

theorem Executable.addrOf_infix {a : Int64} {Q₁ P Q₂ : List (Sized (Directive Instr Const))}
    {k : Nat} (hk : k ≤ P.length) :
    (⟨a, Q₁ ++ P ++ Q₂⟩ : Executable Instr Const).addrOf (Q₁.length + k) =
      (⟨a + .ofNat (Directives.size Q₁), P⟩ : Executable Instr Const).addrOf k := by
  simp [Executable.addrOf, Executable.sizeBefore, Directives.size, List.take_append,
    Nat.sub_eq_zero_of_le hk, Int64.ofNat_add, Int64.add_assoc,
    List.take_of_length_le (l := Q₁.map (·.size)) (by simp : (Q₁.map (·.size)).length ≤ Q₁.length + k)]

theorem Layout.addrOf_infix (layout : Layout Instr Const) (q₁ p q₂ : Program Instr Const)
    {k : Nat} (hk : k ≤ p.length) :
    (layout (q₁ ++ p ++ q₂)).addrOf (q₁.length + k) = ((layout.after q₁) p).addrOf k := by
  have hlen1 : (layout q₁).program.length = q₁.length := by simp
  have hlenp : ((layout.after q₁) p).program.length = p.length := by simp
  rw [Layout.apply_append, Layout.apply_append]
  have h := Executable.addrOf_infix (a := layout.start)
    (Q₁ := (layout q₁).program) (P := ((layout.after q₁) p).program)
    (Q₂ := ((layout.after (q₁ ++ p)) q₂).program) (hlenp ▸ hk)
  have heta : ({ startAddr := layout.start + .ofNat (Directives.size (layout q₁).program)
                 program := ((layout.after q₁) p).program } : Executable Instr Const) =
      (layout.after q₁) p := rfl
  simpa only [List.append_assoc, hlen1, heta] using h

theorem Layout.labels_sub_infix (layout : Layout Instr Const) (q₁ p q₂ : Program Instr Const)
    (hdisj : ∀ l ∈ q₁.definedLabels, l ∉ p.definedLabels) :
    ((layout.after q₁) p).labels ⊆ (layout (q₁ ++ p ++ q₂)).labels := by
  rw [Layout.apply_append, Layout.apply_append]
  exact Executable.labels_sub_infix layout.start (layout q₁).program ((layout.after q₁) p).program
    ((layout.after (q₁ ++ p)) q₂).program (by simpa only [Layout.apply_map_directive])

theorem Layout.labels_sub_append_right (layout : Layout Instr Const) (p q : Program Instr Const) :
    (layout p).labels ⊆ (layout (p ++ q)).labels := by
  simpa using layout.labels_sub_infix [] p q nofun

theorem Layout.labels_sub_append_left (layout : Layout Instr Const) (q p : Program Instr Const)
    (hdisj : ∀ l ∈ q.definedLabels, l ∉ p.definedLabels) :
    ((layout.after q) p).labels ⊆ (layout (q ++ p)).labels := by
  simpa using layout.labels_sub_infix q p [] hdisj

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
    (hk : p.findIdx? (·.isLabel fn) = some k)
    {contract : Int64 → Prop}
    (h : FnSpec (l p) fn contract) :
    contract ((l p).addrOf k) := by
  obtain ⟨entry, hentry, hc⟩ := h
  have hk' := l.label?_eq_some_addrOf p fn hk
  cases hentry.symm.trans hk'
  exact hc

end Kraken

export Kraken (Labels FnSpec)
