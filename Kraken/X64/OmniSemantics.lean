module

/-
Omnisemantics, dynamic-alignment stepping, modular concatenation, and `SpecOf`/`Embedded` for X64.
-/

public import Kraken.X64.Semantics
import Kraken.Attribute
public import Kraken.OmniSemantics

@[expose] public section

@[kstep] def Effects.All (L : Labels) (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .lookup_label l cont =>
    match L.label? l with
    | some a => (cont a).All L post
    | none => False
  | .unimplemented _ => False
  | .gp_unaligned _ _ => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v : α, (cont v).All L post
  | .require_read_access _ cont => (cont ()).All L post
  | .require_write_access _ cont => (cont ()).All L post
  | .require_exec_access _ cont => (cont ()).All L post

/-- Monotonicity of `Effects.All` in both `Labels` (`L₁ ⊆ L₂`) and the postcondition (`P → Q`),
proved once by induction on `Effects` without inspecting individual instructions. -/
theorem Effects.All_mono {L₁ L₂ : Labels} (hL : L₁ ⊆ L₂) {P Q : @Post MachineState}
    (hPQ : ∀ s, P s → Q s) (eff : Effects) :
    eff.All L₁ P → eff.All L₂ Q := by
  induction eff with
  | done a => exact hPQ a
  | lookup_label l cont ih =>
    intro h0
    cases h : L₁.label? l with
    | none => simp [Effects.All, h] at h0
    | some a =>
      simp only [Effects.All, h] at h0
      simp only [Effects.All, hL l a h]
      exact ih a h0
  | undefined cont ih => exact fun h v => ih v (h v)
  | require_read_access _ cont ih => exact ih ()
  | require_write_access _ cont ih => exact ih ()
  | require_exec_access _ cont ih => exact ih ()
  | _ => exact False.elim

theorem Effects.All_lookup_label_of_eq {L : Labels} {l : Label} {a : Int64}
    (h : L.label? l = some a) (post : MachineState → Prop) (cont : Int64 → Effects) :
    (Effects.lookup_label l cont).All L post = (cont a).All L post := by
  simp [Effects.All, h]

@[ksimp] theorem Effects.All_require_read_access (L : Labels) (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_read_access addr bytes ok).All L post = (ok ()).All L post := by
  dsimp only [require_access]
  split <;> rfl

@[ksimp] theorem Effects.All_require_write_access (L : Labels) (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_write_access addr bytes ok).All L post = (ok ()).All L post := by
  dsimp only [require_access]
  split <;> rfl

@[ksimp] theorem Int64.add_sub_cancel_left (a b : Int64) : a + (b - a) = b := by grind
@[ksimp] theorem Int64.ofBitVec_toBitVec_ksimp (a : Int64) : Int64.ofBitVec a.toBitVec = a := rfl

def step1 (e : Executable) (labels : Labels := e.labels) (s : MachineState)
    (post : @Post MachineState) : Prop :=
  (Executable.step e s .done).All labels post

def straightlineStep (e : Executable) (s : MachineState) (post : @Post MachineState) : Prop :=
  (Executable.straightline e s .done).All e.labels post

/-- Single `CodeDirective` stepping into `Eventually (step1 (layout p) labels)`.
For dynamic `.align log2Align true`, the `alignPad = 0` (0 steps) vs `alignPad > 0` (1 NOP step)
case split is absorbed here once and never exposed to user proofs or `kstep`. -/
theorem eventually_of_interp [layout : Layout] {p : Program}
    (hfit : layout.totalSize p < 2 ^ 64)
    {labels : Labels} {k : Nat} {cd : CodeDirective}
    (hcd : p.splitLabels.body[k]? = some cd)
    {post : @Post MachineState} {s : MachineData}
    (h : (CodeDirective.interp cd s ⟨layout.addrOf p k, layout.addrOf p (k + 1)⟩
      (fun s' => .done ⟨s', layout.addrOf p (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All labels post) :
    Eventually (step1 (layout p) labels) post ⟨s, layout.addrOf p k⟩ := by
  have hsucc : layout.addrOf p (k + 1) =
      layout.addrOf p k + .ofNat (layout.codeDirSize (layout.addrOf p k) k cd) :=
    layout.addrOf_succ p hcd
  match hsize : layout.codeDirSize (layout.addrOf p k) k cd with
  | 0 =>
    apply Eventually.done
    cases cd with
    | instr _ => exact absurd hsize (Nat.ne_of_gt (layout.instrSize_pos k))
    | byteArray bs =>
      have h0 : bs.size = 0 := hsize
      simpa [hsucc, hsize, CodeDirective.interp, ByteArray.isEmpty, h0, Effects.All] using h
    | word n c =>
      have h0 : n = 0 := hsize
      subst h0
      simpa [hsucc, hsize, CodeDirective.interp, Effects.All] using h
    | align m ex =>
      cases ex
      · simp [CodeDirective.interp, Effects.All] at h
      · simpa [hsucc, hsize, CodeDirective.interp, Effects.All] using h
  | sz' + 1 =>
    refine .step _ post ?_ fun _ => .done _
    have hpos : 0 < layout.codeDirSize (layout.addrOf p k) k cd := by omega
    have hat := layout.itemAt?_addrOf p hfit hcd hpos
    dsimp only [step1, Executable.step]
    rw [hat]
    cases cd with
    | instr i =>
      simpa [Item.interp, CodeDirective.interp, Kraken.CodeDirective.toItem, hsucc] using h
    | byteArray bs =>
      have hne : bs.isEmpty = false := by grind [ByteArray.isEmpty, Kraken.Layout.codeDirSize]
      simp [CodeDirective.interp, hne, Effects.All] at h
    | word n c =>
      cases n with
      | zero => dsimp [Kraken.Layout.codeDirSize] at hpos; omega
      | succ _ => simp [CodeDirective.interp, Effects.All] at h
    | align m ex =>
      cases ex
      · simp [CodeDirective.interp, Effects.All] at h
      · simpa [Item.interp, CodeDirective.interp, Kraken.CodeDirective.toItem, Effects.All, hsucc] using h

theorem step_at [layout : Layout] {p : Program}
    (hfit : layout.totalSize p < 2 ^ 64)
    {labels : Labels} {k : Nat} {cd : CodeDirective}
    (hcd : p.splitLabels.body[k]? = some cd)
    {post : @Post MachineState} {s : MachineData}
    (h : (CodeDirective.interp cd s ⟨layout.addrOf p k, layout.addrOf p (k + 1)⟩
      (fun s' => .done ⟨s', layout.addrOf p (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All labels
        (fun mid => Eventually (step1 (layout p) labels) post mid)) :
    Eventually (step1 (layout p) labels) post ⟨s, layout.addrOf p k⟩ :=
  eventually_trans _ _ _ _ (eventually_of_interp hfit hcd h) fun _ => id

/-- Step past an executable `.align log2Align` directive with zero user-visible case splitting. -/
theorem step_align [layout : Layout] {p : Program}
    (hfit : layout.totalSize p < 2 ^ 64)
    {labels : Labels} {k log2Align : Nat}
    (hcd : p.splitLabels.body[k]? = some (.align log2Align true))
    {post : @Post MachineState} {s : MachineData}
    (h : Eventually (step1 (layout p) labels) post ⟨s, layout.addrOf p (k + 1)⟩) :
    Eventually (step1 (layout p) labels) post ⟨s, layout.addrOf p k⟩ :=
  step_at hfit hcd (by simpa [CodeDirective.interp, Effects.All] using h)

section Concat
variable (layout : Layout) {L L₁ L₂ : Labels} {q₁ p q₂ q : Program}
  {s : MachineState} {mid post : @Post MachineState}

/-- Step simulation from an infix snippet `p` to `q₁ ++ p ++ q₂` under `L₁ ⊆ L₂`. -/
theorem Layout.subStep_infix (hL : L₁ ⊆ L₂)
    (hfit : layout.totalSize (q₁ ++ p ++ q₂) < 2 ^ 64) :
    SubStep (step1 ((layout.after q₁) p) L₁) (step1 (layout (q₁ ++ p ++ q₂)) L₂) := by
  rintro ⟨md, pc⟩ post h
  dsimp only [step1, Executable.step] at h ⊢
  cases hat : ((layout.after q₁) p).itemAt? pc with
  | none => simp [hat, Effects.All] at h
  | some c =>
    rw [hat] at h
    rw [layout.itemAt?_infix q₁ p q₂ hfit hat]
    exact Effects.All_mono hL (fun _ hp => hp) _ h

theorem Layout.subStep_append_right (hL : L₁ ⊆ L₂)
    (hfit : layout.totalSize (p ++ q) < 2 ^ 64) :
    SubStep (step1 (layout p) L₁) (step1 (layout (p ++ q)) L₂) := by
  have h := layout.subStep_infix (q₁ := []) (p := p) (q₂ := q) hL hfit
  rwa [Kraken.Layout.after_nil] at h

theorem Layout.subStep_append_left (hL : L₁ ⊆ L₂)
    (hfit : layout.totalSize (q ++ p) < 2 ^ 64) :
    SubStep (step1 ((layout.after q) p) L₁) (step1 (layout (q ++ p)) L₂) := by
  rw [← List.append_nil (q ++ p)] at hfit ⊢
  exact layout.subStep_infix (q₁ := q) (p := p) (q₂ := []) hL hfit

theorem Layout.eventually_infix_of_sub (hL : L₁ ⊆ L₂)
    (hfit : layout.totalSize (q₁ ++ p ++ q₂) < 2 ^ 64)
    (h : Eventually (step1 ((layout.after q₁) p) L₁) post s) :
    Eventually (step1 (layout (q₁ ++ p ++ q₂)) L₂) post s :=
  (layout.subStep_infix hL hfit).eventually h

theorem Layout.eventually_append_right (hL : L₁ ⊆ L₂)
    (hfit : layout.totalSize (p ++ q) < 2 ^ 64)
    (h : Eventually (step1 (layout p) L₁) post s) :
    Eventually (step1 (layout (p ++ q)) L₂) post s :=
  (layout.subStep_append_right hL hfit).eventually h

theorem Layout.eventually_append_left (hL : L₁ ⊆ L₂)
    (hfit : layout.totalSize (q ++ p) < 2 ^ 64)
    (h : Eventually (step1 ((layout.after q) p) L₁) post s) :
    Eventually (step1 (layout (q ++ p)) L₂) post s :=
  (layout.subStep_append_left hL hfit).eventually h

/-- Closed-subprogram `append` (requires no disjointness because `p₁` wins label resolution). -/
theorem Eventually.append [layout : Layout] (p₁ p₂ : Program)
    (hfit : layout.totalSize (p₁ ++ p₂) < 2 ^ 64)
    {post : @Post MachineState} {init : MachineState}
    (h : Eventually (step1 (layout p₁)) post init) :
    Eventually (step1 (layout (p₁ ++ p₂))) post init :=
  layout.eventually_append_right (layout.labels_sub_append_right p₁ p₂) hfit h

/-- Closed-subprogram `prepend` (requiring only disjoint defined labels). -/
theorem Eventually.prepend [layout : Layout] (p₁ p₂ : Program)
    (hfit : layout.totalSize (p₁ ++ p₂) < 2 ^ 64)
    (hdisj : ∀ l ∈ p₁.definedLabels, l ∉ p₂.definedLabels)
    {post : @Post MachineState} {init : MachineState}
    (h : Eventually (step1 ((layout.after p₁) p₂)) post init) :
    Eventually (step1 (layout (p₁ ++ p₂))) post init :=
  layout.eventually_append_left (layout.labels_sub_append_left p₁ p₂ hdisj) hfit h

/-- Sequential composition under a shared label environment `L`. -/
theorem Layout.eventually_seq
    (hfit : layout.totalSize (p ++ q) < 2 ^ 64)
    (h₁ : Eventually (step1 (layout p) L) mid s)
    (h₂ : ∀ st', mid st' → Eventually (step1 ((layout.after p) q) L) post st') :
    Eventually (step1 (layout (p ++ q)) L) post s :=
  eventually_trans _ _ _ _ (layout.eventually_append_right (Kraken.Labels.subset_refl L) hfit h₁)
    fun st' hst' => layout.eventually_append_left (Kraken.Labels.subset_refl L) hfit (h₂ st' hst')

end Concat

/-! ## Function Specifications & Modular Snippet Embedding (`SpecOf`, `WPCall`, `Embedded`) -/

abbrev SpecOf (fn : Label) := Kraken.SpecOf Instr ConstExpr fn

/-- Execute from a resolved entry address `entry` in ambient executable `e`
(also directly usable for indirect calls such as `call *%rax`). -/
abbrev WPCallAt (e : Executable) (entry : Int64) (s : MachineData) (post : @Post MachineState) : Prop :=
  Eventually (step1 e) post ⟨s, entry⟩

/-- Assembly analogue of `bedrock2.WeakestPrecondition.call`:
`fn` resolves in `e.labels` and executing from that address in `e` satisfies `post`. -/
def WPCall (e : Executable) (fn : Label) (s : MachineData) (post : @Post MachineState) : Prop :=
  FnSpec e fn fun entry => WPCallAt e entry s post

/-- Step a single `CodeDirective` of an embedded snippet `layout p` directly inside `Eventually (step1 e)`. -/
theorem step_at_sub [layout : Layout] {p : Program} {e : Executable}
    (hfit : layout.totalSize p < 2 ^ 64)
    (hsub : SubStep (step1 (layout p) e.labels) (step1 e))
    {k : Nat} {cd : CodeDirective}
    (hcd : p.splitLabels.body[k]? = some cd)
    {post : @Post MachineState} {s : MachineData}
    (h : (CodeDirective.interp cd s ⟨layout.addrOf p k, layout.addrOf p (k + 1)⟩
      (fun s' => .done ⟨s', layout.addrOf p (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All e.labels
        (fun mid => Eventually (step1 e) post mid)) :
    Eventually (step1 e) post ⟨s, layout.addrOf p k⟩ :=
  Eventually.bind (hsub.eventually (eventually_of_interp hfit hcd h)) fun _ => id

/-- Step past an executable `.align log2Align` inside an embedded snippet without case splitting. -/
theorem step_align_sub [layout : Layout] {p : Program} {e : Executable}
    (hfit : layout.totalSize p < 2 ^ 64)
    (hsub : SubStep (step1 (layout p) e.labels) (step1 e))
    {k log2Align : Nat}
    (hcd : p.splitLabels.body[k]? = some (.align log2Align true))
    {post : @Post MachineState} {s : MachineData}
    (h : Eventually (step1 e) post ⟨s, layout.addrOf p (k + 1)⟩) :
    Eventually (step1 e) post ⟨s, layout.addrOf p k⟩ :=
  step_at_sub hfit hsub hcd (by simpa [CodeDirective.interp, Effects.All] using h)

/-- `Embedded p e` asserts that snippet `p` is laid out inside ambient executable `e`
with non-shadowed defined labels and step simulation under any label extension `L`. -/
inductive Embedded (p : Program) (e : Executable) : Prop where
  | intro (layout : Layout)
      (fit : layout.totalSize p < 2 ^ 64)
      (labels_sub : (layout p).labels ⊆ e.labels)
      (subStep : ∀ L : Labels, e.labels ⊆ L → SubStep (step1 (layout p) L) (step1 e L))

theorem Embedded.self (layout : Layout) (p : Program)
    (hfit : layout.totalSize p < 2 ^ 64) :
    Embedded p (layout p) :=
  ⟨layout, hfit, Kraken.Labels.subset_refl _, fun L _ => SubStep.refl (step1 (layout p) L)⟩

theorem Embedded.of_infix (layout : Layout) (q₁ p q₂ : Program)
    (hdisj : ∀ l ∈ q₁.definedLabels, l ∉ p.definedLabels)
    (hfit : layout.totalSize (q₁ ++ p ++ q₂) < 2 ^ 64) :
    Embedded p (layout (q₁ ++ p ++ q₂)) :=
  ⟨layout.after q₁,
    (layout.after q₁).size_left_lt (layout.size_after_lt (p := q₁) (q := p ++ q₂)
      (by simpa only [List.append_assoc] using hfit)),
    layout.labels_sub_infix q₁ p q₂ hdisj,
    fun L _ => layout.subStep_infix (Kraken.Labels.subset_refl L) hfit⟩

theorem Embedded.append_right (layout : Layout) {p : Program} (p₁ p₂ : Program)
    (hfit : layout.totalSize (p₁ ++ p₂) < 2 ^ 64)
    (hemb : Embedded p (layout p₁)) :
    Embedded p (layout (p₁ ++ p₂)) := by
  rcases hemb with ⟨l', hfit_p, hlbl_p, hsub_p⟩
  have hsub12 := layout.labels_sub_append_right p₁ p₂
  exact ⟨l', hfit_p, Kraken.Labels.subset_trans hlbl_p hsub12, fun L hL =>
    (hsub_p L (Kraken.Labels.subset_trans hsub12 hL)).trans
      (layout.subStep_append_right (Kraken.Labels.subset_refl L) hfit)⟩

theorem Embedded.append_left (layout : Layout) {p : Program} (p₁ p₂ : Program)
    (hdisj : ∀ l ∈ p₁.definedLabels, l ∉ p₂.definedLabels)
    (hfit : layout.totalSize (p₁ ++ p₂) < 2 ^ 64)
    (hemb : Embedded p ((layout.after p₁) p₂)) :
    Embedded p (layout (p₁ ++ p₂)) := by
  rcases hemb with ⟨l', hfit_p, hlbl_p, hsub_p⟩
  have hsub12 := layout.labels_sub_append_left p₁ p₂ hdisj
  exact ⟨l', hfit_p, Kraken.Labels.subset_trans hlbl_p hsub12, fun L hL =>
    (hsub_p L (Kraken.Labels.subset_trans hsub12 hL)).trans
      (layout.subStep_append_left (Kraken.Labels.subset_refl L) hfit)⟩

theorem Embedded.of_append_right (layout : Layout) (p₁ p₂ : Program)
    (hfit : layout.totalSize (p₁ ++ p₂) < 2 ^ 64) :
    Embedded p₁ (layout (p₁ ++ p₂)) :=
  Embedded.append_right layout p₁ p₂ hfit (Embedded.self layout p₁ (layout.size_left_lt hfit))

theorem Embedded.of_append_left (layout : Layout) (p₁ p₂ : Program)
    (hdisj : ∀ l ∈ p₁.definedLabels, l ∉ p₂.definedLabels)
    (hfit : layout.totalSize (p₁ ++ p₂) < 2 ^ 64) :
    Embedded p₂ (layout (p₁ ++ p₂)) :=
  Embedded.append_left layout p₁ p₂ hdisj hfit
    (Embedded.self (layout.after p₁) p₂ (layout.size_after_lt hfit))

/-- Unpack `Embedded p e` to prove `FnSpec e fn contract` where `fn` resolves to body index `k` of `p`. -/
theorem Embedded.fnSpec_of_label {p : Program} {e : Executable}
    (hemb : Embedded p e) {fn : Label} {k : Nat}
    (hk : p.splitLabels.labels.lookup fn = some k)
    {contract : Int64 → Prop}
    (h : ∀ [layout : Layout],
      layout.totalSize p < 2 ^ 64 →
      (layout p).labels ⊆ e.labels →
      SubStep (step1 (layout p) e.labels) (step1 e) →
      contract (layout.addrOf p k)) :
    FnSpec e fn contract := by
  rcases hemb with ⟨layout, hfit, hlocal, hsub⟩
  exact ⟨layout.addrOf p k,
    hlocal fn _ (Kraken.Layout.label?_eq_some_addrOf p fn hk),
    @h layout hfit hlocal (hsub e.labels (Kraken.Labels.subset_refl _))⟩

theorem Embedded.wpCall_of_label {p : Program} {e : Executable}
    (hemb : Embedded p e) {fn : Label} {k : Nat}
    (hk : p.splitLabels.labels.lookup fn = some k)
    {s : MachineData} {post : @Post MachineState}
    (h : ∀ [layout : Layout],
      layout.totalSize p < 2 ^ 64 →
      (layout p).labels ⊆ e.labels →
      SubStep (step1 (layout p) e.labels) (step1 e) →
      Eventually (step1 e) post ⟨s, layout.addrOf p k⟩) :
    WPCall e fn s post :=
  hemb.fnSpec_of_label hk h
