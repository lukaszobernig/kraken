module

/-
Omnisemantics, dynamic-alignment stepping, modular concatenation, and `SpecOf`/`Embedded` for X64.
-/

public import Kraken.X64.Semantics
import Kraken.Attribute
public import Kraken.OmniSemantics

@[expose] public section

@[kstep] def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .gp_unaligned _ _ => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v : α, (cont v).All post
  | .require_read_access _ cont => (cont ()).All post
  | .require_write_access _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

@[ksimp] theorem Effects.All_require_read_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_read_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

@[ksimp] theorem Effects.All_require_write_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_write_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

@[ksimp] theorem Int64.add_sub_cancel_left (a b : Int64) : a + (b - a) = b := by grind
@[ksimp] theorem Int64.ofBitVec_toBitVec_ksimp (a : Int64) : Int64.ofBitVec a.toBitVec = a := rfl

def step1 (e : Executable) (labels : Labels := e.labels) (s : MachineState)
    (post : @Post MachineState) : Prop :=
  ∀ env : LabelEnv, labels.Consistent env → (Executable.step e s .done env).All post

def straightlineStep (e : Executable) (s : MachineState) (post : @Post MachineState) : Prop :=
  (Executable.straightline e s .done).All post

/-- Single `Directive` stepping into `Eventually (step1 (layout p) labels)`.
For dynamic `.align log2Align true`, the `alignPad = 0` (0 steps) vs `alignPad > 0` (1 NOP step)
case split is absorbed here once and never exposed to user proofs or `kstep`. -/
theorem eventually_of_interp [layout : Layout] {p : Program}
    (hfit : layout.totalSize p < 2 ^ 64)
    {labels : Labels} {k : Nat} {d : Directive}
    (hd : p.stripLabels[k]? = some d)
    {post : @Post MachineState} {s : MachineData}
    (h : ∀ env : LabelEnv, labels.Consistent env →
      (@Directive.interp env d s ⟨layout.addrOf p k, layout.addrOf p (k + 1)⟩
        (fun s' => .done ⟨s', layout.addrOf p (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 (layout p) labels) post ⟨s, layout.addrOf p k⟩ := by
  have hsucc : layout.addrOf p (k + 1) =
      layout.addrOf p k + .ofNat (layout.dirSize (layout.addrOf p k) k d) :=
    layout.addrOf_succ p hd
  match hsize : layout.dirSize (layout.addrOf p k) k d with
  | 0 =>
    apply Eventually.done
    have h0 := h labels.toEnv (Kraken.Labels.Consistent.toEnv labels)
    cases d with
    | instr _ => exact absurd hsize (Nat.ne_of_gt (layout.instrSize_pos k))
    | label _ => simpa [hsucc, hsize, Directive.interp, Effects.All] using h0
    | byteArray bs =>
      have hbs : bs.size = 0 := hsize
      simpa [hsucc, hsize, Directive.interp, ByteArray.isEmpty, hbs, Effects.All] using h0
    | word n c =>
      have hn : n = 0 := hsize
      subst hn
      simpa [hsucc, hsize, Directive.interp, Effects.All] using h0
    | align m ex =>
      cases ex
      · simp [Directive.interp, Effects.All] at h0
      · simpa [hsucc, hsize, Directive.interp, Effects.All] using h0
  | sz' + 1 =>
    refine .step _ post ?_ fun _ => .done _
    intro env henv
    have hpos : 0 < layout.dirSize (layout.addrOf p k) k d := by omega
    dsimp only [Executable.step]
    rw [layout.directiveAt?_addrOf p hfit hd hpos]
    simpa [hsucc] using h env henv

theorem step_at [layout : Layout] {p : Program}
    (hfit : layout.totalSize p < 2 ^ 64)
    {labels : Labels} {k : Nat} {d : Directive}
    (hd : p.stripLabels[k]? = some d)
    {post : @Post MachineState} {s : MachineData}
    (h : ∀ env : LabelEnv, labels.Consistent env →
      (@Directive.interp env d s ⟨layout.addrOf p k, layout.addrOf p (k + 1)⟩
        (fun s' => .done ⟨s', layout.addrOf p (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All
          (fun mid => Eventually (step1 (layout p) labels) post mid)) :
    Eventually (step1 (layout p) labels) post ⟨s, layout.addrOf p k⟩ :=
  eventually_trans _ _ _ _ (eventually_of_interp hfit hd h) fun _ => id

/-- Step past an executable `.align log2Align` directive with zero user-visible case splitting. -/
theorem step_align [layout : Layout] {p : Program}
    (hfit : layout.totalSize p < 2 ^ 64)
    {labels : Labels} {k log2Align : Nat}
    (hd : p.stripLabels[k]? = some (.align log2Align true))
    {post : @Post MachineState} {s : MachineData}
    (h : Eventually (step1 (layout p) labels) post ⟨s, layout.addrOf p (k + 1)⟩) :
    Eventually (step1 (layout p) labels) post ⟨s, layout.addrOf p k⟩ :=
  step_at hfit hd (fun _ _ => by simpa [Directive.interp, Effects.All] using h)

section Concat
variable (layout : Layout) {L L₁ L₂ : Labels} {q₁ p q₂ q : Program}
  {s : MachineState} {mid post : @Post MachineState}

/-- Step simulation from an infix snippet `p` to `q₁ ++ p ++ q₂` under `L₁ ⊆ L₂`. -/
theorem Layout.subStep_infix (hL : L₁ ⊆ L₂)
    (hfit : layout.totalSize (q₁ ++ p ++ q₂) < 2 ^ 64) :
    SubStep (step1 ((layout.after q₁) p) L₁) (step1 (layout (q₁ ++ p ++ q₂)) L₂) := by
  rintro ⟨md, pc⟩ post h env henv
  have h1 := h env (henv.mono hL)
  dsimp only [Executable.step] at h1 ⊢
  cases hat : ((layout.after q₁) p).directiveAt? pc with
  | none => simp [hat, Effects.All] at h1
  | some c =>
    rw [hat] at h1
    rwa [layout.directiveAt?_infix q₁ p q₂ hfit hat]

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

/-- Step a single `Directive` of an embedded snippet `layout p` directly inside `Eventually (step1 e)`. -/
theorem step_at_sub [layout : Layout] {p : Program} {e : Executable}
    (hfit : layout.totalSize p < 2 ^ 64)
    (hsub : SubStep (step1 (layout p) e.labels) (step1 e))
    {k : Nat} {d : Directive}
    (hd : p.stripLabels[k]? = some d)
    {post : @Post MachineState} {s : MachineData}
    (h : ∀ env : LabelEnv, e.labels.Consistent env →
      (@Directive.interp env d s ⟨layout.addrOf p k, layout.addrOf p (k + 1)⟩
        (fun s' => .done ⟨s', layout.addrOf p (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All
          (fun mid => Eventually (step1 e) post mid)) :
    Eventually (step1 e) post ⟨s, layout.addrOf p k⟩ :=
  Eventually.bind (hsub.eventually (eventually_of_interp hfit hd h)) fun _ => id

/-- Step past an executable `.align log2Align` inside an embedded snippet without case splitting. -/
theorem step_align_sub [layout : Layout] {p : Program} {e : Executable}
    (hfit : layout.totalSize p < 2 ^ 64)
    (hsub : SubStep (step1 (layout p) e.labels) (step1 e))
    {k log2Align : Nat}
    (hd : p.stripLabels[k]? = some (.align log2Align true))
    {post : @Post MachineState} {s : MachineData}
    (h : Eventually (step1 e) post ⟨s, layout.addrOf p (k + 1)⟩) :
    Eventually (step1 e) post ⟨s, layout.addrOf p k⟩ :=
  step_at_sub hfit hsub hd (fun _ _ => by simpa [Directive.interp, Effects.All] using h)

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
    (hk : p.extractLabels.lookup fn = some k)
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
    (hk : p.extractLabels.lookup fn = some k)
    {s : MachineData} {post : @Post MachineState}
    (h : ∀ [layout : Layout],
      layout.totalSize p < 2 ^ 64 →
      (layout p).labels ⊆ e.labels →
      SubStep (step1 (layout p) e.labels) (step1 e) →
      Eventually (step1 e) post ⟨s, layout.addrOf p k⟩) :
    WPCall e fn s post :=
  hemb.fnSpec_of_label hk h
