module

/-
Omnisemantics and modular concatenation lemmas for AArch64.
-/

public import Kraken.AArch64.Semantics
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
  | .unaligned_sp .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v : α, (cont v).All L post
  | .require_read_access _ _ cont => (cont ()).All L post
  | .require_write_access _ _ cont => (cont ()).All L post
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
  | require_read_access _ _ cont ih => exact ih ()
  | require_write_access _ _ cont ih => exact ih ()
  | require_exec_access _ cont ih => exact ih ()
  | _ => exact False.elim

theorem Effects.All_lookup_label_of_eq {L : Labels} {l : Label} {a : Int64}
    (h : L.label? l = some a) (post : MachineState → Prop) (cont : Int64 → Effects) :
    (Effects.lookup_label l cont).All L post = (cont a).All L post := by
  simp [Effects.All, h]

def step1 (e : Executable) (labels : Labels := e.labels) (s : MachineState)
    (post : @Post MachineState) : Prop :=
  (Executable.step e s .done).All labels post

def straightlineStep (e : Executable) (s : MachineState) (post : @Post MachineState) : Prop :=
  (Executable.straightline e s .done).All e.labels post

private theorem Directives.interp_zero_prefix (layout : Layout) (p : Program)
    {pre rest : List (Kraken.Sized Directive)}
    (hmem : ∀ c ∈ pre, c ∈ (layout p).program)
    (hz : ∀ c ∈ pre, c.size = 0)
    (s : MachineData) (pc : Int64) (ret : Int64 → MachineData → Effects) :
    Directives.interp (pre ++ rest) s pc ret = Directives.interp rest s pc ret := by
  induction pre generalizing s with
  | nil => rfl
  | cons c pre ih =>
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp (hmem c List.mem_cons_self)
    obtain ⟨d', _, rfl⟩ := Option.map_eq_some_iff.mp (layout.apply_getElem? p m ▸ hm)
    have hz0 : layout.size d' m = 0 := hz _ List.mem_cons_self
    simp only [hz0, List.cons_append, Directives.interp, Int64.reduceOfNat, Int64.add_zero,
      inert_of_size_zero layout hz0]
    exact ih (fun c' hc' => hmem c' (List.mem_cons_of_mem _ hc'))
      (fun c' hc' => hz c' (List.mem_cons_of_mem _ hc')) s

theorem Directives.interp_directivesAtAddress_addrOf (layout : Layout) (p : Program)
    (hfit : Kraken.Directives.size (layout p).program < 2 ^ 64)
    {k : Nat} {d : Directive} (hd : p[k]? = some d) (hz : 0 < layout.size d k)
    (s : MachineData) (ret : Int64 → MachineData → Effects) :
    Directives.interp ((layout p).directivesAtAddress ((layout p).addrOf k)) s ((layout p).addrOf k) ret =
      Directives.interp [{directive := d, size := layout.size d k}] s ((layout p).addrOf k) ret := by
  have hc : (layout p).program[k]? = some {directive := d, size := layout.size d k} := by
    simp [Kraken.Layout.apply_getElem?, hd]
  obtain ⟨pre, hat, hpre⟩ := (layout p).directivesAtAddress_addrOf
    (fun _ _ => (layout p).sizeBefore_eq_of_addrOf_eq hfit) hc hz
  rw [hat]
  exact Directives.interp_zero_prefix layout p
    (fun c hc => Kraken.Executable.mem_of_mem_directivesAtAddress (hat ▸ List.mem_append_left _ hc))
    hpre s _ ret

theorem Directives.interp_directivesAtAddress_all_zero (layout : Layout) (p : Program) (pc : Int64)
    (h0 : ∀ c ∈ (layout p).directivesAtAddress pc, c.size = 0)
    (s : MachineData) (ret : Int64 → MachineData → Effects) :
    Directives.interp ((layout p).directivesAtAddress pc) s pc ret = ret pc s := by
  rw [← List.append_nil ((layout p).directivesAtAddress pc),
    Directives.interp_zero_prefix layout p
      (fun _ hc => Kraken.Executable.mem_of_mem_directivesAtAddress hc) h0]
  rfl

/-- Single-directive stepping into `Eventually (step1 (layout p) labels)`. -/
theorem eventually_of_interp [layout : Layout] {p : Program}
    (hfit : Kraken.Directives.size (layout p).program < 2 ^ 64)
    {labels : Labels} {k : Nat} {d : Directive} (hd : p[k]? = some d)
    {post : @Post MachineState} {s : MachineData}
    (h : (d.interp s ⟨(layout p).addrOf k, (layout p).addrOf (k + 1)⟩
      (fun s' => .done ⟨s', (layout p).addrOf (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All labels post) :
    Eventually (step1 (layout p) labels) post ⟨s, (layout p).addrOf k⟩ := by
  have hc : (layout p).program[k]? = some {directive := d, size := layout.size d k} := by
    simp [Kraken.Layout.apply_getElem?, hd]
  have hsucc : (layout p).addrOf (k + 1) = (layout p).addrOf k + .ofNat (layout.size d k) :=
    (layout p).addrOf_succ hc
  match hsize : layout.size d k with
  | 0 =>
    apply Eventually.done
    simpa [hsucc, hsize, inert_of_size_zero layout hsize, Effects.All] using h
  | _ + 1 =>
    refine .step _ post ?_ fun _ => .done _
    dsimp only [step1, Executable.step]
    rw [Directives.interp_directivesAtAddress_addrOf layout p hfit hd (by omega)]
    simpa [Directives.interp, hsucc, hsize] using h

theorem step_at [layout : Layout] {p : Program}
    (hfit : Kraken.Directives.size (layout p).program < 2 ^ 64)
    {labels : Labels} {k : Nat} {d : Directive} (hd : p[k]? = some d)
    {post : @Post MachineState} {s : MachineData}
    (h : (d.interp s ⟨(layout p).addrOf k, (layout p).addrOf (k + 1)⟩
      (fun s' => .done ⟨s', (layout p).addrOf (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All labels
        (fun mid => Eventually (step1 (layout p) labels) post mid)) :
    Eventually (step1 (layout p) labels) post ⟨s, (layout p).addrOf k⟩ :=
  eventually_trans _ _ _ _ (eventually_of_interp hfit hd h) fun _ => id

section Concat
variable (layout : Layout) {L L₁ L₂ : Labels} {q₁ p q₂ q : Program}
  {s : MachineState} {mid post : @Post MachineState}

/-- Step simulation from an infix snippet `p` to `q₁ ++ p ++ q₂` under `L₁ ⊆ L₂`. -/
theorem Layout.subStep_infix (hL : L₁ ⊆ L₂)
    (hfit : Kraken.Directives.size (layout (q₁ ++ p ++ q₂)).program < 2 ^ 64) :
    SubStep (step1 ((layout.after q₁) p) L₁) (step1 (layout (q₁ ++ p ++ q₂)) L₂) := by
  rintro ⟨md, pc⟩ post h
  dsimp only [step1, Executable.step] at h ⊢
  by_cases hpos : ∃ c ∈ ((layout.after q₁) p).directivesAtAddress pc, 0 < c.size
  · right
    obtain ⟨c, hc, hz⟩ := hpos
    obtain ⟨k, hk, rfl⟩ := Kraken.Executable.exists_of_mem_directivesAtAddress hc
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp ((layout.after q₁).apply_getElem? p k ▸ hk)
    have hk_lt : k < p.length := (List.getElem?_eq_some_iff.mp hd).1
    have hfit_sub : Kraken.Directives.size (((layout.after q₁) p).program) < 2 ^ 64 :=
      (layout.after q₁).size_left_lt (layout.size_after_lt (p := q₁) (q := p ++ q₂)
        (by simpa only [List.append_assoc] using hfit))
    have hd_big : (q₁ ++ p ++ q₂)[q₁.length + k]? = some d := by grind
    have hsz : @Kraken.Layout.size _ _ layout d (q₁.length + k) =
        @Kraken.Layout.size _ _ (layout.after q₁) d k := by
      rw [Kraken.Layout.size_after, Nat.add_comm]
    rw [Directives.interp_directivesAtAddress_addrOf (layout.after q₁) p hfit_sub hd hz] at h
    rw [← layout.addrOf_infix q₁ p q₂ (Nat.le_of_lt hk_lt),
      Directives.interp_directivesAtAddress_addrOf layout (q₁ ++ p ++ q₂) hfit hd_big (hsz ▸ hz),
      layout.addrOf_infix q₁ p q₂ (Nat.le_of_lt hk_lt), hsz]
    exact Effects.All_mono hL (fun _ hp => hp) _ h
  · left
    rw [Directives.interp_directivesAtAddress_all_zero (layout.after q₁) p pc
      (fun c hc => Classical.byContradiction fun hne => hpos ⟨c, hc, Nat.pos_of_ne_zero hne⟩)] at h
    exact h

theorem Layout.subStep_append_right (hL : L₁ ⊆ L₂)
    (hfit : Kraken.Directives.size (layout (p ++ q)).program < 2 ^ 64) :
    SubStep (step1 (layout p) L₁) (step1 (layout (p ++ q)) L₂) := by
  have h := layout.subStep_infix (q₁ := []) (p := p) (q₂ := q) hL hfit
  rwa [Kraken.Layout.after_nil] at h

theorem Layout.subStep_append_left (hL : L₁ ⊆ L₂)
    (hfit : Kraken.Directives.size (layout (q ++ p)).program < 2 ^ 64) :
    SubStep (step1 ((layout.after q) p) L₁) (step1 (layout (q ++ p)) L₂) := by
  rw [← List.append_nil (q ++ p)] at hfit ⊢
  exact layout.subStep_infix (q₁ := q) (p := p) (q₂ := []) hL hfit

theorem Layout.eventually_infix_of_sub (hL : L₁ ⊆ L₂)
    (hfit : Kraken.Directives.size (layout (q₁ ++ p ++ q₂)).program < 2 ^ 64)
    (h : Eventually (step1 ((layout.after q₁) p) L₁) post s) :
    Eventually (step1 (layout (q₁ ++ p ++ q₂)) L₂) post s :=
  (layout.subStep_infix hL hfit).eventually h

theorem Layout.eventually_append_right (hL : L₁ ⊆ L₂)
    (hfit : Kraken.Directives.size (layout (p ++ q)).program < 2 ^ 64)
    (h : Eventually (step1 (layout p) L₁) post s) :
    Eventually (step1 (layout (p ++ q)) L₂) post s :=
  (layout.subStep_append_right hL hfit).eventually h

theorem Layout.eventually_append_left (hL : L₁ ⊆ L₂)
    (hfit : Kraken.Directives.size (layout (q ++ p)).program < 2 ^ 64)
    (h : Eventually (step1 ((layout.after q) p) L₁) post s) :
    Eventually (step1 (layout (q ++ p)) L₂) post s :=
  (layout.subStep_append_left hL hfit).eventually h

/-- Closed-subprogram `append` (with no label-uniqueness side condition). -/
theorem Eventually.append [layout : Layout] (p₁ p₂ : Program)
    (hfit : Kraken.Directives.size (layout (p₁ ++ p₂)).program < 2 ^ 64)
    {post : @Post MachineState} {init : MachineState}
    (h : Eventually (step1 (layout p₁)) post init) :
    Eventually (step1 (layout (p₁ ++ p₂))) post init :=
  layout.eventually_append_right (layout.labels_sub_append_right p₁ p₂) hfit h

/-- Closed-subprogram `prepend` (requiring only disjoint defined labels). -/
theorem Eventually.prepend [layout : Layout] (p₁ p₂ : Program)
    (hfit : Kraken.Directives.size (layout (p₁ ++ p₂)).program < 2 ^ 64)
    (hdisj : ∀ l ∈ p₁.definedLabels, l ∉ p₂.definedLabels)
    {post : @Post MachineState} {init : MachineState}
    (h : Eventually (step1 ((layout.after p₁) p₂)) post init) :
    Eventually (step1 (layout (p₁ ++ p₂))) post init :=
  layout.eventually_append_left (layout.labels_sub_append_left p₁ p₂ hdisj) hfit h

/-- Sequential composition under a shared label environment `L`. -/
theorem Layout.eventually_seq
    (hfit : Kraken.Directives.size (layout (p ++ q)).program < 2 ^ 64)
    (h₁ : Eventually (step1 (layout p) L) mid s)
    (h₂ : ∀ st', mid st' → Eventually (step1 ((layout.after p) q) L) post st') :
    Eventually (step1 (layout (p ++ q)) L) post s :=
  eventually_trans _ _ _ _ (layout.eventually_append_right (Kraken.Labels.subset_refl L) hfit h₁)
    fun st' hst' => layout.eventually_append_left (Kraken.Labels.subset_refl L) hfit (h₂ st' hst')

end Concat
