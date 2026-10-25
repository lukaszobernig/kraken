module

import Kraken.Attribute
public import Kraken.Semantics

@[expose] public section

/-
Common Kraken Temporal Logic and OmniSemantics.
-/

abbrev Post {State : Type} := State → Prop

-- NOTE: 'initial' cannot be moved to the left of the colon as a parameter
-- because it varies in the recursive call in the 'step' constructor (it becomes 'mid').
inductive Eventually {State : Type} (trans : State → Post → Prop) (post : Post) : Post
  | done (initial: State):
      post initial →
      Eventually trans post initial
  | step (initial: State):
      (mid_p: Post) →
      trans initial mid_p →
      (forall (mid: State), mid_p mid → Eventually trans post mid) →
      Eventually trans post initial

theorem step_cps {State : Type} (trans : State → Post → Prop) (post : Post) (initial : State) :
  trans initial (fun mid => Eventually trans post mid) → Eventually trans post initial :=
  by
    intro h
    exact .step initial _ h (fun _ => id)

theorem eventually_trans {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (e : Eventually trans p initial)
  (h : ∀ s, p s → Eventually trans q s) :
    Eventually trans q initial
  := by
    induction e with
    | done initial hp => exact h initial hp
    | step initial mid_p ht _ ih => exact .step initial mid_p ht ih

theorem eventually_weaken {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (h : ∀ s, p s → q s) :
    Eventually trans p initial → Eventually trans q initial
  := by
    exact fun hp => eventually_trans trans p q initial hp fun s hs => .done s (h s hs)

theorem Eventually.bind {State : Type} {trans : State → Post → Prop} {p q : Post} {s : State}
    (h₁ : Eventually trans p s) (h₂ : ∀ s', p s' → Eventually trans q s') :
    Eventually trans q s :=
  eventually_trans trans p q s h₁ h₂

-- A loop down to 0
theorem reg_dec_loop {State : Type} (trans : State → Post → Prop) (post : Post) (initial : State) (invariant : Nat → Post) (n : Nat) :
  -- if:
  -- invariant holds before entering the loop
  invariant n initial ∧
  -- final iteration allows proving `post`
  (∀ state, invariant 0 state → Eventually trans post state) ∧
  -- while iterating, we eventually re-establish the invariant
  (∀ state k, k ≠ 0 → invariant k state → Eventually trans (invariant (k - 1)) state) →
  -- then: we can prove the post
  Eventually trans post initial
  := by
    rintro ⟨hinv, hzero, hnz⟩
    if h : n = 0 then
      exact hzero initial (h ▸ hinv)
    else
      exact eventually_trans trans (invariant (n - 1)) post initial
        (hnz initial n h hinv) fun s hs =>
          reg_dec_loop trans post s invariant (n - 1) ⟨hs, hzero, hnz⟩

-- Tailrec-style loop rule
-- Adapted from: https://github.com/mit-plv/bedrock2/blob/8ec2c459bbf16d6cf2baa7d433ae211a243b1011/bedrock2/src/bedrock2/Loops.v#L48
-- This version moves the choice inside the Eventually postcondition.
theorem tailrec_loop {State Measure : Type _} {Ghost : Sort _}
  (trans : State → Post → Prop) (post : Post) (initial : State)
  (P Q : Measure → Ghost → Post)
  (lt : Measure → Measure → Prop)
  (Hwf : WellFounded lt)
  (v0 : Measure) (g0 : Ghost) :
  P v0 g0 initial →
  (∀ v g state, P v g state →
    Eventually trans (fun mid_s =>
      (Q v g mid_s) ∨
      (∃ v' g', P v' g' mid_s ∧ lt v' v ∧ (∀ t_s, Q v' g' t_s → Q v g t_s))
    ) state) →
  (∀ state, Q v0 g0 state → post state) →
  Eventually trans post initial := by
  intro hP hbody hpost
  have h_general : ∀ v g state, P v g state → (∀ t_s, Q v g t_s → Q v0 g0 t_s) → Eventually trans post state := by
    intro v
    induction v using Hwf.induction with
    | h v ih =>
      intro g state hP_state hQ_impl
      have hstep := hbody v g state hP_state
      apply eventually_trans trans _ post state hstep
      intro mid_state h_mid
      match h_mid with
      | .inl hQ =>
        apply Eventually.done
        apply hpost
        apply hQ_impl
        apply hQ
      | .inr ⟨v', ⟨g', ⟨hP_mid, hlt, hQ_impl'⟩⟩⟩ =>
        apply ih v' hlt g' mid_state hP_mid
        intro t_s hQ_t
        apply hQ_impl
        apply hQ_impl'
        apply hQ_t
  apply h_general v0 g0 initial hP
  intro t_s hQ_t
  apply hQ_t

theorem tailrec_loop_cps {State Measure : Type _} {Ghost : Sort _}
  (trans : State → Post → Prop) (post : Post) (initial : State)
  (P Q : Measure → Ghost → Post)
  (lt : Measure → Measure → Prop)
  (Hwf : WellFounded lt)
  (v0 : Measure) (g0 : Ghost) :
  Eventually trans (fun mid_s => Q v0 g0 mid_s ∨ P v0 g0 mid_s) initial →
  (∀ v g state, P v g state →
    Eventually trans (fun mid_s =>
      (Q v g mid_s) ∨
      (∃ v' g', P v' g' mid_s ∧ lt v' v ∧ (∀ t_s, Q v' g' t_s → Q v g t_s))
    ) state) →
  (∀ state, Q v0 g0 state → Eventually trans post state) →
  Eventually trans post initial := by
  intro hinit hbody hpost
  refine eventually_trans trans _ post initial hinit ?_
  rintro mid_s (hQ | hP)
  · exact hpost mid_s hQ
  · exact eventually_trans trans (Q v0 g0) post mid_s
      (tailrec_loop trans (Q v0 g0) mid_s P Q lt Hwf v0 g0 hP hbody (fun _ h => h))
      hpost

@[kstep] def Kraken.Effects.All {MD : Type} (post : Kraken.MachineState MD → Prop) :
    Kraken.Effects MD → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Kraken.Effects.undefined _ α _ cont => ∀ v : α, (cont v).All post
  | .require_read_access _ _ cont => (cont ()).All post
  | .require_write_access _ _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

def step1 {D MD : Type} [ArchDirective D MD]
    (e : Kraken.Executable D) (s : Kraken.MachineState MD)
    (post : @Post (Kraken.MachineState MD)) : Prop :=
  (e.step s .done).All post

theorem Effects.undefined_mono {MD α : Type} [NondetSupportingType α]
    {k₁ k₂ : α → Kraken.Effects MD} {P Q : Kraken.MachineState MD → Prop}
    (hk : ∀ v, (k₁ v).All P → (k₂ v).All Q) :
    (Kraken.Effects.undefined k₁).All P → (Kraken.Effects.undefined k₂).All Q :=
  fun h v => hk v (h v)

theorem MachineData.load_mono {MD : Type} [HasDataMem MD]
    (s : MD) (addr : BitVec 64) (w : Width)
    {k₁ k₂ : w.type → MD → Kraken.Effects MD}
    {P Q : Kraken.MachineState MD → Prop}
    (hk : ∀ v s', (k₁ v s').All P → (k₂ v s').All Q) :
    (MachineData.load s addr w k₁).All P → (MachineData.load s addr w k₂).All Q := by
  unfold MachineData.load
  dsimp only [Kraken.Effects.All]
  split
  · exact hk _ _
  · exact False.elim

theorem MachineData.store_mono {MD : Type} [HasDataMem MD]
    (s : MD) (addr : BitVec 64) {w : Width} (v : w.type)
    {k₁ k₂ : MD → Kraken.Effects MD}
    {P Q : Kraken.MachineState MD → Prop}
    (hk : ∀ s', (k₁ s').All P → (k₂ s').All Q) :
    (MachineData.store s addr v k₁).All P → (MachineData.store s addr v k₂).All Q := by
  unfold MachineData.store
  dsimp only [Kraken.Effects.All]
  split
  · exact hk _
  · exact False.elim

class OmniDirective (D : Type) {MD : outParam Type}
    [ArchDirective D MD] : Prop where
  interp_mono : ∀ [Labels] (d : D) (s : MD) (p : Std.Rco Int64)
    {P Q : Kraken.MachineState MD → Prop}
    {next₁ next₂ : MD → Kraken.Effects MD}
    {jmp₁ jmp₂ : Int64 → MD → Kraken.Effects MD},
    (∀ s', (next₁ s').All P → (next₂ s').All Q) →
    (∀ a s', (jmp₁ a s').All P → (jmp₂ a s').All Q) →
    (ArchDirective.interp d s p next₁ jmp₁).All P →
    (ArchDirective.interp d s p next₂ jmp₂).All Q

/-- `d` is inert if it falls through with the same machine state and no observable effect. -/
def Directive.Inert {D MD : Type} [ArchDirective D MD]
    (d : D) : Prop :=
  ∀ [Labels] (s : MD) (p : Std.Rco Int64)
    (next : MD → Kraken.Effects MD)
    (jmp : Int64 → MD → Kraken.Effects MD)
    (post : @Post (Kraken.MachineState MD)),
    (ArchDirective.interp d s p next jmp).All post ↔ (next s).All post

/-- Abstract validity assumptions about the `Layout` of a program `prog`. -/
class Layout.Valid {D MD : Type} [ArchDirective D MD]
    [layout : Kraken.Layout D] (prog : List D) : Prop where
  /-- Any directive that occupies zero space in the executable must be semantically inert. -/
  zero_inert : ∀ i d, prog[i]? = some d → layout.size i = 0 → Directive.Inert d
  /-- Two directives at the same address have the same offset in the executable. -/
  addr_determines_offset : ∀ j k, (layout prog).addrOf j = (layout prog).addrOf k →
    (layout prog).sizeBefore j = (layout prog).sizeBefore k

section
variable {D MD : Type} [ArchDirective D MD]

theorem Directives.interp_inert_append [Labels] {pre rest : List (Kraken.Sized D)}
    (hpre : ∀ c ∈ pre, c.size = 0 ∧ Directive.Inert c.directive) (s : MD) (pc : Int64)
    (ret : Int64 → MD → Kraken.Effects MD)
    (post : @Post (Kraken.MachineState MD)) :
    (Directives.interp (pre ++ rest) s pc ret).All post ↔
      (Directives.interp rest s pc ret).All post := by
  induction pre generalizing s with
  | nil => rfl
  | cons c pre ih =>
    obtain ⟨hz, hinert⟩ := hpre c List.mem_cons_self
    obtain ⟨d, z⟩ := c
    dsimp only at hz hinert
    subst hz
    have h0 : pc + Int64.ofNat 0 = pc := by simp
    simp only [List.cons_append, Directives.interp, h0]
    rw [hinert]
    exact ih (fun c hc => hpre c (List.mem_cons_of_mem _ hc)) s

variable [layout : Kraken.Layout D] {prog : List D}
  [hv : Layout.Valid prog]

theorem Directive.inert_of_size_zero {d : D}
    (h : {directive := d, size := 0} ∈ (layout prog).program) : Directive.Inert d := by
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp h
  rw [Kraken.Layout.apply_getElem?] at hm
  obtain ⟨d', hd', h_eq⟩ := Option.map_eq_some_iff.mp hm
  injection h_eq with hd_eq hz_eq
  subst hd_eq
  exact hv.zero_inert m d' hd' hz_eq

theorem eventually_of_getElem? {k : Nat} {d : D}
    (hd_prog : prog[k]? = some d) {post : @Post (Kraken.MachineState MD)} {s : MD}
    (h : (@ArchDirective.interp _ _ _ (Kraken.Executable.labels (layout prog)) d s
      ⟨(layout prog).addrOf k, (layout prog).addrOf (k + 1)⟩
      (fun s' => .done ⟨s', (layout prog).addrOf (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 (layout prog)) post ⟨s, (layout prog).addrOf k⟩ := by
  have hd : (layout prog).program[k]? = some {directive := d, size := layout.size k} := by
    rw [Kraken.Layout.apply_getElem?, hd_prog]; rfl
  rw [Kraken.Executable.addrOf_apply_succ hd_prog] at h
  rcases Nat.eq_zero_or_pos (layout.size k) with h0 | hz
  · rw [h0] at hd h
    letI := Kraken.Executable.labels (layout prog)
    rw [Directive.inert_of_size_zero (List.mem_of_getElem? hd)] at h
    have h0' : (layout prog).addrOf k + Int64.ofNat 0 = (layout prog).addrOf k := by simp
    rw [h0'] at h
    exact Eventually.done _ h
  · refine Eventually.step _ post ?_ fun _ hb => Eventually.done _ hb
    obtain ⟨pre, hat, hpre⟩ :=
      Kraken.Executable.directivesAtAddress_addrOf (layout prog) hv.addr_determines_offset hd hz
    have hinert : ∀ c ∈ pre, c.size = 0 ∧ Directive.Inert c.directive := fun c hc =>
      ⟨hpre c hc, Directive.inert_of_size_zero (prog := prog) (hpre c hc ▸
        Kraken.Executable.mem_of_mem_directivesAtAddress (hat ▸ List.mem_append_left _ hc))⟩
    letI := Kraken.Executable.labels (layout prog)
    dsimp only [step1, Kraken.Executable.step]
    rw [hat]
    refine (Directives.interp_inert_append hinert _ _ _ _).mpr ?_
    simpa only [Directives.interp] using h

variable [OmniDirective D]

omit layout [OmniDirective D] in
theorem Eventually.bind_at {e : Kraken.Executable D} {p q : @Post (Kraken.MachineState MD)}
    {s : MD} {pc pc' : Int64}
    (h₁ : Eventually (step1 e) p ⟨s, pc'⟩) (hpc : pc = pc')
    (h₂ : ∀ s', p s' → Eventually (step1 e) q s') :
    Eventually (step1 e) q ⟨s, pc⟩ :=
  hpc ▸ eventually_trans (step1 e) p q ⟨s, pc'⟩ h₁ h₂

/-- Specification for an `Executable` starting at `pc` (defaulting to `e.startAddr`)
in state `s₀`, requiring `pre` and ensuring `post` eventually holds. -/
@[reducible]
def Kraken.Executable.Spec (e : Kraken.Executable D) (s₀ : MD)
    (pc : Int64 := e.startAddr)
    (pre : Prop := True)
    (post : @Post (Kraken.MachineState MD)) : Prop :=
  pre → Eventually (step1 e) post ⟨s₀, pc⟩

omit layout [OmniDirective D] in
theorem Kraken.Executable.Spec.bind {e : Kraken.Executable D} {pre : Prop}
    {p q : @Post (Kraken.MachineState MD)} {s : MD} {pc : Int64}
    (h₁ : e.Spec s (pc := pc) (pre := pre) (post := p))
    (h₂ : ∀ s', p s' → Eventually (step1 e) q s')
    (hpre : pre := by trivial) :
    Eventually (step1 e) q ⟨s, pc⟩ :=
  eventually_trans (step1 e) p q ⟨s, pc⟩ (h₁ hpre) h₂

omit layout [OmniDirective D] in
theorem Kraken.Executable.Spec.bind_at {e : Kraken.Executable D} {pre : Prop}
    {p q : @Post (Kraken.MachineState MD)} {s : MD} {pc pc' : Int64}
    (h₁ : e.Spec s (pc := pc') (pre := pre) (post := p))
    (hpc : pc = pc')
    (h₂ : ∀ s', p s' → Eventually (step1 e) q s')
    (hpre : pre := by trivial) :
    Eventually (step1 e) q ⟨s, pc⟩ :=
  Eventually.bind_at (h₁ hpre) hpc h₂

omit layout in
theorem Directives.interp_mono [Labels] (cs : List (Kraken.Sized D)) (s : MD) (pc : Int64)
    {ret₁ ret₂ : Int64 → MD → Kraken.Effects MD}
    {P Q : Kraken.MachineState MD → Prop}
    (hret : ∀ a s', (ret₁ a s').All P → (ret₂ a s').All Q) :
    (Directives.interp cs s pc ret₁).All P →
    (Directives.interp cs s pc ret₂).All Q := by
  induction cs generalizing s pc with
  | nil => exact hret pc s
  | cons c cs ih =>
    exact OmniDirective.interp_mono c.directive s ⟨pc, pc + .ofNat c.size⟩
      (fun s' => ih s' (pc + .ofNat c.size)) hret

/-- Symbolic execution of all directives in an `Executable` starting from `e.startAddr`. -/
def Kraken.Executable.Exec [Labels] (e : Kraken.Executable D) (s : MD)
    (post : @Post (Kraken.MachineState MD)) : Prop :=
  (Directives.interp e.program s e.startAddr (fun pc s' => .done ⟨s', pc⟩)).All post

/-- Specification for straight-line symbolic execution of all directives in an `Executable`
starting from `e.startAddr` in state `s₀`, requiring `pre` and ensuring `post`. -/
@[reducible]
def Kraken.Executable.ExecSpec [Labels] (e : Kraken.Executable D) (s₀ : MD)
    (pre : Prop := True)
    (post : @Post (Kraken.MachineState MD)) : Prop :=
  pre → e.Exec s₀ post

omit layout in
theorem Kraken.Executable.Exec.mono [Labels] {e : Kraken.Executable D} {s : MD}
    {P Q : @Post (Kraken.MachineState MD)}
    (h : e.Exec s P) (hpq : ∀ st, P st → Q st) : e.Exec s Q :=
  Directives.interp_mono e.program s e.startAddr
    (ret₁ := fun pc s' => .done ⟨s', pc⟩) (ret₂ := fun pc s' => .done ⟨s', pc⟩)
    (fun a s' hp => hpq ⟨s', a⟩ hp) h

theorem step1_cps_slice (k n : Nat) (post : @Post (Kraken.MachineState MD))
    {s : MD} {pc : Int64} (hpc : pc = (layout prog).addrOf k)
    (h : (@Directives.interp _ _ _ (Kraken.Executable.labels (layout prog))
          (((layout prog).program.drop k).take n) s ((layout prog).addrOf k)
          (fun pc s => .done ⟨s, pc⟩)).All
        (fun mid => Eventually (step1 (layout prog)) post mid)) :
    Eventually (step1 (layout prog)) post ⟨s, pc⟩ := by
  subst hpc
  letI := Kraken.Executable.labels (layout prog)
  induction n generalizing k s with
  | zero =>
    simpa only [List.take_zero, Directives.interp, Kraken.Effects.All] using h
  | succ n ih =>
    by_cases hk : k < prog.length
    · have hd_prog : prog[k]? = some prog[k] := List.getElem?_eq_getElem hk
      have hd_exe : (layout prog).program[k]? = some {directive := prog[k], size := layout.size k} := by
        rw [Kraken.Layout.apply_getElem?, hd_prog]; rfl
      obtain ⟨hlt_exe, hget_exe⟩ := List.getElem?_eq_some_iff.mp hd_exe
      rw [List.drop_eq_getElem_cons hlt_exe, hget_exe, List.take_succ_cons,
          Directives.interp, ← Kraken.Executable.addrOf_apply_succ hd_prog] at h
      have hstep := OmniDirective.interp_mono prog[k] s
        ⟨(layout prog).addrOf k, (layout prog).addrOf (k + 1)⟩
        (next₂ := fun s' => .done ⟨s', (layout prog).addrOf (k + 1)⟩)
        (jmp₂ := fun a s' => .done ⟨s', a⟩)
        (Q := fun mid => Eventually (step1 (layout prog)) post mid)
        (fun s' hs' => ih (k + 1) hs')
        (fun _ _ ha => ha)
        h
      exact eventually_trans _ _ _ _ (eventually_of_getElem? hd_prog hstep) (fun _ h => h)
    · have hdrop : (layout prog).program.drop k = [] :=
        List.drop_eq_nil_of_le (by simp [Kraken.Layout.apply]; omega)
      simpa only [hdrop, List.take_nil, Directives.interp, Kraken.Effects.All] using h

theorem step1_cps_at (k : Nat) (post : @Post (Kraken.MachineState MD))
    {s : MD} {pc : Int64} (hpc : pc = (layout prog).addrOf k)
    (h : (@Directives.interp _ _ _ (Kraken.Executable.labels (layout prog))
          ((layout prog).program.drop k) s ((layout prog).addrOf k)
          (fun pc s => .done ⟨s, pc⟩)).All
        (fun mid => Eventually (step1 (layout prog)) post mid)) :
    Eventually (step1 (layout prog)) post ⟨s, pc⟩ := by
  refine step1_cps_slice k (layout prog).program.length post hpc ?_
  rw [List.take_of_length_le (by simp)]
  exact h

theorem step1_cps (post : @Post (Kraken.MachineState MD))
    (initial : Kraken.MachineState MD)
    (h : (@Directives.interp _ _ _ (Kraken.Executable.labels (layout prog))
          ((layout prog).directivesFromAddress initial.pc) initial.data initial.pc
          (fun pc s => .done ⟨s, pc⟩)).All
        (fun mid => Eventually (step1 (layout prog)) post mid)) :
    Eventually (step1 (layout prog)) post initial := by
  rcases initial with ⟨s, pc⟩
  rcases Kraken.Executable.directivesFromAddress_cases (layout prog) pc with hnil | ⟨j, _, hpc, hdrop⟩
  · simpa only [hnil, Directives.interp, Kraken.Effects.All] using h
  · rw [hdrop, ← hpc] at h
    exact step1_cps_at j post hpc.symm h

theorem Kraken.Executable.Exec.eventually {s : MD} {post : @Post (Kraken.MachineState MD)}
    (h : @Kraken.Executable.Exec _ _ _ (Kraken.Executable.labels (layout prog)) (layout prog) s post) :
    Eventually (step1 (layout prog)) post ⟨s, layout.start⟩ := by
  letI := Kraken.Executable.labels (layout prog)
  refine step1_cps_at 0 post (by simp [Kraken.Layout.apply]) ?_
  simpa only [List.drop_zero, Kraken.Executable.addrOf_zero, Kraken.Executable.Exec] using
    h.mono (fun mid hmid => Eventually.done mid hmid)

theorem step1_cps_subprog {sub : List D}
    (k : Nat) {s : MD} {pc : Int64} {P : Kraken.Layout D → @Post (Kraken.MachineState MD)}
    {post : @Post (Kraken.MachineState MD)}
    (hsub : (prog.drop k).take sub.length = sub)
    (hpc : pc = (layout prog).addrOf k)
    (hexec : ∀ [layout' : Kraken.Layout D] [Labels], (layout' sub).Exec s (P layout'))
    (hcont : ∀ s' pc', P (layout.shift prog k) ⟨s', pc'⟩ →
      Eventually (step1 (layout prog)) post ⟨s', pc'⟩) :
    Eventually (step1 (layout prog)) post ⟨s, pc⟩ := by
  letI := Kraken.Executable.labels (layout prog)
  refine step1_cps_slice k sub.length post hpc ?_
  rw [← Kraken.Layout.program_shift_of_slice layout hsub]
  exact (@hexec (layout.shift prog k) _).mono (fun ⟨s', pc'⟩ hp => hcont s' pc' hp)

theorem step1_subprog {sub : List D}
    (k : Nat) {s : MD} {pc : Int64} {pre : Prop} {Q post : @Post (Kraken.MachineState MD)}
    (hexec : ∀ [layout' : Kraken.Layout D] [Labels],
      (layout' sub).ExecSpec s (pre := pre)
        (post := fun st => st.pc = (layout' sub).addrOf sub.length ∧ Q st))
    (hpre : pre := by trivial)
    (hsub : (prog.drop k).take sub.length = sub := by rfl)
    (hpc : pc = (layout prog).addrOf k)
    (hcont : ∀ s', Q ⟨s', (layout prog).addrOf (k + sub.length)⟩ →
      Eventually (step1 (layout prog)) post ⟨s', (layout prog).addrOf (k + sub.length)⟩) :
    Eventually (step1 (layout prog)) post ⟨s, pc⟩ := by
  refine step1_cps_subprog k hsub hpc (fun [layout' : Kraken.Layout D] [Labels] => hexec hpre) ?_
  rintro s' _ ⟨rfl, hQ⟩
  rw [Kraken.Layout.addrOf_shift_of_slice layout hsub (Nat.le_refl _)] at hQ ⊢
  exact hcont s' hQ

end
