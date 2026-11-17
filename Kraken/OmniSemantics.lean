module

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

/-- Step simulation allowing stutter (`post s`) or a matching step in `R₂`. -/
def SubStep {State : Type} (R₁ R₂ : State → @Post State → Prop) : Prop :=
  ∀ s post, R₁ s post → post s ∨ R₂ s post

theorem SubStep.refl {State : Type} (R : State → @Post State → Prop) : SubStep R R :=
  fun _ _ h => .inr h

theorem SubStep.trans {State : Type} {R₁ R₂ R₃ : State → @Post State → Prop}
    (h₁ : SubStep R₁ R₂) (h₂ : SubStep R₂ R₃) : SubStep R₁ R₃ :=
  fun s post h => (h₁ s post h).elim .inl (h₂ s post)

theorem SubStep.eventually {State : Type} {R₁ R₂ : State → @Post State → Prop}
    (h : SubStep R₁ R₂) {post : @Post State} {s : State}
    (he : Eventually R₁ post s) : Eventually R₂ post s := by
  induction he with
  | done s hp => exact .done s hp
  | step s mid hstep _ ih =>
    rcases h s mid hstep with hs | hstep'
    · exact ih s hs
    · exact .step s mid hstep' ih

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
