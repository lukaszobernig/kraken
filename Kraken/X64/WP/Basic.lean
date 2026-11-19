module

public import Kraken.X64.OmniSemantics
public import Kraken.X64.WP.Host

/-
# Weakest precondition of a fragment of a host program

`Program.wp p Q E s` is the weakest precondition of the fragment `p` in the ambient, laid out `Host`
program.
-/

/-- Weakest precondition of a `Program` fragment embedded in a host program. -/
@[expose] public def Program.wp [Host] (p : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ k, p.stripLabels.IsInfixAt Host.body k →
    Eventually (step1 Host.exe)
      (fun st => (st.pc = Host.addrOf (k + p.stripLabels.length) ∧ Q st.data) ∨ E st.pc st.data)
      ⟨s, Host.addrOf k⟩

public theorem Program.wp_mono [Host] {p : Program} {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Int64 → MachineData → Prop} (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : Program.wp p Q₁ E₁ s) : Program.wp p Q₂ E₂ s :=
  fun k hk => eventually_trans _ _ _ _ (h k hk) fun _ hb => Eventually.done _ <|
    hb.imp (fun ⟨ha, hq⟩ => ⟨ha, hQ _ hq⟩) (hE _ _)

public theorem Program.wp_append [Host] {p₁ p₂ : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : Program.wp p₁ (fun s' => Program.wp p₂ Q E s') E s) : Program.wp (p₁ ++ p₂) Q E s := by
  intro k hk
  simp only [List.stripLabels, Kraken.Program.stripLabels_append] at hk ⊢
  obtain ⟨h₁, h₂⟩ := List.IsInfixAt.append hk
  refine eventually_trans _ _ _ _ (h k h₁) ?_
  rintro ⟨s', a⟩ (⟨ha, hrun⟩ | hE)
  · dsimp only at ha hrun
    subst ha
    refine eventually_trans _ _ _ _ (hrun (k + p₁.stripLabels.length) h₂) fun _ hb => Eventually.done _ ?_
    rcases hb with ⟨hend, hq⟩ | hE
    · exact Or.inl ⟨by rw [hend, List.length_append, Nat.add_assoc], hq⟩
    · exact Or.inr hE
  · exact Eventually.done _ (Or.inr hE)

public theorem Program.wp_cons [Host] {d : Directive} {p : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : Program.wp [d] (fun s' => Program.wp p Q E s') E s) : Program.wp (d :: p) Q E s :=
  Program.wp_append (p₁ := [d]) (p₂ := p) h

section
variable [Host]

public theorem Host.eventually_of_interp {k : Nat} {d : Directive} {rest : Program}
    (hdp : (d :: rest).IsInfixAt Host.body k) {post : @Post MachineState} {s : MachineData}
    (h : ∀ env : LabelEnv, Host.exe.labels.Consistent env →
      (@Directive.interp env d s ⟨Host.addrOf k, Host.addrOf (k + 1)⟩
        (fun s' => .done ⟨s', Host.addrOf (k + 1)⟩) (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ :=
  _root_.eventually_of_interp Host.fits hdp.cons.1 h

end

/--
Soundness of `Program.wp`: if `p` is a fragment of a `Host` program at body index `k` and
`p.wp Q E s` holds, then `p` eventually reaches `Q` at the fall-through address or `E`.
-/
public theorem Program.step1_of_wp_at [Host] {p : Program}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    {post : @Post MachineState} {k : Nat} (hk : p.stripLabels.IsInfixAt Host.body k) (hwp : p.wp Q E s)
    (hQ : ∀ s', Q s' → post ⟨s', Host.addrOf (k + p.stripLabels.length)⟩) (hE : ∀ a s', E a s' → post ⟨s', a⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (hwp k hk)
  rintro ⟨s', a⟩ (⟨ha, hq⟩ | he)
  · dsimp only at ha
    rw [ha]
    exact hQ s' hq
  · exact hE a s' he

public theorem Program.step1_of_wp [Host] {p : Program}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    {post : @Post MachineState} (h : p.stripLabels.IsInfix Host.body) (hwp : p.wp Q E s)
    (hQ : ∀ s', Q s' → post ⟨s', endAddr h⟩) (hE : ∀ a s', E a s' → post ⟨s', a⟩) :
    Eventually (step1 Host.exe) post ⟨s, startAddr h⟩ :=
  Program.step1_of_wp_at (List.isInfixAt_infixIdx h) hwp hQ hE
