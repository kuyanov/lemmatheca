import Lemmatheca.IntuitionisticFirstOrderKripkeSemantics.Operations

namespace Lemmatheca.ProofTheory.FirstOrder.Kripke
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w d a
variable {L : Language.{u,v}} {W : Type w} [Preorder W]
variable (K : Model.{u,v,w,d} L W) {α : Type a} {e : Bool}

private theorem transport_complete {w z : W} (h : w ≤ z) (s : α → K.Domain w) :
    K.transport h (Sum.elim s Fin.elim0) = Sum.elim (K.transport h s) Fin.elim0 := by
  funext x
  cases x with
  | inl x => rfl
  | inr i => exact Fin.elim0 i

private theorem holds_impl (A B : Formula L α) (w : W) (s : α → K.Domain w) :
    Holds K w (.impl A B) s ↔ ∀ z (h : w ≤ z),
      Holds K z A (K.transport h s) → Holds K z B (K.transport h s) := by
  unfold Holds
  simp only [Forces, transport_complete]

private theorem holds_neg (A : Formula L α) (w : W) (s : α → K.Domain w) :
    Holds K w (.neg A) s ↔ ∀ z (h : w ≤ z), ¬ Holds K z A (K.transport h s) := by
  unfold Holds
  simp only [Forces, transport_complete]

theorem derivation_sound {Γ : NaturalDeduction.Context L α} {A : Formula L α}
    (p : NaturalDeduction.Derivation false e L Γ A) (w : W) (s : α → K.Domain w)
    (hΓ : ∀ B ∈ Γ, Holds K w B s) : Holds K w A s := by
  classical
  induction p generalizing w with
  | assumption hA => exact hΓ _ hA
  | conjIntro _ _ ihA ihB => exact ⟨ihA w s hΓ, ihB w s hΓ⟩
  | conjElimLeft _ ih => exact (ih w s hΓ).1
  | conjElimRight _ ih => exact (ih w s hΓ).2
  | disjIntroLeft _ ih => exact Or.inl (ih w s hΓ)
  | disjIntroRight _ ih => exact Or.inr (ih w s hΓ)
  | disjElim _ _ _ ihAB ihA ihB =>
      rcases ihAB w s hΓ with hA | hB
      · apply ihA w s
        intro C hC
        rcases Finset.mem_insert.mp hC with rfl | hC
        · exact hA
        · exact hΓ C hC
      · apply ihB w s
        intro C hC
        rcases Finset.mem_insert.mp hC with rfl | hC
        · exact hB
        · exact hΓ C hC
  | impIntro _ ih =>
      apply (holds_impl K _ _ w s).mpr
      intro z hwz hA
      apply ih z (K.transport hwz s)
      intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact hA
      · exact holds_mono K C hwz s (hΓ C hC)
  | impElim _ _ ihAB ihA =>
      have hp := (holds_impl K _ _ w s).mp (ihAB w s hΓ) w le_rfl
      rw [transport_refl] at hp
      exact hp (ihA w s hΓ)
  | negIntro _ ih =>
      apply (holds_neg K _ w s).mpr
      intro z hwz hA
      apply ih z (K.transport hwz s)
      intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact hA
      · exact holds_mono K C hwz s (hΓ C hC)
  | negElim _ _ ihA ihN =>
      have hp := (holds_neg K _ w s).mp (ihN w s hΓ) w le_rfl
      rw [transport_refl] at hp
      exact hp (ihA w s hΓ)
  | falsumElim _ ih => exact (ih w s hΓ).elim
  | classicalContradiction hc _ _ => cases hc
  | allElim t _ ih =>
      apply (holds_instantiate K _ t w s).mpr
      have hp := (holds_all K _ w s).mp (ih w s hΓ) w le_rfl (K.termValue w s t)
      simpa only [transport_refl] using hp
  | exIntro t _ ih =>
      apply (holds_ex K _ w s).mpr
      exact ⟨K.termValue w s t, (holds_instantiate K _ t w s).mp (ih w s hΓ)⟩
  | @allIntro α Γ B _ ih =>
      apply (holds_all K B w s).mpr
      intro z hwz x
      apply (holds_open K B z (K.transport hwz s) x).mp
      apply ih z (Sum.elim (K.transport hwz s) (fun _ => x))
      intro C hC
      rcases Finset.mem_image.mp hC with ⟨D,hD,rfl⟩
      exact (holds_rename K D Sum.inl z _).mpr (holds_mono K D hwz s (hΓ D hD))
  | @exElim α Γ C B _ _ ihEx ihB =>
      rcases (holds_ex K B w s).mp (ihEx w s hΓ) with ⟨x,hx⟩
      have hp := ihB w (Sum.elim s (fun _ => x)) (by
        intro D hD
        rcases Finset.mem_insert.mp hD with rfl | hD
        · exact (holds_open K B w s x).mpr hx
        · rcases Finset.mem_image.mp hD with ⟨E,hE,rfl⟩
          exact (holds_rename K E Sum.inl w _).mpr (hΓ E hE))
      exact (holds_rename K C Sum.inl w (Sum.elim s (fun _ => x))).mp hp
  | equalIntro t _ => exact (holds_termEqual K t t w s).mpr rfl
  | equalElim B t₁ t₂ _ _ _ ihEq ihB =>
      have he := (holds_termEqual K t₁ t₂ w s).mp (ihEq w s hΓ)
      have hp := (holds_instantiate K B t₁ w s).mp (ihB w s hΓ)
      apply (holds_instantiate K B t₂ w s).mpr
      simpa only [he] using hp

theorem proof_sound {Γ : NaturalDeduction.Context L α} {A : Formula L α}
    (p : NaturalDeduction.Proof false e L Γ A) (w : W) (s : α → K.Domain w)
    (hΓ : ∀ B ∈ Γ, Holds K w B s) : Holds K w A s := by
  classical
  let x : K.Domain w := Classical.choice (K.domain_nonempty w)
  have hp := derivation_sound K p w (Sum.elim s (fun _ => x)) (by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨B,hB,rfl⟩
    exact (holds_rename K B Sum.inl w _).mpr (hΓ B hB))
  exact (holds_rename K A Sum.inl w (Sum.elim s (fun _ => x))).mp hp

theorem theoryProof_sound {T : Set (Formula L α)} {A : Formula L α}
    (p : NaturalDeduction.TheoryProof false e L T A) (w : W) (s : α → K.Domain w)
    (hT : ForcesContext K w T s) : Holds K w A s := by
  exact proof_sound K p.derivation w s (fun B hB => hT B (p.allowed B hB))

theorem theory_entails {T : Set (Formula L α)} {A : Formula L α}
    (h : NaturalDeduction.TheoryDerives false e L T A) : Entails.{u,v,w,d} T A := by
  intro X _ M x s hT
  rcases h with ⟨p⟩
  exact theoryProof_sound M p x s hT

theorem countermodel_not_derivable {T : Set (Formula L α)} {A : Formula L α}
    (w : W) (s : α → K.Domain w) (h : Countermodel K w T A s) :
    ¬ NaturalDeduction.TheoryDerives false e L T A := by
  rintro ⟨p⟩
  exact h.2 (theoryProof_sound K p w s h.1)

end Lemmatheca.ProofTheory.FirstOrder.Kripke
