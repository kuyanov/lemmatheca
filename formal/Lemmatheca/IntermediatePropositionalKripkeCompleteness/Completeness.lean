import Lemmatheca.IntermediatePropositionalKripkeCompleteness.Geometry

/-! Semantic consequence ranges over every valuation of every frame in the chosen class. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.IntermediateCanonical

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula Canonical Extensions Kripke

universe v

/-- A frame class is allowed to depend on the actual preorder, as well as its carrier. -/
def EntailsOn (K : (W : Type v) → Preorder W → Prop) (Γ : Set Formula) (A : Formula) : Prop :=
  ∀ (W : Type v) (r : Preorder W), K W r → ∀ (M : @Model ℕ W r) (w : W),
    @ForcesContext ℕ W r M w Γ → @Forces ℕ W r M w A

/-- Pointed satisfiability on some nonempty model in the specified frame class. -/
def SatisfiableOn (K : (W : Type v) → Preorder W → Prop) (Γ : Set Formula) : Prop :=
  ∃ (W : Type v) (r : Preorder W), K W r ∧
    ∃ (M : @Model ℕ W r) (w : W), @ForcesContext ℕ W r M w Γ

theorem kc_strong_completeness (Γ : Set Formula) (A : Formula) :
    SchemaConsequence WeakExcludedMiddle.axioms Γ A ↔
      EntailsOn.{v} (fun W r => @WeakExcludedMiddle.DirectedFutureCones W r) Γ A := by
  classical
  constructor
  · intro hd W r hK M w hΓ
    let : Preorder W := r
    let : Nonempty W := M.world_nonempty
    apply schemaConsequence_sound WeakExcludedMiddle.axioms Γ A _ hd M w hΓ
    intro B hB
    obtain ⟨C, rfl⟩ := hB
    exact WeakExcludedMiddle.frame_wem_iff_directed.mpr hK C
  · intro hs
    by_contra hd
    let P := counterworld WeakExcludedMiddle.axioms Γ A hd
    have hP := specified_countermodel WeakExcludedMiddle.axioms kc_axioms_consistent Γ A hd
    have hf : Forces (liftedModel.{v} WeakExcludedMiddle.axioms kc_axioms_consistent)
        (ULift.up P) A :=
      hs (ULift.{v} (World WeakExcludedMiddle.axioms)) inferInstance kc_lifted_directed
        (liftedModel WeakExcludedMiddle.axioms kc_axioms_consistent) (ULift.up P) (by
          intro B hB
          exact (lifted_forcing WeakExcludedMiddle.axioms kc_axioms_consistent _ B).mpr
            (hP.1 B hB))
    exact hP.2 ((lifted_forcing WeakExcludedMiddle.axioms kc_axioms_consistent _ A).mp hf)

theorem lc_strong_completeness (Γ : Set Formula) (A : Formula) :
    SchemaConsequence Dummett.axioms Γ A ↔
      EntailsOn.{v} (fun W r => @Dummett.LocallyLinear W r) Γ A := by
  classical
  constructor
  · intro hd W r hK M w hΓ
    let : Preorder W := r
    let : Nonempty W := M.world_nonempty
    apply schemaConsequence_sound Dummett.axioms Γ A _ hd M w hΓ
    intro B hB
    obtain ⟨⟨C, D⟩, rfl⟩ := hB
    exact Dummett.frame_linearity_iff_local.mpr hK C D
  · intro hs
    by_contra hd
    let P := counterworld Dummett.axioms Γ A hd
    have hP := specified_countermodel Dummett.axioms lc_axioms_consistent Γ A hd
    have hf : Forces (liftedModel.{v} Dummett.axioms lc_axioms_consistent)
        (ULift.up P) A :=
      hs (ULift.{v} (World Dummett.axioms)) inferInstance lc_lifted_linear
        (liftedModel Dummett.axioms lc_axioms_consistent) (ULift.up P) (by
          intro B hB
          exact (lifted_forcing Dummett.axioms lc_axioms_consistent _ B).mpr (hP.1 B hB))
    exact hP.2 ((lifted_forcing Dummett.axioms lc_axioms_consistent _ A).mp hf)

/-- Specialize this statement with either of the two strong-completeness theorems. -/
theorem consequence_compactness (S : Set Formula)
    (K : (W : Type v) → Preorder W → Prop)
    (hcomplete : ∀ Γ A, SchemaConsequence S Γ A ↔ EntailsOn K Γ A)
    (Γ : Set Formula) (A : Formula) :
    EntailsOn K Γ A ↔ ∃ D : Set Formula, D.Finite ∧ D ⊆ Γ ∧ EntailsOn K D A := by
  constructor
  · intro hs
    obtain ⟨F, hF, hsub, hd⟩ := finite_support.mp
      ((schemaConsequence_iff_union S Γ A).mp ((hcomplete Γ A).mpr hs))
    let D := F ∩ Γ
    refine ⟨D, hF.subset (fun _ hB => hB.1), fun _ hB => hB.2, ?_⟩
    apply (hcomplete D A).mp
    apply (schemaConsequence_iff_union S D A).mpr
    apply hd.weaken
    intro B hB
    rcases hsub hB with hΓ | hS
    · exact Or.inl ⟨hB, hΓ⟩
    · exact Or.inr hS
  · rintro ⟨D, _, hsub, hs⟩ W r hK M w hΓ
    exact hs W r hK M w (fun B hB => hΓ B (hsub hB))

theorem satisfiable_iff_consistent (S : Set Formula)
    (K : (W : Type v) → Preorder W → Prop)
    (hcomplete : ∀ Γ A, SchemaConsequence S Γ A ↔ EntailsOn K Γ A)
    (Γ : Set Formula) : SatisfiableOn K Γ ↔ ¬ SchemaConsequence S Γ falsum := by
  classical
  constructor
  · rintro ⟨W, r, hK, M, w, hΓ⟩ hd
    exact (hcomplete Γ falsum).mp hd W r hK M w hΓ
  · intro hn
    by_contra hsat
    apply hn
    apply (hcomplete Γ falsum).mpr
    intro W r hK M w hΓ
    exact hsat ⟨W, r, hK, M, w, hΓ⟩

theorem satisfiability_compactness (S : Set Formula)
    (K : (W : Type v) → Preorder W → Prop)
    (hcomplete : ∀ Γ A, SchemaConsequence S Γ A ↔ EntailsOn K Γ A)
    (Γ : Set Formula) :
    SatisfiableOn K Γ ↔ ∀ D : Set Formula, D.Finite → D ⊆ Γ → SatisfiableOn K D := by
  constructor
  · rintro ⟨W, r, hK, M, w, hΓ⟩ D _ hsub
    exact ⟨W, r, hK, M, w, fun B hB => hΓ B (hsub hB)⟩
  · intro hs
    apply (satisfiable_iff_consistent S K hcomplete Γ).mpr
    intro hd
    obtain ⟨D, hD, hsub, hDed⟩ :=
      (consequence_compactness S K hcomplete Γ falsum).mp ((hcomplete Γ falsum).mp hd)
    obtain ⟨W, r, hK, M, w, hΓ⟩ := hs D hD hsub
    exact hDed W r hK M w hΓ

theorem kc_rooted_countermodel (Γ : Set Formula) (A : Formula)
    (h : ¬ SchemaConsequence WeakExcludedMiddle.axioms Γ A) :
    let P := counterworld WeakExcludedMiddle.axioms Γ A h
    Countermodel (generated (model WeakExcludedMiddle.axioms kc_axioms_consistent) P)
        ⟨P, le_rfl⟩ Γ A ∧
      (∀ Q : {Q : World WeakExcludedMiddle.axioms // P ≤ Q},
        (⟨P, le_rfl⟩ : {Q : World WeakExcludedMiddle.axioms // P ≤ Q}) ≤ Q) ∧
      (∀ Q R : {Q : World WeakExcludedMiddle.axioms // P ≤ Q},
        ∃ U : {Q : World WeakExcludedMiddle.axioms // P ≤ Q}, Q ≤ U ∧ R ≤ U) := by
  let P := counterworld WeakExcludedMiddle.axioms Γ A h
  refine ⟨generated_countermodel (model WeakExcludedMiddle.axioms kc_axioms_consistent)
    P Γ A (specified_countermodel WeakExcludedMiddle.axioms kc_axioms_consistent Γ A h),
    ?_, ?_⟩
  · intro Q
    exact Q.property
  · intro Q R
    obtain ⟨U, hQU, hRU⟩ := kc_canonical_directed P Q.val R.val Q.property R.property
    exact ⟨⟨U, le_trans Q.property hQU⟩, hQU, hRU⟩

theorem lc_rooted_countermodel (Γ : Set Formula) (A : Formula)
    (h : ¬ SchemaConsequence Dummett.axioms Γ A) :
    let P := counterworld Dummett.axioms Γ A h
    Countermodel (generated (model Dummett.axioms lc_axioms_consistent) P)
        ⟨P, le_rfl⟩ Γ A ∧
      (∀ Q : {Q : World Dummett.axioms // P ≤ Q},
        (⟨P, le_rfl⟩ : {Q : World Dummett.axioms // P ≤ Q}) ≤ Q) ∧
      (∀ Q R : {Q : World Dummett.axioms // P ≤ Q}, Q ≤ R ∨ R ≤ Q) := by
  let P := counterworld Dummett.axioms Γ A h
  refine ⟨generated_countermodel (model Dummett.axioms lc_axioms_consistent)
    P Γ A (specified_countermodel Dummett.axioms lc_axioms_consistent Γ A h), ?_, ?_⟩
  · intro Q
    exact Q.property
  · intro Q R
    exact lc_canonical_linear P Q.val R.val Q.property R.property

end Lemmatheca.ProofTheory.Intuitionistic.IntermediateCanonical
