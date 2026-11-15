import Lemmatheca.KcPropositionalFiniteModels.Countermodels

/-! Native LC finite consequence on actual finite rooted chain models. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.LCFiniteModels

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula Kripke Extensions

abbrev Formula := FiniteModels.Formula

universe u

theorem chain_sound {W : Type u} [Preorder W] (M : Model ℕ W)
    (hc : ∀ u v : W, u ≤ v ∨ v ≤ u) (Γ : Set Formula) (A : Formula)
    (hd : SchemaConsequence Dummett.axioms Γ A)
    (w : W) (hΓ : ForcesContext M w Γ) : Forces M w A := by
  obtain ⟨E, hE, hd⟩ := hd
  apply Kripke.sound hd M w
  intro B hB
  rcases hB with hB | hB
  · exact hΓ B hB
  · obtain ⟨⟨C, D⟩, rfl⟩ := hE hB
    exact Dummett.linear_cone_forces_linearity M w (fun u v _ _ => hc u v) C D

theorem finite_countermodel (Γ : Finset Formula) (A : Formula)
    (h : ¬ SchemaConsequence Dummett.axioms (Γ : Set Formula) A) :
    ∃ (W : Type) (r : PartialOrder W) (f : Fintype W)
      (M : @Model ℕ W r.toPreorder) (root top : W),
      @Fintype.card W f ≤ FiniteModels.worldBound Γ A ∧
      (∀ w : W, @LE.le W r.toLE root w) ∧
      (∀ w : W, @LE.le W r.toLE w top) ∧
      (∀ u v : W, @LE.le W r.toLE u v ∨ @LE.le W r.toLE v u) ∧
      @Countermodel ℕ W r.toPreorder M root (Γ : Set Formula) A := by
  let P := IntermediateCanonical.counterworld Dummett.axioms (Γ : Set Formula) A h
  let M := generated
    (IntermediateCanonical.model Dummett.axioms IntermediateCanonical.lc_axioms_consistent) P
  let root : {Q : IntermediateCanonical.World Dummett.axioms // P ≤ Q} := ⟨P, le_rfl⟩
  have hs := IntermediateCanonical.lc_rooted_countermodel (Γ : Set Formula) A h
  let Δ := FiniteModels.problemSubformulas Γ A
  obtain ⟨top, ht⟩ := Filtrations.trace_greatest M Δ
    (fun u v => (hs.2.2 u v).elim
      (fun huv => ⟨v, huv, le_rfl⟩) (fun hvu => ⟨u, le_rfl, hvu⟩))
  refine ⟨Filtrations.TraceWorld M Δ, inferInstance, inferInstance,
    Filtrations.traceModel M Δ, Filtrations.traceWorld M Δ root, top, ?_, ?_,
    ht, Filtrations.trace_comparable M Δ hs.2.2, ?_⟩
  · exact (Filtrations.trace_card_bounds M Δ).2
  · exact Filtrations.trace_root M Δ root hs.2.1
  · apply (Filtrations.trace_countermodel M Δ (FiniteModels.problem_closed Γ A)
      (Γ : Set Formula) (FiniteModels.problem_contains Γ A).2 A
      (FiniteModels.problem_contains Γ A).1 root).mpr
    exact hs.1

theorem finite_validity_iff (Γ : Finset Formula) (A : Formula) :
    (∀ (W : Type) (r : PartialOrder W) (_f : Fintype W)
      (M : @Model ℕ W r.toPreorder) (root : W),
      (∀ w : W, @LE.le W r.toLE root w) →
      (∀ u v : W, @LE.le W r.toLE u v ∨ @LE.le W r.toLE v u) →
      @ForcesContext ℕ W r.toPreorder M root (Γ : Set Formula) →
      @Forces ℕ W r.toPreorder M root A) ↔
    SchemaConsequence Dummett.axioms (Γ : Set Formula) A := by
  classical
  constructor
  · intro hv
    by_contra hn
    obtain ⟨W, r, f, M, root, _top, _, hr, _ht, hc, hM⟩ := finite_countermodel Γ A hn
    exact hM.2 (hv W r f M root hr hc hM.1)
  · intro hd W r f M root _hr hc hΓ
    exact @chain_sound W r.toPreorder M hc (Γ : Set Formula) A hd root hΓ

theorem bounded_validity_iff (Γ : Finset Formula) (A : Formula) :
    (∀ (W : Type) (r : PartialOrder W) (f : Fintype W)
      (M : @Model ℕ W r.toPreorder) (root : W),
      @Fintype.card W f ≤ FiniteModels.worldBound Γ A →
      (∀ w : W, @LE.le W r.toLE root w) →
      (∀ u v : W, @LE.le W r.toLE u v ∨ @LE.le W r.toLE v u) →
      @ForcesContext ℕ W r.toPreorder M root (Γ : Set Formula) →
      @Forces ℕ W r.toPreorder M root A) ↔
    SchemaConsequence Dummett.axioms (Γ : Set Formula) A := by
  classical
  constructor
  · intro hv
    by_contra hn
    obtain ⟨W, r, f, M, root, _top, hb, hr, _ht, hc, hM⟩ := finite_countermodel Γ A hn
    exact hM.2 (hv W r f M root hb hr hc hM.1)
  · intro hd W r f M root _hb _hr hc hΓ
    exact @chain_sound W r.toPreorder M hc (Γ : Set Formula) A hd root hΓ

theorem generated_comparable {W : Type u} [Preorder W]
    (w : W) (h : Dummett.LocallyLinear W) :
    ∀ u v : {z : W // w ≤ z}, u ≤ v ∨ v ≤ u := by
  intro u v
  exact h w u.val v.val u.property v.property

end Lemmatheca.ProofTheory.Intuitionistic.LCFiniteModels
