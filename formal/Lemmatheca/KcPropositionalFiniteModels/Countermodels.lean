import Lemmatheca.IntuitionisticPropositionalFiniteFiltrations.Filtrations
import Lemmatheca.IntermediatePropositionalKripkeCompleteness.Completeness

/-! Finite rooted KC countermodels, with a genuine greatest world. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.KCFiniteModels

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula Kripke Extensions

abbrev Formula := FiniteModels.Formula

universe u

theorem greatest_world_wem {W : Type u} [Preorder W] (M : Model ℕ W)
    (t : W) (ht : ∀ w : W, w ≤ t) (w : W) (A : Formula) :
    Forces M w (WeakExcludedMiddle.wem A) := by
  apply WeakExcludedMiddle.directed_cone_forces_wem M w _ A
  intro u v _ _
  exact ⟨t, ht u, ht v⟩

theorem greatest_world_sound {W : Type u} [Preorder W] (M : Model ℕ W)
    (t : W) (ht : ∀ w : W, w ≤ t) (Γ : Set Formula) (A : Formula)
    (hd : SchemaConsequence WeakExcludedMiddle.axioms Γ A)
    (w : W) (hΓ : ForcesContext M w Γ) : Forces M w A := by
  obtain ⟨E, hE, hd⟩ := hd
  apply Kripke.sound hd M w
  intro B hB
  rcases hB with hB | hB
  · exact hΓ B hB
  · obtain ⟨C, rfl⟩ := hE hB
    exact greatest_world_wem M t ht w C

theorem finite_countermodel (Γ : Finset Formula) (A : Formula)
    (h : ¬ SchemaConsequence WeakExcludedMiddle.axioms (Γ : Set Formula) A) :
    ∃ (W : Type) (r : PartialOrder W) (f : Fintype W)
      (M : @Model ℕ W r.toPreorder) (root top : W),
      @Fintype.card W f ≤ FiniteModels.worldBound Γ A ∧
      (∀ w : W, @LE.le W r.toLE root w) ∧
      (∀ w : W, @LE.le W r.toLE w top) ∧
      @Countermodel ℕ W r.toPreorder M root (Γ : Set Formula) A := by
  let P := IntermediateCanonical.counterworld WeakExcludedMiddle.axioms
    (Γ : Set Formula) A h
  let M := generated
    (IntermediateCanonical.model WeakExcludedMiddle.axioms
      IntermediateCanonical.kc_axioms_consistent) P
  let root : {Q : IntermediateCanonical.World WeakExcludedMiddle.axioms // P ≤ Q} :=
    ⟨P, le_rfl⟩
  have hs := IntermediateCanonical.kc_rooted_countermodel (Γ : Set Formula) A h
  let Δ := FiniteModels.problemSubformulas Γ A
  obtain ⟨top, ht⟩ := Filtrations.trace_greatest M Δ hs.2.2
  refine ⟨Filtrations.TraceWorld M Δ, inferInstance, inferInstance,
    Filtrations.traceModel M Δ, Filtrations.traceWorld M Δ root, top, ?_, ?_, ht, ?_⟩
  · exact (Filtrations.trace_card_bounds M Δ).2
  · exact Filtrations.trace_root M Δ root hs.2.1
  · apply (Filtrations.trace_countermodel M Δ (FiniteModels.problem_closed Γ A)
      (Γ : Set Formula) (FiniteModels.problem_contains Γ A).2 A
      (FiniteModels.problem_contains Γ A).1 root).mpr
    exact hs.1

theorem finite_validity_iff (Γ : Finset Formula) (A : Formula) :
    (∀ (W : Type) (r : PartialOrder W) (_f : Fintype W)
      (M : @Model ℕ W r.toPreorder) (root top : W),
      (∀ w : W, @LE.le W r.toLE root w) →
      (∀ w : W, @LE.le W r.toLE w top) →
      @ForcesContext ℕ W r.toPreorder M root (Γ : Set Formula) →
      @Forces ℕ W r.toPreorder M root A) ↔
    SchemaConsequence WeakExcludedMiddle.axioms (Γ : Set Formula) A := by
  classical
  constructor
  · intro hv
    by_contra hn
    obtain ⟨W, r, f, M, root, top, _, hr, ht, hM⟩ := finite_countermodel Γ A hn
    exact hM.2 (hv W r f M root top hr ht hM.1)
  · intro hd W r f M root top _hr ht hΓ
    exact @greatest_world_sound W r.toPreorder M top ht
      (Γ : Set Formula) A hd root hΓ

theorem bounded_validity_iff (Γ : Finset Formula) (A : Formula) :
    (∀ (W : Type) (r : PartialOrder W) (f : Fintype W)
      (M : @Model ℕ W r.toPreorder) (root top : W),
      @Fintype.card W f ≤ FiniteModels.worldBound Γ A →
      (∀ w : W, @LE.le W r.toLE root w) →
      (∀ w : W, @LE.le W r.toLE w top) →
      @ForcesContext ℕ W r.toPreorder M root (Γ : Set Formula) →
      @Forces ℕ W r.toPreorder M root A) ↔
    SchemaConsequence WeakExcludedMiddle.axioms (Γ : Set Formula) A := by
  classical
  constructor
  · intro hv
    by_contra hn
    obtain ⟨W, r, f, M, root, top, hb, hr, ht, hM⟩ := finite_countermodel Γ A hn
    exact hM.2 (hv W r f M root top hb hr ht hM.1)
  · intro hd W r f M root top _hb _hr ht hΓ
    exact @greatest_world_sound W r.toPreorder M top ht
      (Γ : Set Formula) A hd root hΓ

theorem wem_axioms_infinite :
    Set.Infinite (WeakExcludedMiddle.axioms : Set Formula) := by
  have hi : Function.Injective
      (fun n : ℕ => WeakExcludedMiddle.wem (atom n)) := by
    intro m n h
    simpa only [WeakExcludedMiddle.wem, PropFormula.disj.injEq,
      PropFormula.neg.injEq, PropFormula.atom.injEq, and_self] using h
  apply (Set.infinite_range_of_injective hi).mono
  rintro B ⟨n, rfl⟩
  exact ⟨atom n, rfl⟩

end Lemmatheca.ProofTheory.Intuitionistic.KCFiniteModels
