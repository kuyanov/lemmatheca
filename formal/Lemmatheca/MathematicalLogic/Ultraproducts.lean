import Mathlib.ModelTheory.Satisfiability
import Mathlib.Order.Filter.Ultrafilter.Basic

/-! Canonical maps and boundary cases for actual first-order ultraproducts.
The quotient, all symbol interpretations, scoped Łoś, and arbitrary-language
compactness are reused directly from mathlib. -/

namespace Lemmatheca.MathematicalLogic.Ultraproducts

open FirstOrder FirstOrder.Language Filter

universe u v w w'

variable {L : Language.{u, v}} {I : Type w}

/-- An ultrafilter on finite subsets containing every finite upward cone. -/
theorem finite_cone_ultrafilter (α : Type w) :
    ∃ U : Ultrafilter (Finset α), ∀ s : Finset α, Set.Ici s ∈ U := by
  classical
  exact ⟨Ultrafilter.of (atTop : Filter (Finset α)),
    fun s => Ultrafilter.of_le _ (Ici_mem_atTop s)⟩

/-- The canonical diagonal elementary embedding into an ultrapower. -/
noncomputable def diagonal {A : Type w'} [L.Structure A] [Nonempty A]
    (U : Ultrafilter I) : A ↪ₑ[L] (U : Filter I).Product (fun _ : I => A) where
  toFun a := ((fun _ : I => a) : (U : Filter I).Product (fun _ : I => A))
  map_formula' := by
    intro n φ x
    change φ.Realize (fun j => ((fun _ : I => x j) :
      (U : Filter I).Product (fun _ : I => A))) ↔ φ.Realize x
    rw [FirstOrder.Language.Ultraproduct.realize_formula_cast]
    exact eventually_const

theorem diagonal_apply {A : Type w'} [L.Structure A] [Nonempty A]
    (U : Ultrafilter I) (a : A) :
    diagonal (L := L) U a =
      ((fun _ : I => a) : (U : Filter I).Product (fun _ : I => A)) := by
  rfl

/-- For a point ultrafilter the actual representative-evaluation map is an
isomorphism, even when the factor domains vary. -/
theorem principal_evaluation_iso (A : I → Type w')
    [∀ i, L.Structure (A i)] [∀ i, Nonempty (A i)] (i₀ : I) :
    ∃ e : ((pure i₀ : Ultrafilter I) : Filter I).Product A ≃[L] A i₀,
      ∀ f : ∀ i, A i,
        e (f : ((pure i₀ : Ultrafilter I) : Filter I).Product A) = f i₀ := by
  classical
  let evaluate : ((pure i₀ : Ultrafilter I) : Filter I).Product A → A i₀ := Quotient.lift (fun f => f i₀) (by
    intro f g hfg
    change (∀ᶠ i in (pure i₀ : Ultrafilter I), f i = g i) at hfg
    simpa only [Ultrafilter.coe_pure, eventually_pure] using hfg)
  have evaluate_mk (f : ∀ i, A i) : evaluate (f : ((pure i₀ : Ultrafilter I) : Filter I).Product A) = f i₀ := rfl
  have hinj : Function.Injective evaluate := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro f g hfg
    change f i₀ = g i₀ at hfg
    apply Quotient.sound
    change ∀ᶠ i in (pure i₀ : Ultrafilter I), f i = g i
    simpa only [Ultrafilter.coe_pure, eventually_pure] using hfg
  have hsurj : Function.Surjective evaluate := by
    intro a
    let defaults : ∀ i, A i := fun i => Classical.choice (inferInstance : Nonempty (A i))
    exact ⟨((Function.update defaults i₀ a) : ((pure i₀ : Ultrafilter I) : Filter I).Product A), by simp [evaluate_mk]⟩
  refine ⟨{ toEquiv := _root_.Equiv.ofBijective evaluate ⟨hinj, hsurj⟩
            map_fun' := ?_
            map_rel' := ?_ }, evaluate_mk⟩
  · intro n F x
    refine Quotient.induction_on_pi x ?_
    intro f
    change evaluate (Structure.funMap F fun j => (f j : ((pure i₀ : Ultrafilter I) : Filter I).Product A)) =
      Structure.funMap F (fun j => evaluate (f j : ((pure i₀ : Ultrafilter I) : Filter I).Product A))
    erw [FirstOrder.Language.Ultraproduct.funMap_cast]
    rfl
  · intro n R x
    refine Quotient.induction_on_pi x ?_
    intro f
    change Structure.RelMap R (fun j => f j i₀) ↔
      Structure.RelMap R (fun j => (f j : ((pure i₀ : Ultrafilter I) : Filter I).Product A))
    erw [FirstOrder.Language.relMap_quotient_mk']
    change Structure.RelMap R (fun j => f j i₀) ↔
      ∀ᶠ i in (pure i₀ : Ultrafilter I), Structure.RelMap R (fun j => f j i)
    simp only [Ultrafilter.coe_pure, eventually_pure]

/-- In a principal ultrapower, this same evaluation isomorphism has the specified
diagonal as its inverse, with both inverse laws exposed. -/
theorem principal_ultrapower_inverse {A : Type w'} [L.Structure A] [Nonempty A]
    (i₀ : I) :
    ∃ e : ((pure i₀ : Ultrafilter I) : Filter I).Product (fun _ : I => A) ≃[L] A,
      (∀ f : I → A,
        e (f : ((pure i₀ : Ultrafilter I) : Filter I).Product (fun _ : I => A)) = f i₀) ∧
      (∀ a : A, e (diagonal (L := L) (pure i₀) a) = a) ∧
      (∀ x, diagonal (L := L) (pure i₀) (e x) = x) := by
  obtain ⟨e, he⟩ := principal_evaluation_iso (L := L) (fun _ : I => A) i₀
  have hd (a : A) : e (diagonal (L := L) (pure i₀) a) = a :=
    he (fun _ => a)
  exact ⟨e, he, hd, fun x => e.injective (hd (e x))⟩

/-- For finite nonempty factors, the specified diagonal itself is an isomorphism. -/
theorem finite_diagonal_iso {A : Type w'} [L.Structure A] [Finite A] [Nonempty A]
    (U : Ultrafilter I) :
    ∃ e : A ≃[L] (U : Filter I).Product (fun _ : I => A),
      (e : A → (U : Filter I).Product (fun _ : I => A)) = diagonal (L := L) U := by
  classical
  let d := diagonal (L := L) (A := A) U
  have hsurj : Function.Surjective d := by
    intro x
    refine Quotient.inductionOn x ?_
    intro f
    have h : ∀ᶠ i in U, ∃ a : A, f i = a :=
      Eventually.of_forall (fun i => ⟨f i, rfl⟩)
    obtain ⟨a, ha⟩ := Ultrafilter.eventually_exists_iff.mp h
    refine ⟨a, Quotient.sound ?_⟩
    exact ha.mono fun _ hi => hi.symm
  exact ⟨{ toEquiv := _root_.Equiv.ofBijective d ⟨d.injective, hsurj⟩
           map_fun' := d.map_fun
           map_rel' := d.map_rel }, rfl⟩

end Lemmatheca.MathematicalLogic.Ultraproducts
