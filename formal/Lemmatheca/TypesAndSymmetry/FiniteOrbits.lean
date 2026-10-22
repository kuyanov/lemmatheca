import Lemmatheca.TypesAndSymmetry.Orbits

/-! Finite-fragment exclusion yields original-parameter definitions for finite orbits. -/
namespace Lemmatheca.ModelTheory.TypesAndSymmetry

open FirstOrder FirstOrder.Language Types

universe u v w
variable {L : Language.{u,v}} {M : Type w} [L.Structure M] [Nonempty M]

theorem finite_exclusion (hM : Saturation.OmegaSaturated L M)
    (A : Set M) (hA : A.Finite)
    (p : (L[[A]].completeTheory M).CompleteType (Fin 1)) (S : Set M) (hS : S.Finite)
    (h : ∀ Δ : Finset (L[[A]].Formula (Fin 1)), (↑Δ : Set _) ⊆ formulas p →
      ∃ b : M, b ∉ S ∧ Realizes (↑Δ : Set (L[[A]].Formula (Fin 1))) (fun _ : Fin 1 => b)) :
    ∃ b : M, b ∉ S ∧ Realizes (formulas p) (fun _ : Fin 1 => b) := by
  classical
  let B : Set M := A ∪ S
  have hB : B.Finite := hA.union hS
  let inc : A → B := Set.inclusion (Set.subset_union_left : A ⊆ B)
  let k := L.lhomWithConstantsMap inc
  let neq (s : S) : L[[B]].Formula (Fin 1) :=
    ((Term.var 0).equal (L.con (⟨s.val, Or.inr s.property⟩ : B)).term).not
  let q : Set (L[[B]].Formula (Fin 1)) := k.onFormula '' formulas p ∪ Set.range neq
  have hq : IsPartial (L[[B]].completeTheory M) q := by
    apply (partial_iff_finitelyRealized_completeTheory _).mpr
    intro Γ hΓ
    let Γ₀ := Γ.filter (fun ψ => ψ ∈ k.onFormula '' formulas p)
    choose pick hpick hpickeq using fun ψ : Γ₀ => (Finset.mem_filter.mp ψ.property).2
    let Δ := Γ₀.attach.image pick
    have hΔ : (↑Δ : Set (L[[A]].Formula (Fin 1))) ⊆ formulas p := by
      rintro φ hφ
      obtain ⟨ψ, _, rfl⟩ := Finset.mem_image.mp hφ
      exact hpick ψ
    obtain ⟨b, hbS, hb⟩ := h Δ hΔ
    refine ⟨fun _ => b, fun ψ hψ => ?_⟩
    rcases hΓ hψ with hψimage | ⟨c, rfl⟩
    · let ψ₀ : Γ₀ := ⟨ψ, Finset.mem_filter.mpr ⟨hψ, hψimage⟩⟩
      have hφ := hb (pick ψ₀) (Finset.mem_image.mpr ⟨ψ₀, Finset.mem_attach _ _, rfl⟩)
      have hr := (LHom.realize_onFormula k (pick ψ₀)).mpr hφ
      rwa [hpickeq ψ₀] at hr
    · apply Formula.realize_not.mpr
      rw [Formula.realize_equal]
      change ¬ b = c.val
      intro heq
      exact hbS (heq ▸ c.property)
  obtain ⟨a, ha⟩ := (Saturation.omega_iff_partial.mp hM) B hB q hq
  refine ⟨a 0, ?_, ?_⟩
  · intro hS
    have hn := ha (neq ⟨a 0, hS⟩) (Or.inr (Set.mem_range_self _))
    apply Formula.realize_not.mp hn
    exact Formula.realize_equal.mpr rfl
  · intro φ hφ
    have hr := (LHom.realize_onFormula k φ).mp (ha _ (Or.inl ⟨φ, hφ, rfl⟩))
    have heq : (fun _ : Fin 1 => a 0) = a := by
      funext i; congr; exact Subsingleton.elim _ _
    exact heq.symm ▸ hr

theorem finite_orbit_formula [Countable M] (hM : Saturation.OmegaSaturated L M)
    (A : Set M) (hA : A.Finite) (a : M) (h : (pointOrbit (L := L) A a).Finite) :
    ∃ δ : L[[A]].Formula (Fin 1),
      ∀ b : M, δ.Realize (fun _ => b) ↔ b ∈ pointOrbit (L := L) A a := by
  classical
  let p := (L[[A]].completeTheory M).typeOf (fun _ : Fin 1 => a)
  have hex : ∃ Δ : Finset (L[[A]].Formula (Fin 1)), (↑Δ : Set _) ⊆ formulas p ∧
      ∀ b : M, Realizes (↑Δ : Set (L[[A]].Formula (Fin 1))) (fun _ => b) →
        b ∈ pointOrbit (L := L) A a := by
    by_contra hn
    have hf : ∀ Δ : Finset (L[[A]].Formula (Fin 1)), (↑Δ : Set _) ⊆ formulas p →
        ∃ b : M, b ∉ pointOrbit (L := L) A a ∧
          Realizes (↑Δ : Set (L[[A]].Formula (Fin 1))) (fun _ => b) := by
      intro Δ hΔ
      by_contra hh
      push Not at hh
      apply hn
      refine ⟨Δ, hΔ, fun b hb => ?_⟩
      by_contra hnot
      exact hh b hnot hb
    obtain ⟨b, hb, hbp⟩ := finite_exclusion hM A hA p _ h hf
    exact hb ((type_iff_point_orbit hM A hA a b).mp ((realizes_complete_iff p _).mp hbp))
  obtain ⟨Δ, hΔ, hbound⟩ := hex
  refine ⟨Formula.iInf (fun φ : Δ => φ.val), fun b => ?_⟩
  rw [Formula.realize_iInf]
  constructor
  · intro hb
    exact hbound b (fun φ hφ => hb ⟨φ, hφ⟩)
  · intro hb φ
    have heq := (type_iff_point_orbit hM A hA a b).mpr hb
    have hm : φ.val ∈ formulas ((L[[A]].completeTheory M).typeOf (fun _ : Fin 1 => b)) :=
      heq ▸ hΔ φ.property
    exact Theory.CompleteType.formula_mem_typeOf.mp hm

theorem finite_orbit_definable [Countable M] (hM : Saturation.OmegaSaturated L M)
    (A : Set M) (hA : A.Finite) (a : M) (h : (pointOrbit (L := L) A a).Finite) :
    A.Definable₁ L (pointOrbit (L := L) A a) := by
  obtain ⟨δ, hδ⟩ := finite_orbit_formula hM A hA a h
  refine ⟨δ, ?_⟩
  ext x
  have heq : (fun _ : Fin 1 => x 0) = x := by
    funext i; congr; exact Subsingleton.elim _ _
  exact (hδ (x 0)).symm.trans (Iff.of_eq (congrArg δ.Realize heq))

theorem dcl_iff_singleton_orbit [Countable M] (hM : Saturation.OmegaSaturated L M)
    (A : Set M) (hA : A.Finite) (a : M) :
    a ∈ Closures.dcl L A ↔ pointOrbit (L := L) A a = {a} := by
  constructor
  · intro ha
    apply Set.Subset.antisymm
    · rintro b ⟨g, rfl⟩
      exact Set.mem_singleton_iff.mpr (Closures.automorphism_fixes_dcl g.val g.property a ha)
    · exact Set.singleton_subset_iff.mpr (point_mem_own_orbit A a)
  · intro h
    change A.Definable₁ L {a}
    rw [← h]
    exact finite_orbit_definable hM A hA a (h ▸ Set.finite_singleton a)

theorem acl_iff_finite_orbit [Countable M] (hM : Saturation.OmegaSaturated L M)
    (A : Set M) (hA : A.Finite) (a : M) :
    a ∈ Closures.acl L A ↔ (pointOrbit (L := L) A a).Finite := by
  constructor
  · rintro ⟨D, hD, hfinite, ha⟩
    apply hfinite.subset
    rintro b ⟨g, rfl⟩
    have h := Definability.definable_invariant hD g.val g.property (fun _ : Fin 1 => a)
    exact h.mp ha
  · intro h
    exact ⟨pointOrbit (L := L) A a, finite_orbit_definable hM A hA a h,
      h, point_mem_own_orbit A a⟩

end Lemmatheca.ModelTheory.TypesAndSymmetry
