import Lemmatheca.CountableTypesInUltraproducts.Realization
import Lemmatheca.Ultraproducts.Ultraproducts
import Lemmatheca.SaturatedModels.Saturation
import Mathlib.ModelTheory.Encoding

namespace Lemmatheca.ModelTheory.Ultraproducts.CountableTypes

open FirstOrder FirstOrder.Language Filter Set
universe u v w z z'
variable {L : Language.{u, v}} {I : Type w}
variable (U : Ultrafilter I) (D : I → Type z)
variable [∀ i, L.Structure (D i)] [∀ i, Nonempty (D i)]

/-- One fixed representative of each actual ultraproduct parameter. -/
noncomputable def representatives (A : Set ((U : Filter I).Product D)) (a : A) : ∀ i, D i :=
  Quotient.out a.val

omit [∀ i, Nonempty (D i)] in
theorem representatives_class (A : Set ((U : Filter I).Product D)) (a : A) :
    ((representatives U D A a) : (U : Filter I).Product D) = a.val := by
  exact Quotient.out_eq a.val

/-- Interpret every parameter name at its chosen coordinate representative. -/
@[instance_reducible] noncomputable def namedCoordinateStructure (A : Set ((U : Filter I).Product D)) (i : I) :
    L[[A]].Structure (D i) :=
  Diagrams.namedExpansion (L := L) (fun a : A => representatives U D A a i)

/-- Native expanded ultraproduct structure on the very same quotient carrier. -/
@[instance_reducible] noncomputable def expandedProductStructure (A : Set ((U : Filter I).Product D)) :
    L[[A]].Structure ((U : Filter I).Product D) := by
  let : ∀ i, L[[A]].Structure (D i) := namedCoordinateStructure U D A
  exact FirstOrder.Language.Ultraproduct.structure

omit [∀ i, Nonempty (D i)] in
/-- Symbol-by-symbol equality identifies the expanded product with the canonical named structure. -/
theorem named_product_identity (A : Set ((U : Filter I).Product D)) :
    expandedProductStructure (L := L) U D A =
      (inferInstance : L[[A]].Structure ((U : Filter I).Product D)) := by
  classical
  apply Structure.ext
  · funext n f xs
    let reps : Fin n → ∀ i, D i := fun j => Quotient.out (xs j)
    have hx : (fun j => (reps j : (U : Filter I).Product D)) = xs := by
      funext j
      exact Quotient.out_eq _
    rw [← hx]
    cases f with
    | inl f =>
      calc
        _ = (fun i => Structure.funMap f (fun j => reps j i) : (U : Filter I).Product D) := by
          let : ∀ i, L[[A]].Structure (D i) := namedCoordinateStructure U D A
          exact Ultraproduct.funMap_cast (L := L[[A]]) (Sum.inl f) reps
        _ = _ := (Ultraproduct.funMap_cast f reps).symm
    | inr c =>
      cases n with
      | zero =>
        have hleft :
            @Structure.funMap L[[A]] ((U : Filter I).Product D)
              (expandedProductStructure U D A) 0 (Sum.inr c)
              (fun j => (reps j : (U : Filter I).Product D)) =
                (representatives U D A c : (U : Filter I).Product D) := by
          let : ∀ i, L[[A]].Structure (D i) := namedCoordinateStructure U D A
          exact Ultraproduct.funMap_cast (L := L[[A]]) (Sum.inr c) reps
        exact hleft.trans (representatives_class U D A c)
      | succ n => exact isEmptyElim c
  · funext n R xs
    cases R with
    | inl R => rfl
    | inr R => exact isEmptyElim R

/-- The representation bridge includes actual scoped formulas and their original parameter values. -/
theorem named_los (A : Set ((U : Filter I).Product D)) {α : Type z'} {n : ℕ}
    (φ : L[[A]].BoundedFormula α n) (a : α → ∀ i, D i) (b : Fin n → ∀ i, D i) :
    @BoundedFormula.Realize L[[A]] ((U : Filter I).Product D) inferInstance α n φ
      (fun j => (a j : (U : Filter I).Product D))
      (fun j => (b j : (U : Filter I).Product D)) ↔
      ∀ᶠ i in U, @BoundedFormula.Realize L[[A]] (D i) (namedCoordinateStructure U D A i)
        α n φ (fun j => a j i) (fun j => b j i) := by
  have hid := named_product_identity (L := L) U D A
  rw [← hid]
  let : ∀ i, L[[A]].Structure (D i) := namedCoordinateStructure U D A
  exact FirstOrder.Language.Ultraproduct.boundedFormula_realize_cast φ a b

/-- The parameter version uses native named formulas and the fixed original ultraproduct. -/
theorem countable_parameter_realization {r : ℕ} (hU : CountablyIncomplete U)
    (A : Set ((U : Filter I).Product D)) (p : Set (L[[A]].Formula (Fin r)))
    (hp : p.Countable) (hf : Types.FinitelyRealized ((U : Filter I).Product D) p) :
    ∃ a : Fin r → (U : Filter I).Product D, Types.Realizes p a := by
  have hid := named_product_identity (L := L) U D A
  have hf' := (congrArg (fun S : L[[A]].Structure ((U : Filter I).Product D) =>
    @Types.FinitelyRealized L[[A]] (Fin r) ((U : Filter I).Product D) S p) hid).mpr hf
  let : ∀ i, L[[A]].Structure (D i) := namedCoordinateStructure U D A
  obtain ⟨a, ha⟩ := countable_realization (L := L[[A]]) U D hU p hp hf'
  refine ⟨a, ?_⟩
  exact (congrArg (fun S : L[[A]].Structure ((U : Filter I).Product D) =>
    @Types.Realizes L[[A]] (Fin r) ((U : Filter I).Product D) S p a) hid).mp ha

/-- Complete one-types over every countable parameter set, in the shared syntax. -/
def AlephOneSaturated (L : Language.{u, v}) (N : Type z) [L.Structure N] [Nonempty N] : Prop :=
  ∀ A : Set N, A.Countable →
    ∀ q : (L[[A]].completeTheory N).CompleteType (Fin 1),
      ∃ a : Fin 1 → N, Types.Realizes (Types.formulas q) a

theorem countable_parameter_formulas [Countable L.Symbols]
    {N : Type z} (A : Set N) (hA : A.Countable) (r : ℕ) :
    (Set.univ : Set (L[[A]].Formula (Fin r))).Countable := by
  let : Countable A := hA.to_subtype
  exact Set.to_countable _

theorem countable_parameter_partial_realization [Countable L.Symbols] {r : ℕ}
    (hU : CountablyIncomplete U) (A : Set ((U : Filter I).Product D)) (hA : A.Countable)
    (p : Set (L[[A]].Formula (Fin r)))
    (hp : Types.IsPartial (L[[A]].completeTheory ((U : Filter I).Product D)) p) :
    ∃ a : Fin r → (U : Filter I).Product D, Types.Realizes p a := by
  apply countable_parameter_realization U D hU A p
  · exact (countable_parameter_formulas (L := L) A hA r).mono (Set.subset_univ p)
  · exact (Types.partial_iff_finitelyRealized_completeTheory p).mp hp

theorem aleph_one_saturated [Countable L.Symbols] (hU : CountablyIncomplete U) :
    AlephOneSaturated L ((U : Filter I).Product D) := by
  intro A hA q
  exact countable_parameter_partial_realization U D hU A hA (Types.formulas q)
    (Types.partial_formulas q)

variable {U D}

theorem aleph_one_implies_omega {N : Type z} [L.Structure N] [Nonempty N]
    (hN : AlephOneSaturated L N) : Saturation.OmegaSaturated L N := by
  intro A hA q
  exact hN A hA.countable q

theorem finite_aleph_one {N : Type z} [L.Structure N] [Nonempty N] [Finite N] :
    AlephOneSaturated L N := by
  intro A _ q
  exact Types.finite_realization (Types.formulas q)
    ((Types.partial_iff_finitelyRealized_completeTheory _).mp (Types.partial_formulas q))

/-- The actual condition excluding one specified named point. -/
def exclusionFormula {N : Type z} (A : Set N) (a : A) : L[[A]].Formula (Fin 1) :=
  (BoundedFormula.equal (.var (.inl 0)) (.func (L.con a) Fin.elim0)).not

/-- All original points are excluded, using exactly the whole carrier as parameter set. -/
def allExclusions (L : Language.{u, v}) (N : Type z) :
    Set (L[[(Set.univ : Set N)]].Formula (Fin 1)) :=
  Set.range (exclusionFormula (L := L) (Set.univ : Set N))

private theorem exclusion_realize {N : Type z} [L.Structure N]
    (A : Set N) (a : A) (b : Fin 1 → N) :
    (exclusionFormula (L := L) A a).Realize b ↔ b 0 ≠ a.val := by
  rfl

theorem infinite_exclusions {N : Type z} [L.Structure N] [Nonempty N] [Infinite N] :
    Types.FinitelyRealized N (allExclusions L N) ∧ Types.Omits N (allExclusions L N) := by
  classical
  constructor
  · intro s hs
    have origins (θ : s) : ∃ a : (Set.univ : Set N), exclusionFormula (L := L) _ a = θ.val :=
      hs θ.property
    choose a ha using origins
    let bad : Finset N := Finset.univ.image (fun θ : s => (a θ).val)
    obtain ⟨b, hb⟩ := bad.finite_toSet.exists_notMem
    refine ⟨fun _ => b, fun θ hθ => ?_⟩
    have heq : exclusionFormula (L := L) _ (a ⟨θ, hθ⟩) = θ := ha ⟨θ, hθ⟩
    rw [← heq]
    apply (exclusion_realize _ _ _).mpr
    intro heq
    exact hb (Finset.mem_image.mpr ⟨⟨θ, hθ⟩, Finset.mem_univ _, heq.symm⟩)
  · rintro ⟨a, ha⟩
    have h := ha (exclusionFormula (L := L) _ ⟨a 0, Set.mem_univ _⟩)
      (Set.mem_range_self _)
    exact ((exclusion_realize _ _ _).mp h) rfl

theorem infinite_countable_not_aleph_one {N : Type z} [L.Structure N]
    [Nonempty N] [Countable N] [Infinite N] : ¬AlephOneSaturated L N := by
  intro h
  obtain ⟨hf, ho⟩ := infinite_exclusions (L := L) (N := N)
  have hp := (Types.partial_iff_finitelyRealized_completeTheory (allExclusions L N)).mpr hf
  obtain ⟨q, hpq⟩ := Types.exists_complete_extension (allExclusions L N) hp
  obtain ⟨a, ha⟩ := h Set.univ (Set.to_countable _) q
  exact ho ⟨a, fun φ hφ => ha φ (hpq hφ)⟩


end Lemmatheca.ModelTheory.Ultraproducts.CountableTypes
