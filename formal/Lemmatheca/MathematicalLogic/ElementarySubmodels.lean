import Mathlib.ModelTheory.Skolem
import Mathlib.ModelTheory.Complexity

/-! Elementary submodels, selected witnesses, and a finite-stage witness hull. -/

namespace Lemmatheca.MathematicalLogic.ElementarySubmodels

open FirstOrder FirstOrder.Language Cardinal

universe u v w

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- An elementary substructure contains a witness for every existential request
with a finite tuple of parameters in that substructure. -/
theorem elementary_witnesses (S : L.Substructure M) (hS : S.IsElementary)
    (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (a : Fin n → S) (b : M)
    (hb : φ.Realize default (Fin.snoc (Subtype.val ∘ a) b)) :
    ∃ c : S, φ.Realize default (Fin.snoc (Subtype.val ∘ a) (c : M)) := by
  let f : S ↪ₑ[L] M := (⟨S, hS⟩ : L.ElementarySubstructure M).subtype
  have hf : (f : S → M) = Subtype.val := rfl
  have hempty : Subtype.val ∘ (default : Empty → S) = (default : Empty → M) :=
    Subsingleton.elim _ _
  have hφ : φ.ex.Realize default (Subtype.val ∘ a) :=
    BoundedFormula.realize_ex.mpr ⟨b, hb⟩
  have hφS : φ.ex.Realize default a := by
    apply (f.map_boundedFormula φ.ex default a).mp
    simpa only [hempty, hf] using hφ
  obtain ⟨c, hc⟩ := BoundedFormula.realize_ex.mp hφS
  refine ⟨c, ?_⟩
  simpa only [Fin.comp_snoc, hempty, hf] using
    (f.map_boundedFormula φ default (Fin.snoc a c)).mpr hc

/-- The image of an elementary embedding is an elementary substructure. -/
theorem elementary_range {N : Type*} [L.Structure N] (f : M ↪ₑ[L] N) :
    f.toHom.range.IsElementary := by
  let e := f.toEmbedding.equivRange
  intro n φ a
  have hf := f.map_formula φ (e.symm ∘ a)
  have he := e.symm.toElementaryEmbedding.map_formula φ a
  have hcomp : f ∘ e.symm ∘ a = Subtype.val ∘ a := by
    funext i
    have h := e.apply_symm_apply (a i)
    exact congrArg Subtype.val h
  rw [hcomp] at hf
  exact hf.trans he

/-- Choose a witness when one exists, with an explicit fallback otherwise. -/
noncomputable def selectedWitness (m : M) {n : ℕ}
    (φ : L.BoundedFormula Empty (n + 1)) (a : Fin n → M) : M :=
  by
    classical
    exact if h : ∃ b, φ.Realize default (Fin.snoc a b) then Classical.choose h else m

theorem selectedWitness_spec (m : M) {n : ℕ}
    (φ : L.BoundedFormula Empty (n + 1)) (a : Fin n → M)
    (h : ∃ b, φ.Realize default (Fin.snoc a b)) :
    φ.Realize default (Fin.snoc a (selectedWitness m φ a)) := by
  classical
  simpa only [selectedWitness, dite_eq_left h] using Classical.choose_spec h

theorem selectedWitness_fallback (m : M) {n : ℕ}
    (φ : L.BoundedFormula Empty (n + 1)) (a : Fin n → M)
    (h : ¬ ∃ b, φ.Realize default (Fin.snoc a b)) :
    selectedWitness m φ a = m := by
  classical
  simp only [selectedWitness, dite_eq_right h]

/-- One stage of adjoining witnesses to all finite parameter tuples. -/
def witnessStep (m : M) (X : Set M) : Set M :=
  X ∪ {b | ∃ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (a : Fin n → M),
    (∀ i, a i ∈ X) ∧ selectedWitness m φ a = b}

/-- Start with the prescribed parameters and the designated domain element. -/
def witnessStage (m : M) (X : Set M) (n : ℕ) : Set M :=
  Nat.rec (X ∪ {m}) (fun _ Y => witnessStep (L := L) m Y) n

/-- The union of the finite witness stages. -/
def witnessHull (m : M) (X : Set M) : Set M :=
  ⋃ n : ℕ, witnessStage (L := L) m X n

theorem subset_witnessHull (m : M) (X : Set M) : X ⊆ witnessHull (L := L) m X := by
  intro a ha
  exact Set.mem_iUnion.mpr ⟨0, Or.inl ha⟩

theorem witnessHull_nonempty (m : M) (X : Set M) : (witnessHull (L := L) m X).Nonempty := by
  exact ⟨m, Set.mem_iUnion.mpr ⟨0, Or.inr (Set.mem_singleton m)⟩⟩

private theorem witnessStage_mono (m : M) (X : Set M) :
    Monotone (witnessStage (L := L) m X) := by
  apply monotone_nat_of_le_succ
  intro r a ha
  exact Or.inl ha

/-- Every finite tuple from the hull already occurs in one finite stage. -/
theorem witnessHull_tuple_stage (m : M) (X : Set M) {n : ℕ} (a : Fin n → M)
    (ha : ∀ i, a i ∈ witnessHull (L := L) m X) :
    ∃ r, ∀ i, a i ∈ witnessStage (L := L) m X r := by
  classical
  choose r hr using fun i => Set.mem_iUnion.mp (ha i)
  refine ⟨Finset.univ.sup r, fun i => ?_⟩
  exact witnessStage_mono m X (Finset.le_sup (Finset.mem_univ i)) (hr i)

theorem selectedWitness_mem_hull (m : M) (X : Set M) {n : ℕ}
    (φ : L.BoundedFormula Empty (n + 1)) (a : Fin n → M)
    (ha : ∀ i, a i ∈ witnessHull (L := L) m X) :
    selectedWitness m φ a ∈ witnessHull (L := L) m X := by
  obtain ⟨r, hr⟩ := witnessHull_tuple_stage m X a ha
  exact Set.mem_iUnion.mpr ⟨r + 1, Or.inr ⟨n, φ, a, hr, rfl⟩⟩

/-- A set closed under selected witnesses is closed under interpreted functions,
including constant interpretations at arity zero. -/
theorem selectedWitnesses_fun_closed (m : M) (X : Set M)
    (hX : ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (a : Fin n → M),
      (∀ i, a i ∈ X) → selectedWitness m φ a ∈ X)
    {n : ℕ} (f : L.Functions n) (a : Fin n → M) (ha : ∀ i, a i ∈ X) :
    Structure.funMap f a ∈ X := by
  let φ : L.BoundedFormula Empty (n + 1) :=
    .equal (.var (.inr (Fin.last n)))
      (.func f (fun i => .var (.inr i.castSucc)))
  have hφ (b : M) : φ.Realize default (Fin.snoc a b) ↔ b = Structure.funMap f a := by
    simp [φ, BoundedFormula.Realize, Term.realize]
  have h : ∃ b, φ.Realize default (Fin.snoc a b) :=
    ⟨Structure.funMap f a, (hφ _).mpr rfl⟩
  have hw := (hφ _).mp (selectedWitness_spec m φ a h)
  rw [← hw]
  exact hX n φ a ha

def witnessHullSubstructure (m : M) (X : Set M) : L.Substructure M where
  carrier := witnessHull (L := L) m X
  fun_mem f a ha := selectedWitnesses_fun_closed m (witnessHull (L := L) m X)
    (fun _ φ a ha => selectedWitness_mem_hull m X φ a ha) f a ha

theorem witnessHull_isElementary (m : M) (X : Set M) :
    (witnessHullSubstructure (L := L) m X).IsElementary := by
  apply Substructure.isElementary_of_exists
  intro n φ a b hb
  let w := selectedWitness m φ (Subtype.val ∘ a)
  refine ⟨⟨w, selectedWitness_mem_hull m X φ (Subtype.val ∘ a) (fun i => (a i).2)⟩,
    selectedWitness_spec m φ (Subtype.val ∘ a) ⟨b, hb⟩⟩

section CardinalBounds

variable {L : Language.{u, u}} {M : Type u} [L.Structure M]

/-- A prescribed set is contained in an elementary substructure bounded by the
maximum of its size, the language size, and countable infinity. -/
theorem exists_elementarySubstructure_card_le [Nonempty M] (X : Set M) :
    ∃ S : L.ElementarySubstructure M,
      X ⊆ S ∧ #S ≤ max ℵ₀ (max L.card #X) := by
  let κ := max ℵ₀ (max L.card #X)
  by_cases hM : #M ≤ κ
  · refine ⟨⊤, fun _ _ => Set.mem_univ _, ?_⟩
    have hcard : #(⊤ : L.ElementarySubstructure M) = #M :=
      Cardinal.mk_congr Substructure.topEquiv.toEquiv
    exact hcard ▸ hM
  · have h1 : ℵ₀ ≤ κ := le_max_left _ _
    have h2 : #X ≤ κ := (le_max_right _ _).trans (le_max_right _ _)
    have h3 : L.card ≤ κ := (le_max_left _ _).trans (le_max_right _ _)
    have h4 : κ ≤ #M := le_of_lt (lt_of_not_ge hM)
    obtain ⟨S, hXS, hS⟩ := L.exists_elementarySubstructure_card_eq X κ h1
      (by simpa only [Cardinal.lift_id] using h2)
      (by simpa only [Cardinal.lift_id] using h3)
      (by simpa only [Cardinal.lift_id] using h4)
    refine ⟨S, hXS, ?_⟩
    simpa only [Cardinal.lift_id] using le_of_eq hS

/-- Countable languages preserve countability when adjoining elementary witnesses. -/
theorem exists_countable_elementarySubstructure [Nonempty M] [Countable L.Symbols]
    (X : Set M) (hX : X.Countable) :
    ∃ S : L.ElementarySubstructure M, X ⊆ S ∧ Countable S := by
  obtain ⟨S, hXS, hS⟩ := exists_elementarySubstructure_card_le (L := L) X
  have hL : L.card ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr inferInstance
  have hX' : #X ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr hX.to_subtype
  refine ⟨S, hXS, Cardinal.mk_le_aleph0_iff.mp (hS.trans ?_)⟩
  exact max_le le_rfl (max_le hL hX')

end CardinalBounds

end Lemmatheca.MathematicalLogic.ElementarySubmodels
