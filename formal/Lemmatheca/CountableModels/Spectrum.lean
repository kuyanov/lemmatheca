import Lemmatheca.CountableSaturatedModels.SmallTheories

/-! Countably infinite models modulo actual structure isomorphism. -/
namespace Lemmatheca.ModelTheory.CountableModels

open FirstOrder FirstOrder.Language
open CountableCategoricity CountableSaturatedModels

variable {L : Language.{0, 0}} (T : L.Theory)

/-- An actual nonempty model with countably infinite carrier. -/
structure CountableModel where
  model : T.ModelType.{0, 0, 0}
  [countable_carrier : Countable model]
  [infinite_carrier : Infinite model]

attribute [instance] CountableModel.countable_carrier CountableModel.infinite_carrier

/-- Isomorphism compares the actual underlying language structures. -/
def modelSetoid : Setoid (CountableModel T) where
  r M N := Nonempty (M.model ≃[L] N.model)
  iseqv := ⟨fun M => ⟨Language.Equiv.refl L M.model⟩,
    fun h => h.map Language.Equiv.symm,
    fun h h' => h.map2 (fun e f => f.comp e) h'⟩

abbrev ModelClass := Quotient (modelSetoid T)

def modelClass (M : CountableModel T) : ModelClass T := Quotient.mk _ M

/-- The corpus's I(T,aleph_0), as the cardinal of the native isomorphism quotient. -/
noncomputable def spectrum : Cardinal.{1} := Cardinal.mk (ModelClass T)

variable {T}

theorem modelClass_eq_iff (M N : CountableModel T) :
    modelClass T M = modelClass T N ↔ Nonempty (M.model ≃[L] N.model) := by
  exact Quotient.eq

/-- Exact finite cardinality is equivalent to a complete list with no repeated isomorphism class. -/
theorem spectrum_eq_nat_iff (k : ℕ) : spectrum T = k ↔
    ∃ M : Fin k → CountableModel T,
      (Pairwise fun i j => ¬ Nonempty ((M i).model ≃[L] (M j).model)) ∧
      ∀ N : CountableModel T, ∃ i, Nonempty ((M i).model ≃[L] N.model) := by
  classical
  constructor
  · intro h
    obtain ⟨E⟩ := Cardinal.mk_eq_nat_iff.mp h
    let M : Fin k → CountableModel T := fun i => Quotient.out (E.symm i)
    have hM (i : Fin k) : modelClass T (M i) = E.symm i := Quotient.out_eq _
    refine ⟨M, ?_, fun N => ?_⟩
    · intro i j hij hiso
      have hh := (hM i).symm.trans ((modelClass_eq_iff _ _).mpr hiso |>.trans (hM j))
      exact hij (E.symm.injective hh)
    · refine ⟨E (modelClass T N), (modelClass_eq_iff _ _).mp ?_⟩
      rw [hM, E.symm_apply_apply]
  · rintro ⟨M, hdist, hcover⟩
    let f : Fin k → ModelClass T := fun i => modelClass T (M i)
    have hinj : Function.Injective f := by
      intro i j hij
      by_contra hne
      exact hdist hne ((modelClass_eq_iff _ _).mp hij)
    have hsurj : Function.Surjective f := by
      intro c
      induction c using Quotient.inductionOn with
      | h N =>
        obtain ⟨i, hi⟩ := hcover N
        exact ⟨i, (modelClass_eq_iff _ _).mpr hi⟩
    exact Cardinal.mk_eq_nat_iff.mpr ⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).symm⟩

theorem categorical_iff_spectrum_one [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : T.ModelType.{0, 0, 0}, Infinite N) :
    (Cardinal.aleph0 : Cardinal.{0}).Categorical T ↔ spectrum T = 1 := by
  constructor
  · intro hcat
    obtain ⟨M, hc, hi⟩ := countable_infinite_model hT hInf
    let := hc
    let := hi
    apply (spectrum_eq_nat_iff 1).mpr
    refine ⟨fun _ => ⟨M⟩, ?_, fun N => ?_⟩
    · intro i j hij
      exact (hij (Subsingleton.elim _ _)).elim
    · exact ⟨0, hcat M N.model (Cardinal.mk_eq_aleph0 M) (Cardinal.mk_eq_aleph0 N.model)⟩
  · intro h
    obtain ⟨P, _, hcover⟩ := (spectrum_eq_nat_iff 1).mp h
    intro M N hM hN
    let : Countable M := Cardinal.mk_le_aleph0_iff.mp hM.le
    let : Countable N := Cardinal.mk_le_aleph0_iff.mp hN.le
    let : Infinite M := models_infinite hT hInf
    let : Infinite N := models_infinite hT hInf
    obtain ⟨i, ⟨e⟩⟩ := hcover ⟨M⟩
    obtain ⟨j, ⟨f⟩⟩ := hcover ⟨N⟩
    have hij : i = j := Subsingleton.elim _ _
    subst j
    exact ⟨f.comp e.symm⟩

theorem finite_spectrum_small [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : T.ModelType.{0, 0, 0}, Infinite N) (hfin : Finite (ModelClass T)) :
    CountableSaturatedModels.Small T := by
  classical
  let := hfin
  intro n
  let F : (Σ c : ModelClass T, Fin n → (Quotient.out c).model) → T.CompleteType (Fin n) :=
    fun z => T.typeOf z.2
  have hs : Function.Surjective F := by
    intro p
    obtain ⟨N, hc, a, ha⟩ := countable_realization p
    let := hc
    let : Infinite N := models_infinite hT hInf
    let B : CountableModel T := ⟨N⟩
    let c := modelClass T B
    have hi : Nonempty ((Quotient.out c).model ≃[L] N) :=
      (modelClass_eq_iff _ _).mp (Quotient.out_eq c)
    obtain ⟨e⟩ := hi
    let b : Fin n → (Quotient.out c).model := e.symm ∘ a
    have hb : Types.Realizes (Types.formulas p) b := fun φ hφ =>
      (e.symm.toElementaryEmbedding.map_formula φ a).mpr (ha φ hφ)
    exact ⟨⟨c, b⟩, ((Types.realizes_complete_iff p b).mp hb).symm⟩
  exact hs.countable

end Lemmatheca.ModelTheory.CountableModels
