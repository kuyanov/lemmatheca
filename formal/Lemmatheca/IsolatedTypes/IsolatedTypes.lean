import Lemmatheca.TypesAndRealization.Types

/-! Isolation, complete types, and finite classifications without topological assumptions. -/
namespace Lemmatheca.ModelTheory.IsolatedTypes

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Types

universe u v w

variable {L : Language.{u, v}} {T : L.Theory} {n : ℕ}

/-- Membership makes the isolator consistent; its consequences recover the whole type. -/
def Isolates (T : L.Theory) (p : T.CompleteType (Fin n)) (θ : L.Formula (Fin n)) : Prop :=
  θ ∈ formulas p ∧ ∀ φ ∈ formulas p, T ⊨ᵇ θ.imp φ

/-- Some single shared-language formula determines the complete type. -/
def Isolated (T : L.Theory) (p : T.CompleteType (Fin n)) : Prop :=
  ∃ θ, Isolates T p θ

/-- The sentence asserting that the displayed finite tuple has a solution. -/
noncomputable def existentialSentence (θ : L.Formula (Fin n)) : L.Sentence :=
  (Formula.relabel Sum.inr θ).iExs (Fin n)

/-- The closure binds exactly the displayed free variables, including the empty list. -/
theorem existentialSentence_realize {M : Type w} [L.Structure M]
    (θ : L.Formula (Fin n)) :
    M ⊨ existentialSentence θ ↔ ∃ a : Fin n → M, θ.Realize a := by
  simp only [existentialSentence, Sentence.Realize, Formula.realize_iExs,
    Formula.realize_relabel, Function.comp_def, Sum.elim_inr]

private theorem realization (p : T.CompleteType (Fin n)) :
    ∃ N : Theory.ModelType.{u, v, max u v} T,
      ∃ a : Fin n → N, Realizes (formulas p) a := by
  obtain ⟨N, a, ha⟩ := T.exists_modelType_is_realized_in p
  exact ⟨N, a, (realizes_complete_iff p a).mpr ha.symm⟩

/-- An isolator is exactly a consistent condition contained in just the specified complete type. -/
theorem isolates_iff_unique (p : T.CompleteType (Fin n)) (θ : L.Formula (Fin n)) :
    Isolates T p θ ↔ θ ∈ formulas p ∧
      ∀ q : T.CompleteType (Fin n), θ ∈ formulas q → q = p := by
  constructor
  · rintro ⟨hθ, hall⟩
    refine ⟨hθ, fun q hq => ?_⟩
    obtain ⟨N, a, ha⟩ := realization q
    have hp : Realizes (formulas p) a := by
      intro φ hφ
      exact ((hall φ hφ).realize_formula N) (ha θ hq)
    exact ((realizes_complete_iff q a).mp ha).trans
      ((realizes_complete_iff p a).mp hp).symm
  · rintro ⟨hθ, hu⟩
    refine ⟨hθ, fun φ hφ => Theory.models_formula_iff.mpr ?_⟩
    intro N a
    change θ.Realize a → φ.Realize a
    intro hθa
    have hqa : θ ∈ formulas (T.typeOf a) := Theory.CompleteType.formula_mem_typeOf.mpr hθa
    have heq := hu (T.typeOf a) hqa
    exact Theory.CompleteType.formula_mem_typeOf.mp (heq.symm ▸ hφ)

/-- Different isolators of the same type have equivalent truth conditions modulo the theory. -/
theorem equivalent_isolators (p : T.CompleteType (Fin n))
    (θ η : L.Formula (Fin n)) (hθ : Isolates T p θ) (hη : Isolates T p η) :
    T ⊨ᵇ θ.iff η := by
  apply Theory.models_formula_iff.mpr
  intro N a
  exact Formula.realize_iff.mpr ⟨(hθ.2 η hη.1).realize_formula N,
    (hη.2 θ hθ.1).realize_formula N⟩

/-- In the specified model and at the specified tuple, satisfying the isolator is realizing the type. -/
theorem isolator_realizes {M : Type w} [L.Structure M] [Nonempty M] [M ⊨ T]
    (p : T.CompleteType (Fin n)) (θ : L.Formula (Fin n)) (hθ : Isolates T p θ)
    (a : Fin n → M) : θ.Realize a ↔ Realizes (formulas p) a := by
  exact ⟨fun ha φ hφ => (hθ.2 φ hφ).realize_formula M ha, fun ha => ha θ hθ.1⟩

/-- Every model of a complete satisfiable theory realizes its isolated complete types. -/
theorem isolated_realized {M : Type w} [L.Structure M] [Nonempty M] [M ⊨ T]
    (hT : T.IsComplete) (p : T.CompleteType (Fin n)) (hp : Isolated T p) :
    ∃ a : Fin n → M, Realizes (formulas p) a := by
  obtain ⟨θ, hθ⟩ := hp
  obtain ⟨N, a, ha⟩ := realization p
  have heN : N ⊨ existentialSentence θ := (existentialSentence_realize θ).mpr ⟨a, ha θ hθ.1⟩
  have he : T ⊨ᵇ existentialSentence θ :=
    (hT.realize_sentence_iff _ N).mp heN
  obtain ⟨b, hb⟩ := (existentialSentence_realize θ).mp (he.realize_sentence M)
  exact ⟨b, (isolator_realizes p θ hθ b).mp hb⟩

/-- A formula and its negation distinguish any two different complete types. -/
theorem separates (p q : T.CompleteType (Fin n)) (h : p ≠ q) :
    ∃ φ ∈ formulas p, φ.not ∈ formulas q := by
  classical
  by_contra hn
  have hpq : formulas p ⊆ formulas q := by
    intro φ hφ
    rcases q.mem_or_not_mem (Formula.equivSentence φ) with hq | hq
    · exact hq
    · exact False.elim (hn ⟨φ, hφ, hq⟩)
  apply h
  apply SetLike.ext
  intro γ
  change γ ∈ p.toTheory ↔ γ ∈ q.toTheory
  constructor
  · intro hγ
    have hφ : Formula.equivSentence.symm γ ∈ formulas p := by
      change Formula.equivSentence (Formula.equivSentence.symm γ) ∈ p.toTheory
      simpa only [Equiv.apply_symm_apply] using hγ
    have := hpq hφ
    simpa only [formulas, Set.mem_preimage, Equiv.apply_symm_apply] using this
  · intro hγ
    by_contra hpγ
    have hnot : γ.not ∈ p := (p.not_mem_iff γ).mpr hpγ
    have hφ : Formula.equivSentence.symm γ.not ∈ formulas p := by
      change Formula.equivSentence (Formula.equivSentence.symm γ.not) ∈ p.toTheory
      rw [Equiv.apply_symm_apply]
      exact hnot
    have hnq := hpq hφ
    have hnq' : γ.not ∈ q := by
      change γ.not ∈ q.toTheory
      simpa only [formulas, Set.mem_preimage, Equiv.apply_symm_apply] using hnq
    exact (q.not_mem_iff γ).mp hnq' hγ

/-- A finite conjunction separates a given type from all the other types in a finite space. -/
theorem isolated_of_finite [Finite (T.CompleteType (Fin n))]
    (p : T.CompleteType (Fin n)) : Isolated T p := by
  classical
  let := Fintype.ofFinite (T.CompleteType (Fin n))
  let others := Finset.univ.erase p
  have hd : ∀ q : others, ∃ φ ∈ formulas p, φ.not ∈ formulas q.val := by
    intro q
    exact separates p q.val (Finset.ne_of_mem_erase q.prop).symm
  choose φ hpφ hqφ using hd
  let θ := Formula.iInf φ
  obtain ⟨M, a, ha⟩ := realization p
  have hθa : θ.Realize a := Formula.realize_iInf.mpr fun q => ha _ (hpφ q)
  have hθp : θ ∈ formulas p := by
    have heq := (realizes_complete_iff p a).mp ha
    rw [heq]
    exact Theory.CompleteType.formula_mem_typeOf.mpr hθa
  refine ⟨θ, (isolates_iff_unique p θ).mpr ⟨hθp, fun q hθq => ?_⟩⟩
  by_contra hneq
  have hqo : q ∈ others := Finset.mem_erase.mpr ⟨hneq, Finset.mem_univ _⟩
  let q' : others := ⟨q, hqo⟩
  obtain ⟨N, b, hb⟩ := realization q
  have hφb := (Formula.realize_iInf.mp (hb θ hθq)) q'
  exact (Formula.realize_not.mp (hb _ (hqφ q'))) hφb

/-- Compactness rules out an infinite complete-type space whose every type has an isolator. -/
theorem finite_iff_all_isolated :
    Finite (T.CompleteType (Fin n)) ↔ ∀ p : T.CompleteType (Fin n), Isolated T p := by
  classical
  constructor
  · intro h
    let := h
    exact isolated_of_finite
  · intro hall
    by_contra hfinite
    let : Infinite (T.CompleteType (Fin n)) := not_finite_iff_infinite.mp hfinite
    choose θ hθ using hall
    let r : Set (L.Formula (Fin n)) := Set.range fun p => (θ p).not
    have hr : IsPartial T r := by
      apply (partial_iff_finite T r).mpr
      intro s hs
      let pick (φ : s) : T.CompleteType (Fin n) := Classical.choose (hs φ.prop)
      have hpick (φ : s) : (θ (pick φ)).not = φ := Classical.choose_spec (hs φ.prop)
      let excluded := s.attach.image pick
      obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset excluded
      obtain ⟨N, a, ha⟩ := realization q
      apply (partial_iff_model T (↑s : Set (L.Formula (Fin n)))).mpr
      refine ⟨N, a, fun φ hφ => ?_⟩
      let φ' : s := ⟨φ, hφ⟩
      have hpneq : q ≠ pick φ' := by
        intro heq
        exact hq (heq ▸ Finset.mem_image.mpr ⟨φ', Finset.mem_attach _ _, rfl⟩)
      have hnot : (θ (pick φ')).not ∈ formulas q := by
        have hno : Formula.equivSentence (θ (pick φ')) ∉ q := by
          intro hmem
          exact hpneq (((isolates_iff_unique _ _).mp (hθ (pick φ'))).2 q hmem)
        exact (q.not_mem_iff _).mpr hno
      have hreal := ha _ hnot
      rw [hpick φ'] at hreal
      exact hreal
    obtain ⟨N, a, ha⟩ := (partial_iff_model T r).mp hr
    let q := T.typeOf a
    have hpos : (θ q).Realize a := Theory.CompleteType.formula_mem_typeOf.mp (hθ q).1
    have hneg : (θ q).not.Realize a := ha _ (Set.mem_range_self q)
    exact (Formula.realize_not.mp hneg) hpos

end Lemmatheca.ModelTheory.IsolatedTypes
