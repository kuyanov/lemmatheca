import Lemmatheca.MathematicalLogic.SecondOrderLogic
import Lemmatheca.MathematicalLogic.ArithmeticTheories
import Mathlib.Tactic

/-! Full second-order Peano arithmetic in the shared second-order syntax. -/
namespace Lemmatheca.MathematicalLogic.SecondOrderArithmetic
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.ArithmeticTheories
noncomputable section
universe u v w

/-- Satisfaction of all displayed sentences, independently of assignments. -/
def FullModels {L : Language.{u,v}} (M : Type w) [L.Structure M]
    (T : Set (SecondOrderLogic.Formula L)) : Prop :=
  ∀ φ ∈ T, ∀ a : ℕ → M, ∀ r : SecondOrderLogic.RelationAssignment M, SecondOrderLogic.fullRealize a r φ

def peanoTheory : Set (SecondOrderLogic.Formula language) :=
  SecondOrderLogic.ofSentence '' Q ∪ {SecondOrderLogic.inductionSentence FunctionSymbol.zero FunctionSymbol.succ}

theorem peano_finite : peanoTheory.Finite := by
  have hQ : Q.Finite := by simp [Q]
  exact (hQ.image _).union (Set.finite_singleton _)


theorem peano_sentences : ∀ φ ∈ peanoTheory, SecondOrderLogic.IsSentence φ := by
  intro φ hφ
  rcases hφ with ⟨ψ, _, rfl⟩ | hφ
  · exact SecondOrderLogic.ofSentence_isSentence ψ
  · obtain rfl := Set.mem_singleton_iff.mp hφ
    exact SecondOrderLogic.inductionSentence_isSentence _ _


variable (M : Type u) [language.Structure M]

private theorem subset_induction_iff : FullSubsetInduction M ↔
    ∀ P : M → Prop, P (zeroValue M) →
      (∀ x, P x → P (succValue M x)) → ∀ x, P x := by
  constructor
  · intro h P hz hs x
    have heq := h {x | P x} hz hs
    exact (Set.ext_iff.mp heq x).mpr (Set.mem_univ x)
  · intro h A hz hs
    ext x
    exact iff_true_intro (h A hz hs x)

theorem models_peano_iff : FullModels M peanoTheory ↔
    (M ⊨ Q) ∧ FullSubsetInduction M := by
  constructor
  · intro h
    constructor
    · constructor
      intro φ hφ
      exact (SecondOrderLogic.fullRealize_ofSentence _ _ φ).mp
        (h _ (Or.inl ⟨φ, hφ, rfl⟩) (fun _ => zeroValue M) (fun _ _ _ => False))
    · apply (subset_induction_iff M).mpr
      exact (SecondOrderLogic.fullRealize_inductionSentence _ _ _ _).mp
        (h _ (Or.inr rfl) (fun _ => zeroValue M) (fun _ _ _ => False))
  · rintro ⟨hQ, hi⟩ φ (⟨ψ, hψ, rfl⟩ | hφ) a r
    · exact (SecondOrderLogic.fullRealize_ofSentence a r ψ).mpr (hQ.realize_of_mem ψ hψ)
    · obtain rfl := Set.mem_singleton_iff.mp hφ
      exact (SecondOrderLogic.fullRealize_inductionSentence _ _ a r).mpr
        ((subset_induction_iff M).mp hi)


theorem full_induction_predecessor (h : FullSubsetInduction M) :
    ∀ x : M, x = zeroValue M ∨ ∃ y : M, succValue M y = x := by
  apply (subset_induction_iff M).mp h
  · exact Or.inl rfl
  · intro x _
    exact Or.inr ⟨x, rfl⟩


theorem nat_models_peano : FullModels ℕ peanoTheory := by
  apply (models_peano_iff ℕ).mpr
  refine ⟨nat_models_Q, (subset_induction_iff ℕ).mpr ?_⟩
  intro P hz hs n
  exact Nat.rec hz hs n


theorem canonical_map_unique (f : ℕ → M) (hz : f 0 = zeroValue M)
    (hs : ∀ n, f (n+1) = succValue M (f n)) : f = numeralValue M := by
  funext n
  induction n with
  | zero => exact hz.trans (numeral_value_zero M).symm
  | succ n ih => rw [hs, ih, numeral_value_succ]


theorem canonical_surjective (h : FullModels M peanoTheory) :
    Function.Surjective (numeralValue M) := by
  exact Set.range_eq_univ.mp (full_induction_standard_copy M ((models_peano_iff M).mp h).2)


theorem recursive_operations_unique (h : FullModels M peanoTheory)
    (a p : M → M → M)
    (a0 : ∀ x, a x (zeroValue M) = x)
    (as : ∀ x y, a x (succValue M y) = succValue M (a x y))
    (p0 : ∀ x, p x (zeroValue M) = zeroValue M)
    (ps : ∀ x y, p x (succValue M y) = a (p x y) x) :
    a = addValue M ∧ p = mulValue M := by
  let : M ⊨ Q := ((models_peano_iff M).mp h).1
  have ha (m n : ℕ) : a (numeralValue M m) (numeralValue M n) = numeralValue M (m+n) := by
    induction n with
    | zero => rw [numeral_value_zero, a0, Nat.add_zero]
    | succ n ih => rw [numeral_value_succ, as, ih, Nat.add_succ, numeral_value_succ]
  have ae : a = addValue M := by
    funext x y
    obtain ⟨m, rfl⟩ := canonical_surjective M h x
    obtain ⟨n, rfl⟩ := canonical_surjective M h y
    exact (ha m n).trans (numeral_add M m n).symm
  refine ⟨ae, ?_⟩
  have hp (m n : ℕ) : p (numeralValue M m) (numeralValue M n) = numeralValue M (m*n) := by
    induction n with
    | zero => rw [numeral_value_zero, p0, Nat.mul_zero, numeral_value_zero]
    | succ n ih => rw [numeral_value_succ, ps, ih, ha, Nat.mul_succ]
  funext x y
  obtain ⟨m, rfl⟩ := canonical_surjective M h x
  obtain ⟨n, rfl⟩ := canonical_surjective M h y
  exact (hp m n).trans (numeral_mul M m n).symm


theorem canonical_isomorphism (h : FullModels M peanoTheory) :
    ∃ e : ℕ ≃[language] M, ∀ n, e n = numeralValue M n := by
  let : M ⊨ Q := ((models_peano_iff M).mp h).1
  obtain ⟨e, he⟩ := standard_embedding M
  have hs : Function.Surjective e := by
    intro x
    obtain ⟨n, hn⟩ := canonical_surjective M h x
    exact ⟨n, (he n).trans hn⟩
  exact ⟨⟨_root_.Equiv.ofBijective e ⟨e.injective, hs⟩, e.map_fun', e.map_rel'⟩, he⟩


theorem canonical_isomorphism_unique (e : ℕ ≃[language] M) :
    ∀ n, e n = numeralValue M n := by
  intro n
  have ht := HomClass.realize_term e (t := numeral n) (v := Empty.elim)
  have hv : e ∘ (Empty.elim : Empty → ℕ) = (Empty.elim : Empty → M) :=
    funext fun x => x.elim
  rw [hv] at ht
  change numeralValue M n = e (numeralValue ℕ n) at ht
  rw [numeral_value_nat] at ht
  exact ht.symm


theorem models_isomorphic (h : FullModels M peanoTheory)
    (N : Type v) [language.Structure N] (hN : FullModels N peanoTheory) :
    Nonempty (M ≃[language] N) := by
  obtain ⟨e, _⟩ := canonical_isomorphism M h
  obtain ⟨f, _⟩ := canonical_isomorphism N hN
  exact ⟨f.comp e.symm⟩


theorem models_firstOrder_PA (h : FullModels M peanoTheory) : M ⊨ PA := by
  obtain ⟨e, _⟩ := canonical_isomorphism M h
  let : ℕ ⊨ PA := nat_models_PA
  exact StrongHomClass.theory_model e


def expandedPeanoTheory : Set (SecondOrderLogic.Formula expandedLanguage) :=
  SecondOrderLogic.ofSentence '' (expansionMap.onTheory Q) ∪
    {SecondOrderLogic.inductionSentence (L := expandedLanguage) (Sum.inl FunctionSymbol.zero) (Sum.inl FunctionSymbol.succ)}

def noncompactTheory : Set (SecondOrderLogic.Formula expandedLanguage) :=
  expandedPeanoTheory ∪ Set.range (fun n => SecondOrderLogic.ofSentence (avoidsNumeral n))

theorem noncompact_sentences : ∀ φ ∈ noncompactTheory, SecondOrderLogic.IsSentence φ := by
  intro φ hφ
  rcases hφ with (⟨ψ, _, rfl⟩ | hφ) | ⟨n, rfl⟩
  · exact SecondOrderLogic.ofSentence_isSentence ψ
  · obtain rfl := Set.mem_singleton_iff.mp hφ
    exact SecondOrderLogic.inductionSentence_isSentence _ _
  · exact SecondOrderLogic.ofSentence_isSentence _


private theorem expanded_induction_iff [expandedLanguage.Structure M]
    [expansionMap.IsExpansionOn M] (a : ℕ → M) (r : SecondOrderLogic.RelationAssignment M) :
    SecondOrderLogic.fullRealize a r
      (SecondOrderLogic.inductionSentence (L := expandedLanguage)
        (Sum.inl FunctionSymbol.zero) (Sum.inl FunctionSymbol.succ)) ↔
      FullSubsetInduction M := by
  refine (SecondOrderLogic.fullRealize_inductionSentence (L := expandedLanguage)
    (Sum.inl FunctionSymbol.zero) (Sum.inl FunctionSymbol.succ) a r).trans ?_
  have hz : Structure.funMap (L := expandedLanguage) (Sum.inl FunctionSymbol.zero) Fin.elim0 =
      zeroValue M := expansionMap.map_onFunction FunctionSymbol.zero _
  have hs (x : M) : Structure.funMap (L := expandedLanguage) (Sum.inl FunctionSymbol.succ)
      (fun _ => x) = succValue M x := expansionMap.map_onFunction FunctionSymbol.succ _
  simp_rw [hz, hs]
  exact (subset_induction_iff M).symm

theorem expanded_models_iff [expandedLanguage.Structure M]
    [expansionMap.IsExpansionOn M] : FullModels M expandedPeanoTheory ↔
      (M ⊨ Q) ∧ FullSubsetInduction M := by
  constructor
  · intro h
    constructor
    · constructor
      intro φ hφ
      apply (expansionMap.realize_onSentence M φ).mp
      apply (SecondOrderLogic.fullRealize_ofSentence _ _ _).mp
      exact h _ (Or.inl ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩)
        (fun _ => zeroValue M) (fun _ _ _ => False)
    · exact (expanded_induction_iff M _ _).mp
        (h _ (Or.inr rfl) (fun _ => zeroValue M) (fun _ _ _ => False))
  · rintro ⟨hQ, hi⟩ φ (⟨ψ, ⟨θ, hθ, rfl⟩, rfl⟩ | hφ) a r
    · apply (SecondOrderLogic.fullRealize_ofSentence a r _).mpr
      exact (expansionMap.realize_onSentence M θ).mpr (hQ.realize_of_mem θ hθ)
    · obtain rfl := Set.mem_singleton_iff.mp hφ
      exact (expanded_induction_iff M a r).mpr hi


theorem noncompact_finite_standard_models (Δ : Finset (SecondOrderLogic.Formula expandedLanguage))
    (hΔ : (↑Δ : Set (SecondOrderLogic.Formula expandedLanguage)) ⊆ noncompactTheory) :
    ∃ I : expandedLanguage.Structure ℕ,
      ∀ φ ∈ Δ, ∀ a : ℕ → ℕ, ∀ r : SecondOrderLogic.RelationAssignment ℕ,
        @SecondOrderLogic.fullRealize expandedLanguage ℕ I a r φ := by
  classical
  let constraints := Set.range (fun n => SecondOrderLogic.ofSentence (avoidsNumeral n))
  let pick (φ : SecondOrderLogic.Formula expandedLanguage) : ℕ :=
    if h : φ ∈ constraints then Classical.choose h else 0
  let b : ℕ := Δ.sup pick + 1
  let : (constantsOn Unit).Structure ℕ := constantsOn.structure (fun _ => b)
  let : expandedLanguage.Structure ℕ := language.withConstantsStructure Unit
  let : expansionMap.IsExpansionOn ℕ := language.withConstants_expansion Unit
  have hp : FullModels ℕ expandedPeanoTheory := (expanded_models_iff ℕ).mpr
    ((models_peano_iff ℕ).mp nat_models_peano)
  refine ⟨inferInstance, ?_⟩
  intro φ hφ a r
  rcases hΔ hφ with hbase | hconstraint
  · exact hp φ hbase a r
  · have he : SecondOrderLogic.ofSentence (avoidsNumeral (pick φ)) = φ := by
      dsimp only [pick]
      rw [dite_eq_left hconstraint]
      exact Classical.choose_spec hconstraint
    rw [← he, SecondOrderLogic.fullRealize_ofSentence, realize_avoidsNumeral]
    change b ≠ numeralValue ℕ (pick φ)
    rw [numeral_value_nat]
    have hle : pick φ ≤ Δ.sup pick := Finset.le_sup hφ
    exact (Nat.lt_succ_of_le hle).ne'


omit [language.Structure M] in
theorem noncompact_no_full_model [expandedLanguage.Structure M] :
    ¬ FullModels M noncompactTheory := by
  let : language.Structure M := expansionMap.reduct M
  intro h
  have hp : FullModels M expandedPeanoTheory := fun φ hφ a r => h φ (Or.inl hφ) a r
  have hP : FullModels M peanoTheory := (models_peano_iff M).mpr
    ((expanded_models_iff M).mp hp)
  let c : M := freshConstant.realize Empty.elim
  obtain ⟨n, hn⟩ := canonical_surjective M hP c
  have hc := h _ (Or.inr ⟨n, rfl⟩) (fun _ => c) (fun _ _ _ => False)
  rw [SecondOrderLogic.fullRealize_ofSentence, realize_avoidsNumeral] at hc
  exact hc hn.symm


theorem full_models_countable (h : FullModels M peanoTheory) : Countable M := by
  exact (canonical_surjective M h).countable


theorem no_uncountable_models [Uncountable M] : ¬ FullModels M peanoTheory := by
  intro h
  let : Countable M := full_models_countable M h
  exact not_countable (α := M) inferInstance


end
end Lemmatheca.MathematicalLogic.SecondOrderArithmetic
