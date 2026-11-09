import Lemmatheca.CreativeSetsAndComputableIsomorphism.Escape
import Lemmatheca.ProductiveAndCreativeSets.Completeness
import Lemmatheca.MyhillsIsomorphismTheorem.Isomorphism

/-! The actual halting recodings and finite-matching maps in the creative-set
classification. These are ordinary numerical computations, with no oracle. -/
namespace Lemmatheca.ComputabilityTheory.CreativeIsomorphism

open UniversalComputation ProductiveAndCreativeSets PaddingAndInjectiveReductions RicesTheorem

def zeroToDiagonal (v e : ℕ) : ℕ := constantRunMap v (zeroPair e)

def diagonalToZero (v e : ℕ) : ℕ := constantRunMap v (diagonalPair e)

theorem halting_recodings (v : ℕ) (hv : ConstantRunIndex v) :
    (Primrec (zeroToDiagonal v) ∧ Function.Injective (zeroToDiagonal v) ∧
      ∀ e, e ∈ haltsZero ↔ zeroToDiagonal v e ∈ haltingDiagonal) ∧
    (Primrec (diagonalToZero v) ∧ Function.Injective (diagonalToZero v) ∧
      ∀ e, e ∈ haltingDiagonal ↔ diagonalToZero v e ∈ haltsZero) := by
  constructor
  · refine ⟨(constant_run_map_primitive v).comp zeroPair_contract.1,
      (constantRunMap_injective v).comp zeroPair_contract.2.1, ?_⟩
    intro e
    exact (zeroPair_contract.2.2 e).trans (constant_run_reduction v hv (zeroPair e))
  · refine ⟨(constant_run_map_primitive v).comp diagonalPair_contract.1,
      (constantRunMap_injective v).comp diagonalPair_contract.2.1, ?_⟩
    intro e
    exact (diagonalPair_contract.2.2 e).trans
      (constant_run_zero_membership v hv (diagonalPair e))

/-- The exact reverse injection K -> C, after the K_z -> C upgrade. -/
def reverseInjection (g : ℕ → ℕ) (qn qm v e : ℕ) : ℕ :=
  replacement g qn qm (diagonalToZero v e)

theorem reverse_injection_spec {g : ℕ → ℕ} {C : Set ℕ} {qn qm : ℕ}
    (hg : Computable g) (hred : ReducesZero g C)
    (hn : IsFirstSelector g qn) (hm : IsSecondSelector g qm)
    (v : ℕ) (hv : ConstantRunIndex v) :
    Computable (reverseInjection g qn qm v) ∧
      Function.Injective (reverseInjection g qn qm v) ∧
      ∀ e, e ∈ haltingDiagonal ↔ reverseInjection g qn qm v e ∈ C := by
  have hr := replacement_spec hg hred hn hm
  have hb := (halting_recodings v hv).2
  exact ⟨hr.1.comp hb.1.to_comp, hr.2.1.comp hb.2.1,
    fun e => (hb.2.2 e).trans (hr.2.2 _)⟩

/-- The exact Myhill forward and backward maps, in the C -> K orientation. -/
def permutation (g : ℕ → ℕ) (qn qm v a : ℕ) : ℕ → ℕ :=
  Myhill.forward (enumerableMap v a) (reverseInjection g qn qm v)

def inversePermutation (g : ℕ → ℕ) (qn qm v a : ℕ) : ℕ → ℕ :=
  Myhill.backward (enumerableMap v a) (reverseInjection g qn qm v)

theorem specified_isomorphism {g : ℕ → ℕ} {C : Set ℕ} {qn qm : ℕ}
    (hg : Computable g) (hred : ReducesZero g C)
    (hn : IsFirstSelector g qn) (hm : IsSecondSelector g qm)
    (v : ℕ) (hv : ConstantRunIndex v) (a : ℕ)
    (ha : ∀ x, x ∈ C ↔ x ∈ EffectiveEnumerations.indexSet a) :
    Computable (permutation g qn qm v a) ∧
      Computable (inversePermutation g qn qm v a) ∧
      Function.LeftInverse (inversePermutation g qn qm v a) (permutation g qn qm v a) ∧
      Function.RightInverse (inversePermutation g qn qm v a) (permutation g qn qm v a) ∧
      ∀ x, x ∈ C ↔ permutation g qn qm v a x ∈ haltingDiagonal := by
  have hr := reverse_injection_spec hg hred hn hm v hv
  have hf : ∀ x, x ∈ C ↔ enumerableMap v a x ∈ haltingDiagonal :=
    fun x => (ha x).trans (enumerableMap_membership v hv a x)
  have h := Myhill.labelled_bijection (fun x => x ∈ C) (fun y => y ∈ haltingDiagonal)
    (enumerableMap v a) (reverseInjection g qn qm v)
    (enumerableMap_primitive v a).to_comp hr.1
    (enumerableMap_injective v a) hr.2.1
    (fun x => propext (hf x)) (fun y => propext (hr.2.2 y))
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun x => Iff.of_eq (h.2.2.2.2 x)⟩

theorem creative_iff_oneone_complete {C : Set ℕ} (hC : REPred C) :
    Creative C ↔ ∀ A : Set ℕ, REPred A → A ≤₁ C := by
  constructor
  · intro hc A hA
    obtain ⟨v, hv⟩ := constant_run_index_exists
    have hb := (halting_recodings v hv).2
    have hbeta : haltingDiagonal ≤₁ haltsZero :=
      ⟨diagonalToZero v, hb.1.to_comp, hb.2.1, hb.2.2⟩
    obtain ⟨q, hq, hqred⟩ := creative_complete hc haltingDiagonal_enumerable
    have ha := (halting_recodings v hv).1
    have hzeroMany : haltsZero ≤₀ C :=
      ⟨q ∘ zeroToDiagonal v, hq.comp ha.1.to_comp,
        fun e => (ha.2.2 e).trans (hqred _)⟩
    have hzero : haltsZero ≤₁ C := injective_upgrade C hzeroMany
    exact ((oneone_complete A).mp hA).trans (hbeta.trans hzero)
  · intro hc
    exact complete_implies_creative hC
      (hc haltingDiagonal haltingDiagonal_enumerable).to_many_one

theorem creative_iff_diagonal_oneone {C : Set ℕ} (hC : REPred C) :
    Creative C ↔ haltingDiagonal ≤₁ C := by
  constructor
  · intro hc
    exact (creative_iff_oneone_complete hC).mp hc haltingDiagonal haltingDiagonal_enumerable
  · intro h
    exact complete_implies_creative hC h.to_many_one

theorem creative_isomorphism_equivalence (C : Set ℕ) :
    Creative C ↔ Myhill.ComputablyIsomorphic C haltingDiagonal := by
  constructor
  · intro hc
    apply (Myhill.myhill C haltingDiagonal).mp
    exact ⟨(oneone_complete C).mp hc.1, (creative_iff_diagonal_oneone hc.1).mp hc⟩
  · intro hi
    have hr := (Myhill.myhill C haltingDiagonal).mpr hi
    have hce : REPred C :=
      ComputableReductions.enumerable_preimage hr.1.to_many_one haltingDiagonal_enumerable
    exact (creative_iff_diagonal_oneone hce).mpr hr.2

/-- The explicit composition of two pairs of computable numerical inverses. -/
theorem compose_isomorphisms (C D : Set ℕ) (hC jC hD jD : ℕ → ℕ)
    (hc : Computable hC) (hjc : Computable jC) (hd : Computable hD) (hjd : Computable jD)
    (hleftC : Function.LeftInverse jC hC) (hrightC : Function.RightInverse jC hC)
    (hleftD : Function.LeftInverse jD hD) (hrightD : Function.RightInverse jD hD)
    (hmC : ∀ x, x ∈ C ↔ hC x ∈ haltingDiagonal)
    (hmD : ∀ x, x ∈ D ↔ hD x ∈ haltingDiagonal) :
    Computable (jD ∘ hC) ∧ Computable (jC ∘ hD) ∧
      Function.LeftInverse (jC ∘ hD) (jD ∘ hC) ∧
      Function.RightInverse (jC ∘ hD) (jD ∘ hC) ∧
      ∀ x, x ∈ C ↔ (jD ∘ hC) x ∈ D := by
  refine ⟨hjd.comp hc, hjc.comp hd, ?_, ?_, ?_⟩
  · intro x
    change jC (hD (jD (hC x))) = x
    rw [hrightD (hC x), hleftC x]
  · intro y
    change jD (hC (jC (hD y))) = y
    rw [hrightC (hD y), hleftD y]
  · intro x
    have hm := hmD (jD (hC x))
    rw [hrightD (hC x)] at hm
    exact (hmC x).trans hm.symm

theorem creative_sets_isomorphic {C D : Set ℕ} (hC : Creative C) (hD : Creative D) :
    Myhill.ComputablyIsomorphic C D := by
  obtain ⟨h, ⟨hc, hb⟩, hm⟩ := (creative_isomorphism_equivalence C).mp hC
  obtain ⟨k, ⟨kc, kb⟩, km⟩ := (creative_isomorphism_equivalence D).mp hD
  have hj := Myhill.inverse_search h hc hb
  have kj := Myhill.inverse_search k kc kb
  have hs := compose_isomorphisms C D h (Myhill.inverseSearch h hb.2)
    k (Myhill.inverseSearch k kb.2) hc hj.1 kc kj.1
    hj.2.1 hj.2.2.1 kj.2.1 kj.2.2.1 hm km
  exact ⟨Myhill.inverseSearch k kb.2 ∘ h,
    ⟨hs.1, hs.2.2.1.injective, hs.2.2.2.1.surjective⟩, hs.2.2.2.2⟩

end Lemmatheca.ComputabilityTheory.CreativeIsomorphism
