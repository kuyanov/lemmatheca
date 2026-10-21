import Lemmatheca.PaInductionAndHistories.PAClosureSentences
import Lemmatheca.PaInductionAndHistories.PAFormulaDefinability
import Lemmatheca.PaInductionAndHistories.PAChineseRemainder
import Lemmatheca.PaInductionAndHistories.PABetaCoding

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Internal beta totality, extension and bounded witness collection. -/
namespace Lemmatheca.ProofTheory.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
noncomputable section
universe u

/-- Uniform PA totality of the actual bounded beta graph. -/
theorem beta_total_unique : Derives PA (totalUnique betaGraph) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_totalUnique]
  intro x
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  let m : M := succValue M (mulValue M (succValue M (x 2)) (x 1))
  have hm : m ≠ zeroValue M := successor_ne_zero _
  obtain ⟨qr, hqr, huniq⟩ := division_model m hm (x 0)
  have hz (a : M) : (0 : M) ≤ a := zero_le_value a
  have hmone : (1 : M) ≤ m := by
    exact ⟨mulValue M (succValue M (x 2)) (x 1), add_one_value _⟩
  have hqbound : leValue M qr.1 (x 0) := by
    change qr.1 ≤ x 0
    calc
      qr.1 = 1 * qr.1 := (one_mul _).symm
      _ ≤ m * qr.1 := mul_le_mul_of_nonneg_right hmone (hz _)
      _ ≤ m * qr.1 + qr.2 := le_add_of_nonneg_right (hz _)
      _ = x 0 := hqr.1.symm
  have hgraph (y : M) : betaGraph.Realize (extend x y) ↔
      leValue M (succValue M y) m ∧ ∃ q, leValue M q (x 0) ∧
        x 0 = addValue M (mulValue M m q) y := by
    simp only [betaGraph, realize_betaFormula, Term.realize_var, extend,
      Sum.elim_inl, Sum.elim_inr, betaModulusTerm, realize_succTerm, realize_mulTerm]
    rfl
  refine ⟨qr.2, (hgraph _).mpr ⟨hqr.2, qr.1, hqbound, hqr.1⟩, ?_⟩
  intro y hy
  obtain ⟨hr, q, _, he⟩ := (hgraph y).mp hy
  exact congrArg Prod.snd (huniq (q, y) ⟨he, hr⟩)

/-- Internal append: the preserved segment ranges over all model indices below n. -/
theorem beta_extension_model {M : Type u} [language.Structure M] [M ⊨ PA]
    (c d n a : M) :
    ∃ c' d', decodeRealizes betaGraph c' d' n a ∧
      ∀ i, leValue M (succValue M i) n → ∀ z,
        decodeRealizes betaGraph c' d' i z ↔ decodeRealizes betaGraph c d i z := by
  obtain ⟨c', d', hn, hi⟩ := beta_extension_value c d n a
  refine ⟨c', d', ?_, ?_⟩
  · change betaGraph.Realize (extend ![c', d', n] a)
    rw [betaValue_iff]
    exact hn.symm
  · intro i hin z
    change betaGraph.Realize (extend ![c', d', i] z) ↔ betaGraph.Realize (extend ![c, d, i] z)
    rw [betaValue_iff, betaValue_iff, hi i hin]

/-- Bounded witness collection for the actual formula, not an arbitrary predicate. -/
theorem bounded_witness_collection {k : ℕ} {M : Type u} [language.Structure M] [M ⊨ PA]
    (φ : language.Formula ((Fin k ⊕ Unit) ⊕ Unit)) (x : Fin k → M) (n : M)
    (h : ∀ i, leValue M (succValue M i) n → ∃ y,
      φ.Realize (extend (extend x i) y)) :
    ∃ c d, ∀ i, leValue M (succValue M i) n → ∀ y,
      decodeRealizes betaGraph c d i y → φ.Realize (extend (extend x i) y) := by
  let : Nonempty M := ⟨zeroValue M⟩
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  have hs (a : M) : succValue M a = a + 1 := (add_one_value a).symm
  have hbeta := (realize_totalUnique (M := M) betaGraph).mp
    (derives_sound beta_total_unique default
      (fun B hB => Theory.realize_sentence_of_mem PA hB))
  let P (t : M) := leValue M t n → ∃ c d, ∀ i,
    leValue M (succValue M i) t → ∀ y,
      decodeRealizes betaGraph c d i y → φ.Realize (extend (extend x i) y)
  have hP : (Set.univ : Set M).Definable₁ language {t | P t} := by
    change DPred (fun w : Fin 1 → M => leValue M (w 0) n → ∃ c d, ∀ i,
      leValue M (succValue M i) (w 0) → ∀ y,
        decodeRealizes betaGraph c d i y → φ.Realize (extend (extend x i) y))
    apply dp_imp
    · apply dp_le <;> fun_prop
    · apply dp_exists
      apply dp_exists
      apply dp_forall
      apply dp_imp
      · apply dp_le <;> fun_prop
      · apply dp_forall
        apply dp_imp
        · apply dp_decode <;> fun_prop
        · apply dp_formula φ
          intro j
          cases j with
          | inl j =>
            cases j <;>
              simp only [extend, Sum.elim_inl, Sum.elim_inr, Function.comp_def] <;> fun_prop
          | inr j =>
            simp only [extend, Sum.elim_inr]
            fun_prop
  have hz : P (zeroValue M) := by
    intro _
    refine ⟨zeroValue M, zeroValue M, ?_⟩
    intro i hi
    exact False.elim (successor_ne_zero i
      (le_antisymm hi (zero_le_value (succValue M i))))
  have hstep : ∀ t, P t → P (succValue M t) := by
    intro t ih ht
    obtain ⟨c, d, hcd⟩ := ih (le_trans_value (le_successor_value t) ht)
    obtain ⟨a, ha⟩ := h t ht
    obtain ⟨c', d', hnew, hpres⟩ := beta_extension_model c d t a
    refine ⟨c', d', ?_⟩
    intro i hi y hy
    have hit : i ≤ t := by
      change succValue M i ≤ succValue M t at hi
      simpa only [hs, add_le_add_iff_right] using hi
    rcases lt_or_eq_of_le hit with hlt | heq
    · have hstrict := (successor_le_iff_lt i t).mpr hlt
      exact hcd i hstrict y ((hpres i hstrict y).mp hy)
    · subst i
      have he : y = a := (hbeta ![c', d', t]).unique hy hnew
      simpa only [he] using ha
  exact definable_induction P hP hz hstep n (le_refl n)

end
end Lemmatheca.ProofTheory.PAComputations
