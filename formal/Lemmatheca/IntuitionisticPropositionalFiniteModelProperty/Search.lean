import Lemmatheca.IntuitionisticPropositionalFiniteModelProperty.Traces
import Lemmatheca.IntuitionisticPropositionalFiniteModelProperty.Codes

namespace Lemmatheca.ProofTheory.Intuitionistic.FiniteModels

open Lemmatheca.MathematicalLogic.Propositional

/-- The designated-world Boolean check on the exact finite list of hypotheses. -/
def candidate {n : ℕ} (H : List Formula) (A : Formula)
    (r : RelationCode n) (v : ValuationCode n (problemAtoms H.toFinset A)) (i : Fin n) : Bool :=
  admissible r v && !(booleanForcing r v A i) &&
    H.all (fun B => booleanForcing r v B i)

/-- An executable finite enumeration, with no oracle for formula derivability. -/
def refute (H : List Formula) (A : Formula) : Bool :=
  decide (∃ n : Fin (worldBound H.toFinset A + 1),
    ∃ r : RelationCode n.val,
    ∃ v : ValuationCode n.val (problemAtoms H.toFinset A),
    ∃ i : Fin n.val, candidate H A r v i = true)

theorem refute_iff_not_derives (H : List Formula) (A : Formula) :
    refute H A = true ↔ ¬ Derives (H.toFinset : Set Formula) A := by
  classical
  simp only [refute, decide_eq_true_eq]
  constructor
  · rintro ⟨n, r, v, i, hpass⟩ hd
    simp only [candidate, Bool.and_eq_true_iff, and_assoc] at hpass
    obtain ⟨hg, hneg, hH⟩ := hpass
    have hgood : Admissible r v := of_decide_eq_true hg
    have hn : 0 < n.val := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    have hfalse : booleanForcing r v A i = false := by
      cases he : booleanForcing r v A i with
      | false => rfl
      | true => simp [he] at hneg
    let : Preorder (Fin n.val) := codePreorder r v hgood
    let M := codeModel r v hn hgood
    have hΓ : Kripke.ForcesContext M i (H.toFinset : Set Formula) := by
      intro B hB
      exact (booleanForcing_correct r v hn hgood B i).mp
        (List.all_eq_true.mp hH B (List.mem_toFinset.mp hB))
    have hA := Kripke.sound hd M i hΓ
    have ht := (booleanForcing_correct r v hn hgood A i).mpr hA
    exact Bool.noConfusion (hfalse.symm.trans ht)
  · intro hnd
    obtain ⟨W, rW, fW, M, w, hBound, hM⟩ := finite_poset_countermodel H.toFinset A hnd
    let : PartialOrder W := rW
    let : Fintype W := fW
    let n := Fintype.card W
    let b : Fin n ≃ W := (Fintype.equivFin W).symm
    let S := problemAtoms H.toFinset A
    let r := presentRelation b
    let v := presentValuation M b S
    let i := b.symm w
    refine ⟨⟨n, Nat.lt_succ_of_le hBound⟩, r, v, i, ?_⟩
    simp only [candidate, Bool.and_eq_true_iff, and_assoc]
    refine ⟨?_, ?_, ?_⟩
    · simpa [admissible] using presentation_admissible M b S
    · have hf : booleanForcing r v A i = false :=
        Bool.eq_false_of_not_eq_true (fun hv => hM.2 (by
          have hh := (presentation_forcing M b S A (problem_support H.toFinset A).1 i).mp hv
          simpa [i] using hh))
      simp [hf]
    · apply List.all_eq_true.mpr
      intro B hB
      have hB' : B ∈ H.toFinset := List.mem_toFinset.mpr hB
      apply (presentation_forcing M b S B ((problem_support H.toFinset A).2 B hB') i).mpr
      simpa [i] using hM.1 B hB'

theorem refute_false_iff_derives (H : List Formula) (A : Formula) :
    refute H A = false ↔ Derives (H.toFinset : Set Formula) A := by
  classical
  exact Bool.eq_false_iff.trans
    ((not_congr (refute_iff_not_derives H A)).trans Classical.not_not)

end Lemmatheca.ProofTheory.Intuitionistic.FiniteModels
