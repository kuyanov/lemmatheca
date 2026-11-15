import Lemmatheca.LcPropositionalFiniteModels.Codes
import Lemmatheca.KcPropositionalFiniteModels.Search

namespace Lemmatheca.ProofTheory.Intuitionistic.LCFiniteModels

open Lemmatheca.MathematicalLogic.Propositional
open Kripke Extensions FiniteModels

/-- All tests use the same native formulas, relation, valuation and two indices. -/
def candidate {n : ℕ} (H : List Formula) (A : Formula)
    (r : RelationCode n) (v : ValuationCode n (problemAtoms H.toFinset A))
    (root top : Fin n) : Bool :=
  KCFiniteModels.candidate H A r v root top && comparable r

theorem candidate_correct {n : ℕ} (H : List Formula) (A : Formula)
    (r : RelationCode n) (v : ValuationCode n (problemAtoms H.toFinset A))
    (root top : Fin n) :
    candidate H A r v root top = true ↔
      Admissible r v ∧ KCFiniteModels.RootedTop r root top ∧ ComparableCode r ∧
      booleanForcing r v A root = false ∧
      ∀ B ∈ H, booleanForcing r v B root = true := by
  simp only [candidate, Bool.and_eq_true, KCFiniteModels.candidate_correct,
    comparable_correct]
  tauto

/-- Ordinary finite enumeration with a computable table-comparison test. -/
def refute (H : List Formula) (A : Formula) : Bool :=
  decide (∃ n : Fin (worldBound H.toFinset A + 1),
    ∃ r : RelationCode n.val,
    ∃ v : ValuationCode n.val (problemAtoms H.toFinset A),
    ∃ root top : Fin n.val, candidate H A r v root top = true)

theorem refute_iff_not_derives (H : List Formula) (A : Formula) :
    refute H A = true ↔
      ¬ SchemaConsequence Dummett.axioms (H.toFinset : Set Formula) A := by
  classical
  simp only [refute, decide_eq_true_eq]
  constructor
  · rintro ⟨n, r, v, root, top, hpass⟩ hd
    obtain ⟨hg, hc, hcomp, hf, hH⟩ := (candidate_correct H A r v root top).mp hpass
    have hn : 0 < n.val := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
    let M := codeModel r v hn hg
    have hΓ : @ForcesContext ℕ (Fin n.val) (codePreorder r v hg) M root
        (H.toFinset : Set Formula) := by
      intro B hB
      exact (booleanForcing_correct r v hn hg B root).mp
        (hH B (List.mem_toFinset.mp hB))
    have hA := @chain_sound (Fin n.val) (codePreorder r v hg)
      M hcomp (H.toFinset : Set Formula) A hd root hΓ
    have ht := (booleanForcing_correct r v hn hg A root).mpr hA
    exact Bool.noConfusion (hf.symm.trans ht)
  · intro hn
    obtain ⟨W, rW, fW, M, root, top, hBound, hr, ht, hcomp, hM⟩ :=
      finite_countermodel H.toFinset A hn
    let : PartialOrder W := rW
    let : Fintype W := fW
    let n := Fintype.card W
    let b : Fin n ≃ W := (Fintype.equivFin W).symm
    let S := problemAtoms H.toFinset A
    let r := presentRelation b
    let v := presentValuation M b S
    let i := b.symm root
    let t := b.symm top
    refine ⟨⟨n, Nat.lt_succ_of_le hBound⟩, r, v, i, t, ?_⟩
    apply (candidate_correct H A r v i t).mpr
    refine ⟨presentation_admissible M b S,
      KCFiniteModels.presentation_rootedTop b root top hr ht,
      presentation_comparable b hcomp, ?_, ?_⟩
    · apply Bool.eq_false_of_not_eq_true
      intro hv
      apply hM.2
      have hh := (presentation_forcing M b S A (problem_support H.toFinset A).1 i).mp hv
      simpa [i] using hh
    · intro B hB
      have hB' : B ∈ H.toFinset := List.mem_toFinset.mpr hB
      apply (presentation_forcing M b S B ((problem_support H.toFinset A).2 B hB') i).mpr
      simpa [i] using hM.1 B hB' 

theorem refute_false_iff_derives (H : List Formula) (A : Formula) :
    refute H A = false ↔
      SchemaConsequence Dummett.axioms (H.toFinset : Set Formula) A := by
  classical
  exact Bool.eq_false_iff.trans
    ((not_congr (refute_iff_not_derives H A)).trans Classical.not_not)

end Lemmatheca.ProofTheory.Intuitionistic.LCFiniteModels
