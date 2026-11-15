import Lemmatheca.KcPropositionalFiniteModels.Codes

namespace Lemmatheca.ProofTheory.Intuitionistic.KCFiniteModels

open Lemmatheca.MathematicalLogic.Propositional
open Kripke Extensions
open FiniteModels

/-- Executable checks on the same root, tables and native formulas. -/
def candidate {n : ℕ} (H : List Formula) (A : Formula)
    (r : RelationCode n) (v : ValuationCode n (problemAtoms H.toFinset A))
    (root top : Fin n) : Bool :=
  admissible r v && rootedTop r root top && !(booleanForcing r v A root) &&
    H.all (fun B => booleanForcing r v B root)

theorem candidate_correct {n : ℕ} (H : List Formula) (A : Formula)
    (r : RelationCode n) (v : ValuationCode n (problemAtoms H.toFinset A))
    (root top : Fin n) :
    candidate H A r v root top = true ↔
      Admissible r v ∧ RootedTop r root top ∧
      booleanForcing r v A root = false ∧
      ∀ B ∈ H, booleanForcing r v B root = true := by
  simp [candidate, admissible, rootedTop, List.all_eq_true, and_assoc]

/-- Bounded finite enumeration; no derivability oracle or classical choice enters the program. -/
def refute (H : List Formula) (A : Formula) : Bool :=
  decide (∃ n : Fin (worldBound H.toFinset A + 1),
    ∃ r : RelationCode n.val,
    ∃ v : ValuationCode n.val (problemAtoms H.toFinset A),
    ∃ root top : Fin n.val, candidate H A r v root top = true)

theorem refute_iff_not_derives (H : List Formula) (A : Formula) :
    refute H A = true ↔
      ¬ SchemaConsequence WeakExcludedMiddle.axioms (H.toFinset : Set Formula) A := by
  classical
  simp only [refute, decide_eq_true_eq]
  constructor
  · rintro ⟨n, r, v, root, top, hpass⟩ hd
    obtain ⟨hg, hc, hf, hH⟩ := (candidate_correct H A r v root top).mp hpass
    have hn : 0 < n.val := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
    let M := codeModel r v hn hg
    have hΓ : @ForcesContext ℕ (Fin n.val) (codePreorder r v hg) M root
        (H.toFinset : Set Formula) := by
      intro B hB
      exact (booleanForcing_correct r v hn hg B root).mp
        (hH B (List.mem_toFinset.mp hB))
    have hA := @greatest_world_sound (Fin n.val) (codePreorder r v hg)
      M top hc.2.1 (H.toFinset : Set Formula) A hd root hΓ
    have ht := (booleanForcing_correct r v hn hg A root).mpr hA
    exact Bool.noConfusion (hf.symm.trans ht)
  · intro hn
    obtain ⟨W, rW, fW, M, root, top, hBound, hr, ht, hM⟩ :=
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
    refine ⟨presentation_admissible M b S, presentation_rootedTop b root top hr ht,
      ?_, ?_⟩
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
      SchemaConsequence WeakExcludedMiddle.axioms (H.toFinset : Set Formula) A := by
  classical
  exact Bool.eq_false_iff.trans
    ((not_congr (refute_iff_not_derives H A)).trans Classical.not_not)

theorem refute_same_premises (H K : List Formula) (A : Formula)
    (h : H.toFinset = K.toFinset) : refute H A = refute K A := by
  have hh := refute_iff_not_derives H A
  have hk := refute_iff_not_derives K A
  rw [h] at hh
  have he := hh.trans hk.symm
  cases hH : refute H A <;> cases hK : refute K A <;> simp_all

theorem refute_falsum_premise (A : Formula) :
    refute [.falsum] A = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [refute, decide_eq_true_eq] at h
  obtain ⟨n, r, v, root, top, hp⟩ := h
  have hbot := (candidate_correct [.falsum] A r v root top).mp hp
  have hf := hbot.2.2.2 .falsum (by simp)
  exact Bool.noConfusion hf

end Lemmatheca.ProofTheory.Intuitionistic.KCFiniteModels
