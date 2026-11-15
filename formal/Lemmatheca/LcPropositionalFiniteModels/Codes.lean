import Lemmatheca.LcPropositionalFiniteModels.Countermodels
import Lemmatheca.KcPropositionalFiniteModels.Codes

namespace Lemmatheca.ProofTheory.Intuitionistic.LCFiniteModels

open Lemmatheca.MathematicalLogic.Propositional
open Kripke FiniteModels

/-- Pairwise comparability for the supplied table, independently of index order. -/
def ComparableCode {n : ℕ} (r : RelationCode n) : Prop :=
  ∀ i j, r i j = true ∨ r j i = true

instance comparableCodeDecidable {n : ℕ} (r : RelationCode n) :
    Decidable (ComparableCode r) := by
  unfold ComparableCode
  infer_instance

def comparable {n : ℕ} (r : RelationCode n) : Bool :=
  decide (ComparableCode r)

theorem comparable_correct {n : ℕ} (r : RelationCode n) :
    comparable r = true ↔ ComparableCode r := by
  simp [comparable]

theorem code_comparable {n : ℕ} {S : Finset ℕ}
    (r : RelationCode n) (v : ValuationCode n S)
    (h : Admissible r v) (hc : ComparableCode r) :
    ∀ i j : Fin n,
      @LE.le (Fin n) (codePreorder r v h).toLE i j ∨
        @LE.le (Fin n) (codePreorder r v h).toLE j i := by
  exact hc

theorem code_forces_linearity {n : ℕ} {S : Finset ℕ}
    (r : RelationCode n) (v : ValuationCode n S) (hn : 0 < n)
    (h : Admissible r v) (hc : ComparableCode r)
    (i : Fin n) (A B : Formula) :
    @Forces ℕ (Fin n) (codePreorder r v h) (codeModel r v hn h) i
      (Dummett.linearity A B) := by
  exact @Dummett.linear_cone_forces_linearity ℕ (Fin n) (codePreorder r v h)
    (codeModel r v hn h) i (fun u v _ _ => hc u v) A B

theorem presentation_comparable {W : Type u} [Preorder W] {n : ℕ}
    (b : Fin n ≃ W) (hc : ∀ u v : W, u ≤ v ∨ v ≤ u) :
    ComparableCode (presentRelation b) := by
  classical
  simp only [ComparableCode, presentRelation, decide_eq_true_eq]
  exact fun i j => hc (b i) (b j)

end Lemmatheca.ProofTheory.Intuitionistic.LCFiniteModels
