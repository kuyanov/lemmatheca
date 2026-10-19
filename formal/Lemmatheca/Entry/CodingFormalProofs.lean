import Lemmatheca.MathematicalLogic.CodingFormalProofsCorrectness

namespace Lemmatheca.Entry.CodingFormalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open Lemmatheca.MathematicalLogic.CodingFormalProofs
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

/-- The deliberately defective last-line test permits the current candidate as
its own minor premise. The earlier implication is checked separately. -/
def circularMPCheck (earlier candidate : ℕ) : Bool :=
  earlier = impCode candidate candidate

/-- The legitimate first line in the circular-proof counterexample is itself
accepted by the actual nineteen-rule derivation checker. -/
theorem identity_record (A : L.Formula ℕ) :
    ∃ d, Der S d (contextCode S []) (namedCode S (A.imp A)) := by
  classical
  apply (checked_sequent_iff S [] (A.imp A)).mpr
  exact FirstOrderProofs.Proof.impIntro
    (FirstOrderProofs.Proof.assumption (by simp))

/-- The faulty test accepts falsity after a genuinely checked identity proof,
even though falsity has no derivation from the empty original-language theory. -/
theorem circular_false_accepted :
    ∃ d, Der S d (contextCode S []) (impCode botCode botCode) ∧
      circularMPCheck (proofConclusion d) botCode = true ∧
      ¬ FirstOrderProofs.Derives (∅ : L.Theory) (⊥ : L.Sentence) := by
  obtain ⟨d, hd, hctx, hcon⟩ := identity_record S (⊥ : L.Formula ℕ)
  refine ⟨d, ⟨hd, hctx, hcon⟩, ?_, FirstOrderProofs.empty_theory_consistent L⟩
  simp [circularMPCheck, hcon]

end Lemmatheca.Entry.CodingFormalProofs
