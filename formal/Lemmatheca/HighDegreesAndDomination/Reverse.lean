import Lemmatheca.HighDegreesAndDomination.Maximum
import Lemmatheca.HighDegreesAndDomination.Deadlines

/-! The exact Q driver, its binary guesses, and the converse implication. -/
namespace Lemmatheca.ComputabilityTheory.HighDegreesAndDomination

open UniversalComputation OracleComputation OracleProgramNumberings TuringDegrees
open BusyBeaverFunctions (ordinaryProgram ordinaryProgram_eval)
open RelativizedLimitComputability

noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false
local notation "TOT" => Lemmatheca.Entry.ArithmeticalHierarchy.Totality

def totalityGuess (g : ℕ → ℕ) (s e : ℕ) : ℕ :=
  if ∀ x ≤ s, 0 < UniversalComputation.boundedValue (g s) e x then 1 else 0

private def suppliedFunctionInput (p : ℕ) : ℕ := Nat.pair p.unpair.1 p.unpair.2.unpair.1
private def guessOutput (w : ℕ) : ℕ :=
  if ∀ x ≤ w.unpair.1.unpair.2.unpair.1,
      0 < UniversalComputation.boundedValue w.unpair.2 w.unpair.1.unpair.2.unpair.2 x
    then 1 else 0

private theorem guess_routines_computable :
    Computable suppliedFunctionInput ∧ Computable guessOutput := by
  have l : Primrec (fun p : ℕ => p.unpair.1) := Primrec.fst.comp Primrec.unpair
  have r : Primrec (fun p : ℕ => p.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hi : Primrec suppliedFunctionInput := Primrec₂.natPair.comp l (l.comp r)
  have hargs : Primrec (fun w : ℕ => Nat.pair
      (Nat.pair w.unpair.1.unpair.2.unpair.2 w.unpair.1.unpair.2.unpair.1) w.unpair.2) :=
    Primrec₂.natPair.comp
      (Primrec₂.natPair.comp (r.comp (r.comp l)) (l.comp (r.comp l))) r
  have hb := deadline_test_computable.comp hargs.to_comp
  have ho := Computable.cond hb (Computable.const 1) (Computable.const 0)
  refine ⟨hi.to_comp, ho.of_eq fun w => ?_⟩
  simp only [deadlineTest, Nat.unpair_pair, guessOutput]
  split <;> simp_all

def guessDriverCode : Code :=
  .comp (embed (ordinaryProgram guessOutput guess_routines_computable.2))
    (.pair identityCode (.comp universalCode
      (embed (ordinaryProgram suppliedFunctionInput guess_routines_computable.1))))

def guessCompiler (d : ℕ) : ℕ :=
  OracleProgramNumberings.specialize (encodeCode guessDriverCode) d

theorem guess_compiler_primitive : Primrec guessCompiler := by
  exact specialize_primitive.comp (Primrec.const (encodeCode guessDriverCode)) Primrec.id

theorem guess_compiler_eval (A : Set ℕ) (d : ℕ) (g : ℕ → ℕ)
    (hd : ∀ s, OracleProgramNumberings.phi A d s = Part.some (g s)) (s e : ℕ) :
    OracleProgramNumberings.phi A (guessCompiler d) (Nat.pair s e) =
      Part.some (totalityGuess g s e) := by
  rw [guessCompiler, OracleProgramNumberings.specialize_eval]
  simp only [OracleProgramNumberings.phi, decode_encode]
  simp [guessDriverCode, eval, eval_embed, ordinaryProgram_eval, identity_eval,
    suppliedFunctionInput, Nat.unpair_pair, universal_code_eval, hd,
    guessOutput, totalityGuess]

theorem guess_joint_computable (A : Set ℕ) (g : ℕ → ℕ)
    (hg : PartialComputable A (fun s => Part.some (g s))) :
    JointComputableIn A (totalityGuess g) ∧ LimitComputability.Binary (totalityGuess g) := by
  obtain ⟨d, hd⟩ := (indexed_complete A (fun s => Part.some (g s))).mp hg
  refine ⟨(joint_index_iff A (totalityGuess g)).mpr ⟨guessCompiler d,
    guess_compiler_eval A d g (fun s => congrFun hd s)⟩, ?_⟩
  intro s e
  unfold totalityGuess
  split <;> simp

theorem guess_converges (g : ℕ → ℕ) (hg : DominatesComputable g) :
    ConvergesTo (totalityGuess g) (indicator TOT) := by
  intro e
  by_cases he : e ∈ TOT
  · obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hg (deadline e he) (deadline_computable e he))
    refine ⟨N, ?_⟩
    intro s hs
    have hgood : ∀ x ≤ s, 0 < boundedValue (g s) e x :=
      (deadline_spec e he s).2.2 (g s) (hN s hs)
    change (if ∀ x ≤ s, 0 < boundedValue (g s) e x then 1 else 0) =
      (if TOT e then 1 else 0)
    rw [ite_eq_left hgood, ite_eq_left (show TOT e from he)]
  · have he' : ¬ ∀ x, (phi e x).Dom := he
    push Not at he'
    obtain ⟨x, hx⟩ := he'
    refine ⟨x, ?_⟩
    intro s hs
    have hfail : ¬ ∀ y ≤ s, 0 < boundedValue (g s) e y := by
      intro h
      exact hx ((phi_domain e x).mpr ⟨g s, h x hs⟩)
    change (if ∀ y ≤ s, 0 < boundedValue (g s) e y then 1 else 0) =
      (if TOT e then 1 else 0)
    rw [ite_eq_right hfail, ite_eq_right (show ¬ TOT e from he)]

theorem dominating_implies_high (A : Set ℕ) (g : ℕ → ℕ)
    (hg : PartialComputable A (fun n => Part.some (g n))) (hdom : DominatesComputable g) :
    High A := by
  obtain ⟨hc, hb⟩ := guess_joint_computable A g hg
  have ht : Reducible TOT (TuringJump.jump A) :=
    (relative_set_limit A TOT).mp ⟨totalityGuess g, hc, hb, guess_converges g hdom⟩
  exact reducible_trans totality_jump_equivalence.2 ht

theorem martin_characterization (A : Set ℕ) :
    High A ↔ ∃ g : ℕ → ℕ,
      PartialComputable A (fun n => Part.some (g n)) ∧ DominatesComputable g := by
  exact ⟨high_computes_dominating A, fun ⟨g, hg, hdom⟩ => dominating_implies_high A g hg hdom⟩

end
end Lemmatheca.ComputabilityTheory.HighDegreesAndDomination
