import Lemmatheca.IntuitionisticPropositionalFiniteFiltrations.Filtrations

-- Retain the public name used by the later Dummett examples.
namespace Lemmatheca.Entry.PropositionalDummettLinearity

/-- A named non-instance: the ordinary Boolean chain instance is never replaced. -/
@[instance_reducible] def discretePreorder : Preorder Bool where
  le := Eq
  lt := fun _ _ => False
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  lt_iff_le_not_ge _ _ := ⟨False.elim, fun h => h.2 h.1.symm⟩


end Lemmatheca.Entry.PropositionalDummettLinearity

namespace Lemmatheca.Entry.IntuitionisticPropositionalFiniteFiltrations

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Lemmatheca.ProofTheory.Intuitionistic
open Kripke
open Filtrations
open Classical

/-- Reuse the existing discrete frame without changing the standard Boolean order. -/
local instance : Preorder Bool :=
  Lemmatheca.Entry.PropositionalDummettLinearity.discretePreorder

/-- The original world u is false, v is true, and only p₀ holds at v. -/
def discreteModel : Model ℕ Bool where
  world_nonempty := ⟨false⟩
  valuation w p := w = true ∧ p = 0
  persistent h _ hp := h ▸ hp

def exampleTracked : Finset Filtrations.Formula := {atom 0}

theorem example_closed : FiniteModels.SubformulaClosed exampleTracked := by
  simp [FiniteModels.SubformulaClosed, exampleTracked, FiniteModels.subformulas]

theorem example_traces :
    trace discreteModel exampleTracked false = ∅ ∧
      trace discreteModel exampleTracked true = {atom 0} ∧
      ∀ s : TraceWorld discreteModel exampleTracked,
        s = traceWorld discreteModel exampleTracked false ∨
        s = traceWorld discreteModel exampleTracked true := by
  refine ⟨?_, ?_, ?_⟩
  · ext A
    constructor
    · intro h
      obtain ⟨hA, hF⟩ := (trace_mem discreteModel exampleTracked false A).mp h
      have heq : A = atom 0 := Finset.mem_singleton.mp hA
      subst A
      exact (Bool.false_ne_true hF.1).elim
    · intro h
      simp at h
  · ext A
    constructor
    · intro h
      exact ((trace_mem discreteModel exampleTracked true A).mp h).1
    · intro h
      have heq : A = atom 0 := Finset.mem_singleton.mp h
      subst A
      exact (trace_mem discreteModel exampleTracked true (atom 0)).mpr
        ⟨by simp [exampleTracked], rfl, rfl⟩
  · intro s
    obtain ⟨w, hw⟩ := s.property
    have heq : traceWorld discreteModel exampleTracked w = s := Subtype.ext hw
    subst s
    cases w
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem example_added_comparison :
    traceWorld discreteModel exampleTracked false <
        traceWorld discreteModel exampleTracked true ∧
      ¬ (@LE.le Bool
        Lemmatheca.Entry.PropositionalDummettLinearity.discretePreorder.toLE
        false true) := by
  constructor
  · change trace discreteModel exampleTracked false <
      trace discreteModel exampleTracked true
    rw [example_traces.1, example_traces.2.1]
    simp
  · exact Bool.false_ne_true

theorem example_not_bounded :
    ¬ IsBoundedFrameMap (traceWorld discreteModel exampleTracked) := by
  intro h
  obtain ⟨z, hz, he⟩ := h.back false
    (traceWorld discreteModel exampleTracked true)
    (le_of_lt example_added_comparison.1)
  change false = z at hz
  subst z
  exact (ne_of_lt example_added_comparison.1) he

theorem example_atom_values :
    ¬ Forces (traceModel discreteModel exampleTracked)
        (traceWorld discreteModel exampleTracked false) (atom 0) ∧
      Forces (traceModel discreteModel exampleTracked)
        (traceWorld discreteModel exampleTracked true) (atom 0) := by
  change atom 0 ∉ trace discreteModel exampleTracked false ∧
    atom 0 ∈ trace discreteModel exampleTracked true
  rw [example_traces.1, example_traces.2.1]
  simp

theorem example_changed_formulas :
    Forces discreteModel false (neg (atom 0)) ∧
      Forces discreteModel false (disj (atom 0) (neg (atom 0))) ∧
      ¬ Forces (traceModel discreteModel exampleTracked)
        (traceWorld discreteModel exampleTracked false) (neg (atom 0)) ∧
      ¬ Forces (traceModel discreteModel exampleTracked)
        (traceWorld discreteModel exampleTracked false) (disj (atom 0) (neg (atom 0))) ∧
      neg (atom 0) ∉ exampleTracked ∧
      disj (atom 0) (neg (atom 0)) ∉ exampleTracked := by
  have hn : Forces discreteModel false (neg (atom 0)) := by
    intro z hz h
    change false = z at hz
    subst z
    exact Bool.false_ne_true h.1
  have hnf : ¬ Forces (traceModel discreteModel exampleTracked)
      (traceWorld discreteModel exampleTracked false) (neg (atom 0)) := by
    intro h
    exact h (traceWorld discreteModel exampleTracked true)
      (le_of_lt example_added_comparison.1) example_atom_values.2
  refine ⟨hn, Or.inr hn, hnf, ?_, ?_, ?_⟩
  · rintro (h | h)
    · exact example_atom_values.1 h
    · exact hnf h
  · simp [exampleTracked]
  · simp [exampleTracked]

theorem discrete_frame_excluded_middle (M : Model ℕ Bool) (w : Bool)
    (A : Filtrations.Formula) : Forces M w (disj A (neg A)) := by
  by_cases h : Forces M w A
  · exact Or.inl h
  · right
    intro z hz hzA
    change w = z at hz
    subst z
    exact h hzA

end Lemmatheca.Entry.IntuitionisticPropositionalFiniteFiltrations
