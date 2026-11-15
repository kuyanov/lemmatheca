import Lemmatheca.IntuitionisticPropositionalG4ip.Calculus
import Mathlib.Tactic.Linarith

namespace Lemmatheca.ProofTheory.Intuitionistic.G4ip
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
universe u
variable {α : Type u} [DecidableEq α]

/-- The value on native negation is its expanded weight; reduced goals need no
native-negation rule. -/
def weight : PropFormula α → ℕ
  | .atom _ | .falsum => 2
  | .neg A => 1 + weight A * 2
  | .conj A B => weight A * (1 + weight B)
  | .disj A B => 1 + weight A + weight B
  | .impl A B => 1 + weight A * weight B

def contextWeight (Γ : Context α) : ℕ := ∑ A ∈ Γ, weight A

def goalWeight (g : Goal α) : ℕ := contextWeight g.1 + weight g.2

omit [DecidableEq α] in
theorem weight_two_le [DecidableEq α] (A : PropFormula α) : 2 ≤ weight A := by
  induction A with
  | atom _ => rfl
  | falsum => rfl
  | neg A ih => simp only [weight]; omega
  | conj A B ihA ihB =>
      simp only [weight]
      nlinarith [Nat.mul_le_mul_right (1 + weight B) ihA]
  | disj A B ihA ihB => simp only [weight]; omega
  | impl A B ihA ihB =>
      simp only [weight]
      nlinarith [Nat.mul_le_mul_right (weight B) ihA]

private theorem insertWeight_le (Γ : Context α) (A : PropFormula α) :
    contextWeight (insert A Γ) ≤ weight A + contextWeight Γ := by
  by_cases h : A ∈ Γ
  · rw [Finset.insert_eq_of_mem h]
    omega
  · simp [contextWeight, Finset.sum_insert h]

private theorem eraseWeight {Γ : Context α} {F : PropFormula α} (h : F ∈ Γ) :
    contextWeight (remainder Γ F) + weight F = contextWeight Γ := by
  exact Finset.sum_erase_add Γ weight h

omit [DecidableEq α] in
private theorem sameContext_lt {Γ : Context α} {A E : PropFormula α}
    (h : weight A < weight E) : goalWeight (Γ, A) < goalWeight (Γ, E) := by
  simpa only [goalWeight, Nat.add_lt_add_iff_left] using h

private theorem replaceNone_lt {Γ : Context α} {F E A : PropFormula α}
    (hF : F ∈ Γ) (h : weight A < weight F + weight E) :
    goalWeight (remainder Γ F, A) < goalWeight (Γ, E) := by
  have he := eraseWeight hF
  simp only [goalWeight]
  omega

private theorem replaceOne_lt {Γ : Context α} {F X E A : PropFormula α}
    (hF : F ∈ Γ) (h : weight X + weight A < weight F + weight E) :
    goalWeight (insert X (remainder Γ F), A) < goalWeight (Γ, E) := by
  have he := eraseWeight hF
  have hi := insertWeight_le (remainder Γ F) X
  simp only [goalWeight]
  omega

private theorem replaceTwo_lt {Γ : Context α} {F X Y E A : PropFormula α}
    (hF : F ∈ Γ) (h : weight X + weight Y + weight A < weight F + weight E) :
    goalWeight (insert X (insert Y (remainder Γ F)), A) < goalWeight (Γ, E) := by
  have he := eraseWeight hF
  have hi := insertWeight_le (insert Y (remainder Γ F)) X
  have hj := insertWeight_le (remainder Γ F) Y
  simp only [goalWeight]
  omega

private theorem sum_le_product (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    a + b ≤ a * b := by
  have h₁ := Nat.mul_le_mul_left a hb
  have h₂ := Nat.mul_le_mul_right b ha
  nlinarith


theorem rule_decrease {child parent : Goal α} (h : Backward child parent) :
    goalWeight child < goalWeight parent := by
  cases h with
  | conjRightLeft Γ A B =>
      apply sameContext_lt
      have ha := weight_two_le A
      have hb := weight_two_le B
      simp only [weight]
      nlinarith [Nat.mul_le_mul_left (weight A) hb]
  | conjRightRight Γ A B =>
      apply sameContext_lt
      have ha := weight_two_le A
      have hb := weight_two_le B
      simp only [weight]
      nlinarith [Nat.mul_le_mul_right (1 + weight B) ha]
  | disjRightLeft Γ A B =>
      apply sameContext_lt
      have hb := weight_two_le B
      simp only [weight]
      omega
  | disjRightRight Γ A B =>
      apply sameContext_lt
      have ha := weight_two_le A
      simp only [weight]
      omega
  | implRight Γ A B =>
      have hi := insertWeight_le Γ A
      have hab := sum_le_product (weight A) (weight B) (weight_two_le A) (weight_two_le B)
      simp only [goalWeight, weight]
      omega
  | @conjLeft Γ A B E hF =>
      apply replaceTwo_lt hF
      have ha := weight_two_le A
      have hb := weight_two_le B
      simp only [weight]
      nlinarith [Nat.mul_le_mul_right (weight B) ha]
  | @disjLeftLeft Γ A B E hF =>
      apply replaceOne_lt hF
      simp only [weight]
      omega
  | @disjLeftRight Γ A B E hF =>
      apply replaceOne_lt hF
      simp only [weight]
      omega
  | @atomImplLeft Γ a B E hF _ =>
      apply replaceOne_lt hF
      have hb := weight_two_le B
      simp only [weight]
      omega
  | @botImplLeft Γ B E hF =>
      apply replaceNone_lt hF
      simp only [weight]
      omega
  | @conjImplLeft Γ A B C E hF =>
      apply replaceOne_lt hF
      have ha := weight_two_le A
      have hc := weight_two_le C
      simp only [weight]
      nlinarith [Nat.mul_le_mul_left (weight A) hc]
  | @disjImplLeft Γ A B C E hF =>
      apply replaceTwo_lt hF
      have hc := weight_two_le C
      simp only [weight]
      nlinarith
  | @implImplLeftFirst Γ A B C E hF =>
      apply replaceOne_lt hF
      have he := weight_two_le E
      have hc := weight_two_le C
      have hac := sum_le_product (weight A) (weight C) (weight_two_le A) hc
      have hm := Nat.mul_le_mul_left (weight B) hac
      simp only [weight]
      nlinarith
  | @implImplLeftSecond Γ A B C E hF =>
      apply replaceOne_lt hF
      simp only [weight, Nat.add_mul, one_mul]
      omega


theorem backward_wellFounded : WellFounded (Backward (α := α)) :=
  (measure goalWeight).wf.mono (fun _ _ h => rule_decrease h)

private def rightPremises (Γ : Context α) : PropFormula α → Finset (Goal α)
  | .conj A B | .disj A B => {(Γ, A), (Γ, B)}
  | .impl A B => {(insert A Γ, B)}
  | _ => ∅

private def leftPremises (Γ : Context α) (E : PropFormula α) :
    PropFormula α → Finset (Goal α)
  | .conj A B => {(insert A (insert B (remainder Γ (conj A B))), E)}
  | .disj A B => {(insert A (remainder Γ (disj A B)), E),
      (insert B (remainder Γ (disj A B)), E)}
  | .impl (.atom a) B => if atom a ∈ Γ then
      {(insert B (remainder Γ (impl (atom a) B)), E)} else ∅
  | .impl .falsum B => {(remainder Γ (impl falsum B), E)}
  | .impl (.conj A B) C =>
      {(insert (impl A (impl B C)) (remainder Γ (impl (conj A B) C)), E)}
  | .impl (.disj A B) C =>
      {(insert (impl A C) (insert (impl B C) (remainder Γ (impl (disj A B) C))), E)}
  | .impl (.impl A B) C =>
      {(insert (impl B C) (remainder Γ (impl (impl A B) C)), impl A B),
        (insert C (remainder Γ (impl (impl A B) C)), E)}
  | _ => ∅

theorem finite_backward_premises (g : Goal α) : Set.Finite {child | Backward child g} := by
  obtain ⟨Γ, E⟩ := g
  apply (Finset.finite_toSet (rightPremises Γ E ∪ Γ.biUnion (leftPremises Γ E))).subset
  intro child hc
  cases hc with
  | conjRightLeft Γ A B => exact Finset.mem_union_left _ (by simp [rightPremises])
  | conjRightRight Γ A B => exact Finset.mem_union_left _ (by simp [rightPremises])
  | disjRightLeft Γ A B => exact Finset.mem_union_left _ (by simp [rightPremises])
  | disjRightRight Γ A B => exact Finset.mem_union_left _ (by simp [rightPremises])
  | implRight Γ A B => exact Finset.mem_union_left _ (by simp [rightPremises])
  | @conjLeft Γ A B E h =>
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, h, by simp [leftPremises]⟩)
  | @disjLeftLeft Γ A B E h =>
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, h, by simp [leftPremises]⟩)
  | @disjLeftRight Γ A B E h =>
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, h, by simp [leftPremises]⟩)
  | @atomImplLeft Γ a B E h ha =>
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, h, by simp [leftPremises, ha]⟩)
  | @botImplLeft Γ B E h =>
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, h, by simp [leftPremises]⟩)
  | @conjImplLeft Γ A B C E h =>
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, h, by simp [leftPremises]⟩)
  | @disjImplLeft Γ A B C E h =>
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, h, by simp [leftPremises]⟩)
  | @implImplLeftFirst Γ A B C E h =>
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, h, by simp [leftPremises]⟩)
  | @implImplLeftSecond Γ A B C E h =>
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, h, by simp [leftPremises]⟩)

def Proof.height {Γ : Context α} {E : PropFormula α} (p : Proof Γ E) : ℕ :=
  match p with
  | .atom _ | .falsumLeft _ => 0
  | .conjRight p q | .disjLeft _ p q | .implImplLeft _ p q => 1 + max p.height q.height
  | .disjRightLeft p | .disjRightRight p | .implRight p | .conjLeft _ p |
      .atomImplLeft _ _ p | .botImplLeft _ p | .conjImplLeft _ p |
      .disjImplLeft _ p => 1 + p.height

theorem Proof.height_lt_weight {Γ : Context α} {E : PropFormula α} (p : Proof Γ E) :
    p.height < goalWeight (Γ, E) := by
  induction p with
  | atom h => simp only [Proof.height, goalWeight, weight]; omega
  | @falsumLeft Γ E h =>
      have he := weight_two_le E
      simp only [Proof.height, goalWeight]
      omega
  | @conjRight Γ A B p q ihp ihq =>
      have hp := rule_decrease (Backward.conjRightLeft Γ A B)
      have hq := rule_decrease (Backward.conjRightRight Γ A B)
      simp only [Proof.height]
      omega
  | @disjRightLeft Γ A B p ih =>
      have hw := rule_decrease (Backward.disjRightLeft Γ A B)
      simp only [Proof.height]
      omega
  | @disjRightRight Γ A B p ih =>
      have hw := rule_decrease (Backward.disjRightRight Γ A B)
      simp only [Proof.height]
      omega
  | @implRight Γ A B p ih =>
      have hw := rule_decrease (Backward.implRight Γ A B)
      simp only [Proof.height]
      omega
  | @conjLeft Γ A B E h p ih =>
      have hw := rule_decrease (Backward.conjLeft (E := E) h)
      simp only [Proof.height]
      omega
  | @disjLeft Γ A B E h p q ihp ihq =>
      have hp := rule_decrease (Backward.disjLeftLeft (E := E) h)
      have hq := rule_decrease (Backward.disjLeftRight (E := E) h)
      simp only [Proof.height]
      omega
  | @atomImplLeft Γ a B E h ha p ih =>
      have hw := rule_decrease (Backward.atomImplLeft (E := E) h ha)
      simp only [Proof.height]
      omega
  | @botImplLeft Γ B E h p ih =>
      have hw := rule_decrease (Backward.botImplLeft (E := E) h)
      simp only [Proof.height]
      omega
  | @conjImplLeft Γ A B C E h p ih =>
      have hw := rule_decrease (Backward.conjImplLeft (E := E) h)
      simp only [Proof.height]
      omega
  | @disjImplLeft Γ A B C E h p ih =>
      have hw := rule_decrease (Backward.disjImplLeft (E := E) h)
      simp only [Proof.height]
      omega
  | @implImplLeft Γ A B C E h p q ihp ihq =>
      have hp := rule_decrease (Backward.implImplLeftFirst (E := E) h)
      have hq := rule_decrease (Backward.implImplLeftSecond (E := E) h)
      simp only [Proof.height]
      omega

end Lemmatheca.ProofTheory.Intuitionistic.G4ip
