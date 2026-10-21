import Lemmatheca.PaProofCheckers.PAProofAxiomScan

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance proofCheckerWellformedLocalInstance1 (P : Prop) : Decidable P := Classical.propDecidable P

def BooleanValue (a : M) : Prop := a = zeroValue M ∨ a = numeralValue M 1

omit [M ⊨ PA] in
theorem truthValue_boolean (P : Prop) : BooleanValue (truthValue (M := M) P) := by
  by_cases hp : P <;> simp [BooleanValue, truthValue, hp]

omit [M ⊨ PA] in
theorem boolean_ne_one {a : M} (ha : BooleanValue a) (hne : a ≠ zeroValue M) :
    a = numeralValue M 1 := ha.resolve_left hne

theorem multiplication_boolean {a b : M} (ha : BooleanValue a) (hb : BooleanValue b) :
    BooleanValue (mulValue M a b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp only [zero_mul_value, mul_zero_value, numeral_one_mul_model] <;>
    simp [BooleanValue]

theorem namedForm_boolean (n e : M) : BooleanValue (namedForm.value ![n, e]) := by
  rw [namedForm_value]
  exact truthValue_boolean _

theorem listAll_boolean (h : Program 2) (p c : M)
    (hh : ∀ a : M, BooleanValue (h.value ![p, a])) :
    BooleanValue ((listAll h).value ![p, c]) := by
  have hall : ∀ c : M, ∀ p,
      (∀ a : M, BooleanValue (h.value ![p, a])) →
      BooleanValue ((listAll h).value ![p, c]) := by
    apply list_code_induction
    · change DPred (fun v : Fin 1 → M => ∀ p,
        (∀ a : M, BooleanValue (h.value ![p, a])) →
          BooleanValue ((listAll h).value ![p, v 0]))
      unfold BooleanValue
      pa_definable
    · intro p _
      rw [listAll_zero_value]
      exact Or.inr rfl
    · intro a c ih p hb
      rw [listAll_cons_value]
      exact multiplication_boolean (hb a) (ih p hb)
  exact hall c p hh

theorem formList_boolean (p gamma : M) : BooleanValue (formList.value ![p, gamma]) := by
  unfold formList
  apply listAll_boolean
  intro a
  simpa only [binary_value, Program.value_proj, Matrix.cons_val_one, Matrix.cons_val_zero, constant_value,
    numeral_value_zero] using namedForm_boolean (zeroValue M) a

theorem mul_ne_zero_left {a b : M} (h : mulValue M a b ≠ zeroValue M) : a ≠ zeroValue M := by
  intro ha
  exact h (by rw [ha, zero_mul_value])

theorem mul_ne_zero_right {a b : M} (h : mulValue M a b ≠ zeroValue M) : b ≠ zeroValue M := by
  intro hb
  exact h (by rw [hb, mul_zero_value])

theorem localCheck_well_formed (d hist : M)
    (hd : localCheck.value ![d, hist] ≠ zeroValue M) :
    namedForm.value ![zeroValue M, conclusionValue d] = numeralValue M 1 ∧
      formList.value ![zeroValue M, contextValue d] = numeralValue M 1 := by
  unfold localCheck at hd
  rw [conjunction_cons_value] at hd
  have hrest := mul_ne_zero_right hd
  rw [conjunction_cons_value] at hrest
  have hform := mul_ne_zero_left hrest
  have hctx := mul_ne_zero_right hrest
  rw [conjunction_cons_value] at hctx
  have hctx' := mul_ne_zero_left hctx
  simp only [binary_value, unary_value, Program.value_proj, constant_value,
    Matrix.cons_val_zero, numeral_value_zero] at hform hctx'
  exact ⟨boolean_ne_one (namedForm_boolean _ _) hform,
    boolean_ne_one (formList_boolean _ _) hctx'⟩

theorem derivationCheck_equation_value (d : M) :
    derivationCheck.value ![d] =
      sign.value ![localCheck.value ![d, (history localCheck).value ![d] ] ] := by
  have hv (a : M) : Fin.snoc (Fin.elim0 : Fin 0 → M) a = ![a] := by
    ext i; fin_cases i; rfl
  have hv2 (a : M) : Fin.snoc (![d] : Fin 1 → M) a = ![d, a] := by
    ext i; fin_cases i <;> rfl
  have he := courseValue_value localCheck (Fin.elim0 : Fin 0 → M) d
  simp only [hv, hv2] at he
  simp only [derivationCheck, unary_value, he]

theorem derivation_well_formed (d : M)
    (hd : derivationCheck.value ![d] = numeralValue M 1) :
    namedForm.value ![zeroValue M, conclusionValue d] = numeralValue M 1 ∧
      formList.value ![zeroValue M, contextValue d] = numeralValue M 1 := by
  rw [derivationCheck_equation_value, sign_value] at hd
  have hne : localCheck.value ![d, (history localCheck).value ![d] ] ≠ zeroValue M := by
    intro hzero
    simp only [hzero, ↓reduceIte] at hd
    exact Nat.one_ne_zero ((zero_eq_numeral_iff_model 1).mp hd)
  exact localCheck_well_formed d _ hne

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
