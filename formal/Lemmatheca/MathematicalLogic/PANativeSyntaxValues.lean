import Lemmatheca.MathematicalLogic.PANativeSyntax

/-! Arithmetic values of the explicit shared-syntax program combinators. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.SyntaxPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance : DecidableEq M := Classical.decEq M
local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem unary_value {n : ℕ} (p : Program 1) (a : Program n) (x : Fin n → M) :
    (unary p a).value x = p.value ![a.value x] := Program.value_comp_one p a x

theorem binary_value {n : ℕ} (p : Program 2) (a b : Program n) (x : Fin n → M) :
    (binary p a b).value x = p.value ![a.value x, b.value x] := Program.value_comp_two p a b x

theorem ternary_value {n : ℕ} (p : Program 3) (a b c : Program n) (x : Fin n → M) :
    (ternary p a b c).value x = p.value ![a.value x, b.value x, c.value x] :=
  Program.value_comp_three p a b c x

theorem quad_value {n : ℕ} (a b c d : Program n) (x : Fin n → M) :
    (quad a b c d).value x = squarePair.value ![a.value x,
      squarePair.value ![b.value x, squarePair.value ![c.value x, d.value x] ] ] := by
  simp only [quad, binary_value]

theorem part_quad_value (i : Fin 4) (a b c d : M) :
    (part i).value ![squarePair.value ![a, squarePair.value ![b, squarePair.value ![c, d] ] ] ] =
      ![a, b, c, d] i := by
  fin_cases i <;>
    simp only [part, unary_value, unpairLeft_pair_value, unpairRight_pair_value] <;> rfl

theorem equalTest_value (a b : M) :
    equalTest.value ![a, b] = if a = b then numeralValue M 1 else zeroValue M := by
  classical
  simp only [equalTest, unary_value, binary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, addition_value, zeroTest_value]
  have hz : addValue M (subtraction.value ![a, b]) (subtraction.value ![b, a]) = zeroValue M ↔ a = b := by
    constructor
    · intro hh
      have hzero := add_eq_zero_value hh
      exact le_antisymm_value ((subtraction_zero_iff a b).mp hzero.1)
        ((subtraction_zero_iff b a).mp hzero.2)
    · intro hab
      subst b
      rw [(subtraction_zero_iff a a).mpr (le_refl_value a), zero_add_value]
  simp only [hz]

@[simp] theorem numeral_eq_iff_model (m n : ℕ) :
    numeralValue M m = numeralValue M n ↔ m = n := by
  let : M ⊨ Q := PA_models_Q M
  exact (numeral_injective M).eq_iff

@[simp] theorem numeral_eq_zero_iff_model (n : ℕ) :
    numeralValue M n = zeroValue M ↔ n = 0 := by
  rw [← numeral_value_zero M]
  exact numeral_eq_iff_model n 0

@[simp] theorem zero_eq_numeral_iff_model (n : ℕ) :
    zeroValue M = numeralValue M n ↔ n = 0 := by
  rw [eq_comm]
  exact numeral_eq_zero_iff_model n

@[simp] theorem numeral_one_mul_model (a : M) :
    mulValue M (numeralValue M 1) a = a := by
  rw [numeral_value_succ, numeral_value_zero, one_mul_value]

@[simp] theorem mul_numeral_one_model (a : M) :
    mulValue M a (numeralValue M 1) = a := by
  rw [numeral_value_succ, numeral_value_zero, mul_one_value]

theorem maximum_value (a b : M) :
    maximum.value ![a, b] = (let := modelLinearOrder M; max a b) := by
  let := modelLinearOrder M
  simp only [maximum, ternary_value, Program.value_proj, Matrix.cons_val_zero,
    Matrix.cons_val_one, less_value, select_value]
  by_cases h : leValue M (succValue M a) b
  · have hab : a < b := (successor_le_iff_lt a b).mp h
    simp only [h, ↓reduceIte, numeral_eq_zero_iff_model, Nat.one_ne_zero,
      max_eq_right hab.le]
  · have hba : b ≤ a :=
      le_of_not_gt (fun hh => h ((successor_le_iff_lt a b).mpr hh))
    simp only [h, ↓reduceIte, max_eq_left hba]

theorem disjoin_value (a b : M) :
    disjoin.value ![a, b] =
      if a = zeroValue M ∧ b = zeroValue M then zeroValue M else numeralValue M 1 := by
  simp only [disjoin, unary_value, addition_value, sign_value]
  have hz : addValue M a b = zeroValue M ↔ a = zeroValue M ∧ b = zeroValue M := by
    constructor
    · exact add_eq_zero_value
    · rintro ⟨rfl, rfl⟩
      exact zero_add_value _
  simp only [hz]

def truthValue (P : Prop) : M := if P then numeralValue M 1 else zeroValue M

@[simp] theorem truthValue_eq_zero_iff (P : Prop) :
    truthValue (M := M) P = zeroValue M ↔ ¬ P := by
  by_cases h : P <;> simp [truthValue, h, successor_ne_zero]

@[simp] theorem truthValue_eq_one_iff (P : Prop) :
    truthValue (M := M) P = numeralValue M 1 ↔ P := by
  by_cases h : P
  · simp only [truthValue, h, ↓reduceIte]
  · simp only [truthValue, h, ↓reduceIte, iff_false]
    rw [numeral_value_succ, numeral_value_zero]
    exact (successor_ne_zero _).symm

theorem multiplication_truthValue (P Q : Prop) :
    mulValue M (truthValue P) (truthValue Q) = truthValue (M := M) (P ∧ Q) := by
  by_cases hp : P <;> by_cases hq : Q <;>
    simp [truthValue, hp, hq, zero_mul_value, mul_zero_value, one_mul_value]

theorem disjoin_truthValue (P Q : Prop) :
    disjoin.value ![truthValue P, truthValue Q] = truthValue (M := M) (P ∨ Q) := by
  rw [disjoin_value]
  simp only [truthValue_eq_zero_iff]
  by_cases hp : P <;> by_cases hq : Q <;> simp [truthValue, hp, hq]

theorem equalTest_truthValue (a b : M) :
    equalTest.value ![a, b] = truthValue (M := M) (a = b) := equalTest_value a b

theorem select_truthValue (P : Prop) (a b : M) :
    select.value ![truthValue P, a, b] = if P then a else b := by
  simp only [select_value, truthValue_eq_zero_iff]
  by_cases h : P <;> simp only [h, not_true_eq_false, not_false_eq_true, ↓reduceIte]

theorem arithmeticFunctionTest_value (f n : M) :
    arithmeticFunctionTest.value ![f, n] = truthValue (M := M)
      ((f = numeralValue M 0 ∧ n = numeralValue M 0) ∨
        (f = numeralValue M 1 ∧ n = numeralValue M 1) ∨
        ((f = numeralValue M 2 ∨ f = numeralValue M 3) ∧ n = numeralValue M 2)) := by
  simp only [arithmeticFunctionTest, binary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, constant_value, equalTest_truthValue,
    multiplication_value, multiplication_truthValue, disjoin_truthValue]
  congr 1
  exact propext or_assoc

theorem sign_truthValue (a : M) :
    sign.value ![a] = truthValue (M := M) (a ≠ zeroValue M) := by
  rw [sign_value]
  by_cases h : a = zeroValue M <;> simp [truthValue, h]

theorem leq_truthValue (a b : M) :
    leq.value ![a, b] = truthValue (M := M) (leValue M a b) := leq_value a b

/-- An externally specified finite constructor spine with arbitrary model
elements as children.  This abbreviation introduces no new formula syntax. -/
def modelList (xs : List M) : M := xs.foldr (fun a c => listCons.value ![a, c]) (zeroValue M)

def modelNode (k : ℕ) (xs : List M) : M := listCons.value ![numeralValue M k, modelList xs]

def termDepth (e : M) : M := (part 0).value ![stats.value ![e] ]
def formDepth (e : M) : M := (part 1).value ![stats.value ![e] ]

theorem depthTest_value (j : Fin 4) (n e : M) :
    (depthTest j).value ![n, e] = truthValue (M := M)
      ((part j).value ![stats.value ![e] ] ≠ zeroValue M ∧
        leValue M ((part j).value ![stats.value ![e] ]) (succValue M n)) := by
  simp only [depthTest, binary_value, unary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, Program.value_succ,
    multiplication_value, sign_truthValue, leq_truthValue, multiplication_truthValue]

theorem isTerm_value (n e : M) :
    isTerm.value ![n, e] = truthValue (M := M)
      (termDepth e ≠ zeroValue M ∧ leValue M (termDepth e) (succValue M n)) :=
  depthTest_value 0 n e

theorem isForm_value (n e : M) :
    isForm.value ![n, e] = truthValue (M := M)
      (formDepth e ≠ zeroValue M ∧ leValue M (formDepth e) (succValue M n)) :=
  depthTest_value 1 n e

theorem isTerm_closed_iff (t : M) :
    isTerm.value ![zeroValue M, t] = numeralValue M 1 ↔ termDepth t = numeralValue M 1 := by
  rw [isTerm_value, truthValue_eq_one_iff]
  have hone : numeralValue M 1 = succValue M (zeroValue M) := by
    rw [numeral_value_succ, numeral_value_zero]
  constructor
  · rintro ⟨hne, hle⟩
    apply le_antisymm_value
    · rwa [hone]
    · exact one_le_nonzero_model _ hne
  · intro ht
    refine ⟨?_, ?_⟩
    · intro hz
      exact Nat.one_ne_zero ((numeral_eq_zero_iff_model 1).mp (ht.symm.trans hz))
    · rw [ht, hone]
      exact le_refl_value _

@[simp] theorem modelList_nil : modelList ([] : List M) = zeroValue M := rfl
@[simp] theorem modelList_cons (a : M) (xs : List M) :
    modelList (a :: xs) = listCons.value ![a, modelList xs] := rfl

theorem modelNode_ne_zero (k : ℕ) (xs : List M) : modelNode k xs ≠ zeroValue M := by
  rw [modelNode, listCons_value]
  exact successor_ne_zero _

theorem part_zero_value (j : Fin 4) : (part j).value ![zeroValue M] = zeroValue M := by
  have hp : squarePair.value ![zeroValue M, zeroValue M] = zeroValue M := by
    simp only [squarePair_value, zero_mul_value, zero_add_value, ite_self]
  have hl := unpairLeft_pair_value (zeroValue M) (zeroValue M)
  have hr := unpairRight_pair_value (zeroValue M) (zeroValue M)
  rw [hp] at hl hr
  fin_cases j <;> simp only [part, unary_value, hl, hr]

@[fun_prop] theorem termDepth_definable {α : Type} (f : (α → M) → M)
    (hf : (Set.univ : Set M).DefinableFun language f) :
    (Set.univ : Set M).DefinableFun language (fun v => termDepth (f v)) := by
  dsimp only [termDepth]
  fun_prop

@[fun_prop] theorem formDepth_definable {α : Type} (f : (α → M) → M)
    (hf : (Set.univ : Set M).DefinableFun language f) :
    (Set.univ : Set M).DefinableFun language (fun v => formDepth (f v)) := by
  dsimp only [formDepth]
  fun_prop

@[fun_prop] theorem program_four_definable {α : Type} (p : Program 4)
    (f g h k : (α → M) → M)
    (hf : (Set.univ : Set M).DefinableFun language f)
    (hg : (Set.univ : Set M).DefinableFun language g)
    (hh : (Set.univ : Set M).DefinableFun language h)
    (hk : (Set.univ : Set M).DefinableFun language k) :
    (Set.univ : Set M).DefinableFun language (fun v => p.value ![f v, g v, h v, k v]) := by
  apply p.value_definable.comp
  intro j
  fin_cases j
  · exact hf
  · exact hg
  · exact hh
  · exact hk

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.SyntaxPrograms
