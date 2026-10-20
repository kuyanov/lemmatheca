import Lemmatheca.MathematicalLogic.PAProofPrograms

/-! Internally verified tests and bounded searches for the exact syntax-code
programs. All inductions range over arithmetic-definable predicates. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance : DecidableEq M := Classical.decEq M
local instance (P : Prop) : Decidable P := Classical.propDecidable P

omit [language.Structure M] [M ⊨ PA] in
private theorem snocFin0 (a : M) : Fin.snoc (Fin.elim0 : Fin 0 → M) a = ![a] := by
  funext i
  fin_cases i
  rfl

theorem sign_zero_value : sign.value ![zeroValue M] = zeroValue M := by
  have h := Program.value_rec_zero Program.zero (constant 1 : Program 2)
    (Fin.elim0 : Fin 0 → M)
  simpa only [sign, snocFin0, Program.value_zero] using h

theorem sign_successor_value (a : M) : sign.value ![succValue M a] = numeralValue M 1 := by
  have h := Program.value_rec_succ Program.zero (constant 1 : Program 2)
    (Fin.elim0 : Fin 0 → M) a
  simpa only [sign, snocFin0, constant_value] using h

theorem zeroTest_zero_value : zeroTest.value ![zeroValue M] = numeralValue M 1 := by
  have h := Program.value_rec_zero (constant 1 : Program 0) (constant 0 : Program 2)
    (Fin.elim0 : Fin 0 → M)
  simpa only [zeroTest, snocFin0, constant_value] using h

theorem zeroTest_successor_value (a : M) : zeroTest.value ![succValue M a] = zeroValue M := by
  have h := Program.value_rec_succ (constant 1 : Program 0) (constant 0 : Program 2)
    (Fin.elim0 : Fin 0 → M) a
  simpa only [zeroTest, snocFin0, constant_value, numeral_value_zero] using h

theorem sign_value (a : M) :
    sign.value ![a] = if a = zeroValue M then zeroValue M else numeralValue M 1 := by
  by_cases ha : a = zeroValue M
  · simpa only [ha, ↓reduceIte] using (sign_zero_value (M := M))
  · obtain ⟨b, rfl⟩ := PAComputations.predecessor a ha
    rw [sign_successor_value, ite_eq_right (successor_ne_zero b)]

theorem zeroTest_value (a : M) :
    zeroTest.value ![a] = if a = zeroValue M then numeralValue M 1 else zeroValue M := by
  by_cases ha : a = zeroValue M
  · simpa only [ha, ↓reduceIte] using (zeroTest_zero_value (M := M))
  · obtain ⟨b, rfl⟩ := PAComputations.predecessor a ha
    rw [zeroTest_successor_value, ite_eq_right (successor_ne_zero b)]

theorem select_value (b x y : M) :
    select.value ![b, x, y] = if b = zeroValue M then y else x := by
  simp only [select, Program.value_comp_two, Program.value_comp_one,
    Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, multiplication_value, addition_value,
    sign_value, zeroTest_value]

  split_ifs <;>
    simp [numeral_value_zero, numeral_value_succ, zero_mul_value, one_mul_value,
      zero_add_value, add_zero_value]

@[fun_prop] theorem program_unary_definable {α : Type} (p : Program 1)
    (f : (α → M) → M)
    (hf : (Set.univ : Set M).DefinableFun language f) :
    (Set.univ : Set M).DefinableFun language (fun x => p.value ![f x]) := by
  apply p.value_definable.comp
  intro i
  fin_cases i
  exact hf

@[fun_prop] theorem program_pair_definable {α : Type} (p : Program 2)
    (f g : (α → M) → M)
    (hf : (Set.univ : Set M).DefinableFun language f)
    (hg : (Set.univ : Set M).DefinableFun language g) :
    (Set.univ : Set M).DefinableFun language (fun x => p.value ![f x, g x]) := by
  apply p.value_definable.comp
  intro i
  fin_cases i
  · exact hf
  · exact hg

theorem subtraction_zero_value (a : M) : subtraction.value ![a, zeroValue M] = a := by
  have h := Program.value_rec_zero (Program.proj (0 : Fin 1))
    (Program.comp predecessor ![Program.proj (2 : Fin 3)]) ![a]
  have hv : Fin.snoc (![a] : Fin 1 → M) (zeroValue M) = ![a, zeroValue M] := by
    funext i
    fin_cases i <;> rfl
  simpa only [subtraction, hv, Program.value_proj, Matrix.cons_val_zero] using h

theorem subtraction_successor_value (a b : M) :
    subtraction.value ![a, succValue M b] = predecessor.value ![subtraction.value ![a, b] ] := by
  have h := Program.value_rec_succ (Program.proj (0 : Fin 1))
    (Program.comp predecessor ![Program.proj (2 : Fin 3)]) ![a] b
  have hv (c : M) : Fin.snoc (![a] : Fin 1 → M) c = ![a, c] := by
    funext i
    fin_cases i <;> rfl
  simp only [hv, Program.value_comp_one, Program.value_proj] at h
  simpa [subtraction, Fin.snoc] using h

theorem subtraction_spec (a b : M) :
    (leValue M b a → addValue M (subtraction.value ![a, b]) b = a) ∧
      (leValue M a b → subtraction.value ![a, b] = zeroValue M) := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have hi : ∀ b : M,
      (b ≤ a → subtraction.value ![a, b] + b = a) ∧
        (a ≤ b → subtraction.value ![a, b] = 0) := by
    apply definable_induction
    · change DPred (fun v : Fin 1 → M =>
        (leValue M (v 0) a → addValue M (subtraction.value ![a, v 0]) (v 0) = a) ∧
          (leValue M a (v 0) → subtraction.value ![a, v 0] = zeroValue M))
      pa_definable
    · rw [subtraction_zero_value]
      change (zeroValue M ≤ a → addValue M a (zeroValue M) = a) ∧
        (a ≤ zeroValue M → a = zeroValue M)
      rw [add_zero_value]
      exact ⟨fun _ => rfl, fun ha => le_antisymm ha (zero_le_value a)⟩
    · intro k hk
      rw [subtraction_successor_value]
      constructor
      · intro hka
        have hka' : k ≤ a := le_trans (le_successor_value k) hka
        have hu := hk.1 hka'
        have hne : subtraction.value ![a, k] ≠ 0 := by
          intro hz
          have ha : a = k := by simpa only [hz, zero_add] using hu.symm
          have hl : k < k := (successor_le_iff_lt k k).mp (ha ▸ hka)
          exact (lt_irrefl k) hl
        obtain ⟨v, hv⟩ := PAComputations.predecessor (subtraction.value ![a, k]) hne
        rw [hv, predecessor_successor]
        calc
          v + succValue M k = succValue M (v + k) := add_successor_value v k
          _ = succValue M v + k := (successor_add_value v k).symm
          _ = a := by rw [← hv]; exact hu
      · intro hak
        by_cases hak' : a ≤ k
        · rw [hk.2 hak']
          exact predecessor_zero
        · have hka : succValue M k ≤ a :=
            (successor_le_iff_lt k a).mpr (lt_of_not_ge hak')
          have ha : a = succValue M k := le_antisymm hak hka
          have hu := hk.1 (le_trans (le_successor_value k) hka)
          have hv : subtraction.value ![a, k] = succValue M (zeroValue M) := by
            apply add_right_cancel_value k
            calc
              subtraction.value ![a, k] + k = a := hu
              _ = succValue M k := ha
              _ = succValue M (zeroValue M) + k :=
                ((successor_add_value (zeroValue M) k).trans
                  (congrArg (succValue M) (zero_add_value k))).symm
          rw [hv, predecessor_successor]
          rfl
  exact hi b

theorem subtraction_zero_iff (a b : M) :
    subtraction.value ![a, b] = zeroValue M ↔ leValue M a b := by
  let := modelSemiring M
  let := modelLinearOrder M
  constructor
  · intro hz
    by_contra hn
    have hba : b ≤ a := le_of_lt (lt_of_not_ge hn)
    have he := (subtraction_spec a b).1 hba
    rw [hz, zero_add_value] at he
    exact hn (he ▸ le_refl b)
  · exact (subtraction_spec a b).2

theorem less_value (a b : M) :
    less.value ![a, b] = if leValue M (succValue M a) b then numeralValue M 1 else zeroValue M := by
  let := modelSemiring M
  let := modelLinearOrder M
  simp only [less, Program.value_comp_one, Program.value_comp_two, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, sign_value]
  by_cases h : a < b
  · have hz : subtraction.value ![b, a] ≠ zeroValue M :=
      fun hh => (not_le.mpr h) ((subtraction_zero_iff b a).mp hh)
    simp only [hz, (successor_le_iff_lt a b).mpr h, ↓reduceIte]
  · have hz := (subtraction_zero_iff b a).mpr (le_of_not_gt h)
    have hn : ¬ leValue M (succValue M a) b :=
      fun hh => h ((successor_le_iff_lt a b).mp hh)
    simp only [hz, hn, ↓reduceIte]


end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms
