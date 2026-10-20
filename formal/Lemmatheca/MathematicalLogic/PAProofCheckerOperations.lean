import Lemmatheca.MathematicalLogic.PAProofRulePrograms
import Lemmatheca.MathematicalLogic.PANativeSyntaxRecurrences

namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem conjunction_nil_value {n : ℕ} (x : Fin n → M) :
    (conjunction []).value x = numeralValue M 1 := constant_value 1 x

theorem conjunction_cons_value {n : ℕ} (p : Program n) (ps : List (Program n))
    (x : Fin n → M) :
    (conjunction (p :: ps)).value x =
      mulValue M (p.value x) ((conjunction ps).value x) := by
  simp only [conjunction, List.foldr_cons, binary, Program.value_comp_two, multiplication_value]

theorem booleanNot_value {n : ℕ} (p : Program n) (x : Fin n → M) :
    (booleanNot p).value x = if p.value x = zeroValue M then numeralValue M 1 else zeroValue M := by
  simp only [booleanNot, unary, Program.value_comp_one, zeroTest_value]

theorem listAllStep_value (h : Program 2) (p a z : M) :
    (listAllStep h).value ![p, a, z] = mulValue M z (h.value ![p, a]) := by
  simp only [listAllStep, binary, Program.value_comp_two, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, multiplication_value]

theorem listAll_value (h : Program 2) (p c : M) :
    (listAll h).value ![p, c] =
      (paramFold (listAllStep h)).value ![p, c, numeralValue M 1] := by
  simp only [listAll, ternary, Program.value_comp_three, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, constant_value]

theorem listAll_zero_value (h : Program 2) (p : M) :
    (listAll h).value ![p, zeroValue M] = numeralValue M 1 := by
  rw [listAll_value, paramFold_zero_value]

theorem listAll_scaled_value (h : Program 2) (p c z : M) :
    (paramFold (listAllStep h)).value ![p, c, z] =
      mulValue M z ((listAll h).value ![p, c]) := by
  have hall : ∀ c : M, ∀ p z,
      (paramFold (listAllStep h)).value ![p, c, z] =
        mulValue M z ((listAll h).value ![p, c]) := by
    apply definable_strong_induction
    · change DPred (fun v : Fin 1 → M => ∀ p z,
        (paramFold (listAllStep h)).value ![p, v 0, z] =
          mulValue M z ((listAll h).value ![p, v 0]))
      pa_definable
    · intro c ih p z
      by_cases hc : c = zeroValue M
      · subst c
        rw [paramFold_zero_value, listAll_zero_value, numeral_value_succ, numeral_value_zero, mul_one_value]
      · let a := listHead.value ![c]
        let t := listTail.value ![c]
        have ht := ih t (tail_smaller_value c hc)
        have hd : listCons.value ![a, t] = c := cons_head_tail_value c hc
        rw [← hd, paramFold_cons_value, listAllStep_value, listAll_value,
          paramFold_cons_value, listAllStep_value, numeral_value_succ, numeral_value_zero, one_mul_value, ht, ht]
        exact mul_assoc_value _ _ _
  exact hall c p z

theorem listAll_cons_value (h : Program 2) (p a c : M) :
    (listAll h).value ![p, listCons.value ![a, c] ] =
      mulValue M (h.value ![p, a]) ((listAll h).value ![p, c]) := by
  rw [listAll_value, paramFold_cons_value, listAllStep_value, numeral_value_succ, numeral_value_zero, one_mul_value,
    listAll_scaled_value]

theorem listAll_append_value (h : Program 2) (p c d : M) :
    (listAll h).value ![p, listAppend.value ![c, d] ] =
      mulValue M ((listAll h).value ![p, c]) ((listAll h).value ![p, d]) := by
  rw [listAll_value, paramFold_append_value, listAll_scaled_value]
  rw [listAll_scaled_value, numeral_one_mul_model]

theorem mul_eq_one_model (a b : M) :
    mulValue M a b = numeralValue M 1 ↔
      a = numeralValue M 1 ∧ b = numeralValue M 1 := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  constructor
  · intro h
    have hone : numeralValue M 1 ≠ zeroValue M := by
      rw [numeral_value_succ, numeral_value_zero]
      exact successor_ne_zero _
    have ha : a ≠ zeroValue M := by intro ha; rw [ha, zero_mul_value] at h; exact hone h.symm
    have hb : b ≠ zeroValue M := by intro hb; rw [hb, mul_zero_value] at h; exact hone h.symm
    have h1a := one_le_nonzero_model a ha
    have h1b := one_le_nonzero_model b hb
    have hla := mul_le_mul_value h1b a
    have hlb := mul_le_mul_value h1a b
    rw [mul_numeral_one_model, h] at hla
    rw [mul_numeral_one_model, mul_comm_value, h] at hlb
    exact ⟨le_antisymm_value hla h1a, le_antisymm_value hlb h1b⟩
  · rintro ⟨rfl, rfl⟩
    exact numeral_one_mul_model _

theorem conjunction_cons_one_iff {n : ℕ} (p : Program n) (ps : List (Program n))
    (x : Fin n → M) :
    (conjunction (p :: ps)).value x = numeralValue M 1 ↔
      p.value x = numeralValue M 1 ∧ (conjunction ps).value x = numeralValue M 1 := by
  rw [conjunction_cons_value, mul_eq_one_model]

theorem listAll_cons_one_iff (h : Program 2) (p a c : M) :
    (listAll h).value ![p, listCons.value ![a, c] ] = numeralValue M 1 ↔
      h.value ![p, a] = numeralValue M 1 ∧
        (listAll h).value ![p, c] = numeralValue M 1 := by
  rw [listAll_cons_value, mul_eq_one_model]

theorem memberStep_value (p a z : M) :
    memberStep.value ![p, a, z] =
      disjoin.value ![z, truthValue (M := M) (p = a)] := by
  simp only [memberStep, binary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, equalTest_truthValue]

theorem listMember_value (p c : M) :
    listMember.value ![p, c] = (paramFold memberStep).value ![p, c, zeroValue M] := by
  simp only [listMember, ternary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, constant_value, numeral_value_zero]

theorem listMember_zero_value (p : M) :
    listMember.value ![p, zeroValue M] = zeroValue M := by
  rw [listMember_value, paramFold_zero_value]

theorem member_fold_one_value (c p : M) :
    (paramFold memberStep).value ![p, c, numeralValue M 1] = numeralValue M 1 := by
  have hall : ∀ c : M, ∀ p,
      (paramFold memberStep).value ![p, c, numeralValue M 1] = numeralValue M 1 := by
    apply list_code_induction
    · change DPred (fun v : Fin 1 → M => ∀ p,
        (paramFold memberStep).value ![p, v 0, numeralValue M 1] = numeralValue M 1)
      pa_definable
    · intro p
      rw [paramFold_zero_value]
    · intro a c ih p
      rw [paramFold_cons_value, memberStep_value, disjoin_value]
      simp only [numeral_eq_zero_iff_model, Nat.one_ne_zero, false_and, ↓reduceIte]
      exact ih p
  exact hall c p

theorem listMember_cons_value (p a c : M) :
    listMember.value ![p, listCons.value ![a, c] ] =
      if p = a then numeralValue M 1 else listMember.value ![p, c] := by
  rw [listMember_value, paramFold_cons_value, memberStep_value, disjoin_value]
  by_cases hp : p = a
  · simp only [hp, truthValue, ↓reduceIte, numeral_eq_zero_iff_model, Nat.one_ne_zero,
      and_false, ↓reduceIte, member_fold_one_value]
  · simp only [truthValue, hp, ↓reduceIte, and_self, ↓reduceIte]
    exact (listMember_value p c).symm

theorem listMember_boolean (c p : M) :
    listMember.value ![p, c] = zeroValue M ∨
      listMember.value ![p, c] = numeralValue M 1 := by
  have hall : ∀ c : M, ∀ p,
      listMember.value ![p, c] = zeroValue M ∨
        listMember.value ![p, c] = numeralValue M 1 := by
    apply list_code_induction
    · change DPred (fun v : Fin 1 → M => ∀ p,
        listMember.value ![p, v 0] = zeroValue M ∨
          listMember.value ![p, v 0] = numeralValue M 1)
      pa_definable
    · intro p
      exact Or.inl (listMember_zero_value p)
    · intro a c ih p
      rw [listMember_cons_value]
      by_cases hp : p = a
      · simp only [hp, ↓reduceIte, or_true]
      · simpa only [hp, ↓reduceIte] using ih p
  exact hall c p

theorem listMember_append_value (c d p : M) :
    listMember.value ![p, listAppend.value ![c, d] ] =
      if listMember.value ![p, c] = zeroValue M then listMember.value ![p, d]
      else numeralValue M 1 := by
  have hall : ∀ c : M, ∀ d p,
      listMember.value ![p, listAppend.value ![c, d] ] =
        if listMember.value ![p, c] = zeroValue M then listMember.value ![p, d]
        else numeralValue M 1 := by
    apply list_code_induction
    · change DPred (fun v : Fin 1 → M => ∀ d p,
        listMember.value ![p, listAppend.value ![v 0, d] ] =
          if listMember.value ![p, v 0] = zeroValue M then listMember.value ![p, d]
          else numeralValue M 1)
      have he (v : Fin 1 → M) :
          (∀ d p, listMember.value ![p, listAppend.value ![v 0, d] ] =
            if listMember.value ![p, v 0] = zeroValue M then listMember.value ![p, d]
            else numeralValue M 1) ↔
          (∀ d p, (listMember.value ![p, v 0] = zeroValue M →
            listMember.value ![p, listAppend.value ![v 0, d] ] = listMember.value ![p, d]) ∧
            (listMember.value ![p, v 0] ≠ zeroValue M →
            listMember.value ![p, listAppend.value ![v 0, d] ] = numeralValue M 1)) := by
        apply forall_congr'
        intro d
        apply forall_congr'
        intro p
        by_cases hp : listMember.value ![p, v 0] = zeroValue M <;> simp [hp]
      have hd : DPred (fun v : Fin 1 → M => ∀ d p,
          (listMember.value ![p, v 0] = zeroValue M →
            listMember.value ![p, listAppend.value ![v 0, d] ] = listMember.value ![p, d]) ∧
          (listMember.value ![p, v 0] ≠ zeroValue M →
            listMember.value ![p, listAppend.value ![v 0, d] ] = numeralValue M 1)) := by
        pa_definable
      convert hd using 1
      ext v
      exact he v
    · intro d p
      rw [listAppend_zero_value, listMember_zero_value]
      simp only [↓reduceIte]
    · intro a c ih d p
      rw [listAppend_cons_value, listMember_cons_value, listMember_cons_value]
      by_cases hp : p = a
      · simp only [hp, ↓reduceIte, numeral_eq_zero_iff_model, Nat.one_ne_zero]
      · simp only [hp, ↓reduceIte]
        exact ih d p
  exact hall c d p

theorem contextIncluded_value (gamma delta : M) :
    contextIncluded.value ![gamma, delta] =
      (listAll (binary listMember (.proj 1) (.proj 0))).value ![delta, gamma] := by
  simp only [contextIncluded, binary_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one]

theorem contextIncluded_zero_value (delta : M) :
    contextIncluded.value ![zeroValue M, delta] = numeralValue M 1 := by
  rw [contextIncluded_value, listAll_zero_value]

theorem contextIncluded_cons_one_iff (a gamma delta : M) :
    contextIncluded.value ![listCons.value ![a, gamma], delta] = numeralValue M 1 ↔
      listMember.value ![a, delta] = numeralValue M 1 ∧
        contextIncluded.value ![gamma, delta] = numeralValue M 1 := by
  rw [contextIncluded_value, listAll_cons_one_iff]
  simp only [binary_value, Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one,
    contextIncluded_value]

theorem contextIncluded_of_members (gamma delta : M)
    (h : ∀ a : M, listMember.value ![a, gamma] = numeralValue M 1 →
      listMember.value ![a, delta] = numeralValue M 1) :
    contextIncluded.value ![gamma, delta] = numeralValue M 1 := by
  have hall : ∀ gamma : M, ∀ delta,
      (∀ a : M, listMember.value ![a, gamma] = numeralValue M 1 →
        listMember.value ![a, delta] = numeralValue M 1) →
      contextIncluded.value ![gamma, delta] = numeralValue M 1 := by
    apply list_code_induction
    · change DPred (fun v : Fin 1 → M => ∀ delta,
        (∀ a : M, listMember.value ![a, v 0] = numeralValue M 1 →
          listMember.value ![a, delta] = numeralValue M 1) →
        contextIncluded.value ![v 0, delta] = numeralValue M 1)
      pa_definable
    · intro delta _
      exact contextIncluded_zero_value delta
    · intro a gamma ih delta hmem
      rw [contextIncluded_cons_one_iff]
      constructor
      · apply hmem a
        rw [listMember_cons_value]
        simp only [↓reduceIte]
      · apply ih delta
        intro b hb
        apply hmem b
        rw [listMember_cons_value]
        by_cases he : b = a <;> simp only [he, ↓reduceIte, hb]
  exact hall gamma delta h

theorem contextIncluded_members (gamma delta : M)
    (h : contextIncluded.value ![gamma, delta] = numeralValue M 1) :
    ∀ a : M, listMember.value ![a, gamma] = numeralValue M 1 →
      listMember.value ![a, delta] = numeralValue M 1 := by
  have hall : ∀ gamma : M, ∀ delta,
      contextIncluded.value ![gamma, delta] = numeralValue M 1 →
      ∀ a : M, listMember.value ![a, gamma] = numeralValue M 1 →
        listMember.value ![a, delta] = numeralValue M 1 := by
    apply list_code_induction
    · change DPred (fun v : Fin 1 → M => ∀ delta,
        contextIncluded.value ![v 0, delta] = numeralValue M 1 →
        ∀ a : M, listMember.value ![a, v 0] = numeralValue M 1 →
          listMember.value ![a, delta] = numeralValue M 1)
      pa_definable
    · intro delta _ a ha
      rw [listMember_zero_value] at ha
      have hz : (1 : ℕ) = 0 := (zero_eq_numeral_iff_model 1).mp ha
      exact False.elim (Nat.one_ne_zero hz)
    · intro b gamma ih delta hinc a ha
      obtain ⟨hb, htail⟩ := (contextIncluded_cons_one_iff b gamma delta).mp hinc
      rw [listMember_cons_value] at ha
      by_cases he : a = b
      · exact he.symm ▸ hb
      · simp only [he, ↓reduceIte] at ha
        exact ih delta htail a ha
  exact hall gamma delta h

theorem contextIncluded_refl_value (gamma : M) :
    contextIncluded.value ![gamma, gamma] = numeralValue M 1 :=
  contextIncluded_of_members gamma gamma (fun _ h => h)

theorem contextIncluded_trans_value (gamma delta theta : M)
    (hg : contextIncluded.value ![gamma, delta] = numeralValue M 1)
    (hd : contextIncluded.value ![delta, theta] = numeralValue M 1) :
    contextIncluded.value ![gamma, theta] = numeralValue M 1 :=
  contextIncluded_of_members gamma theta (fun a ha =>
    contextIncluded_members delta theta hd a (contextIncluded_members gamma delta hg a ha))

theorem contextIncluded_append_left_value (gamma delta : M) :
    contextIncluded.value ![gamma, listAppend.value ![gamma, delta] ] = numeralValue M 1 := by
  apply contextIncluded_of_members
  intro a ha
  rw [listMember_append_value, ha]
  simp only [numeral_eq_zero_iff_model, Nat.one_ne_zero, ↓reduceIte]

theorem contextIncluded_append_right_value (gamma delta : M) :
    contextIncluded.value ![delta, listAppend.value ![gamma, delta] ] = numeralValue M 1 := by
  apply contextIncluded_of_members
  intro a ha
  rw [listMember_append_value, ha]
  split_ifs <;> rfl

theorem certified_iff (E : Program 2) (p a : M) :
    Certified E p a ↔
      listLength.value ![p] = numeralValue M 2 ∧
      derivationCheck.value ![rootValue p] = numeralValue M 1 ∧
      conclusionValue (rootValue p) = a ∧
      isSentence.value ![a] = numeralValue M 1 ∧
      listLength.value ![contextValue (rootValue p)] = listLength.value ![witnessesValue p] ∧
      (axiomScan E).value ![contextValue (rootValue p), witnessesValue p,
        listLength.value ![contextValue (rootValue p)] ] = numeralValue M 1 := by
  simp only [Certified, certificateCheck, conjunction_cons_one_iff, conjunction_nil_value,
    binary_value, unary_value, ternary_value, Program.value_proj, constant_value,
    Matrix.cons_val_zero, Matrix.cons_val_one, equalTest_value,
    numeral_value_zero, rootValue, contextValue, witnessesValue, conclusionValue,
    and_true]
  have hzero : zeroValue M ≠ numeralValue M 1 := by
    rw [numeral_value_succ, numeral_value_zero]
    exact (successor_ne_zero _).symm
  simp only [ite_eq_left_iff, hzero, imp_false, not_not]

theorem modusPonensRecord_value (d e b : M) :
    modusPonensRecord.value ![d, e, b] =
      listCons.value ![numeralValue M 108,
        listCons.value ![listAppend.value ![(argument 0).value ![d], (argument 0).value ![e] ],
          listCons.value ![b, listCons.value ![d, listCons.value ![e, zeroValue M] ] ] ] ] := by
  simp only [modusPonensRecord, syntaxNode_value, list_cons_value, list_nil_value,
    binary, unary, Program.value_comp_two, Program.value_comp_one,
    Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]

end Internal
end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
