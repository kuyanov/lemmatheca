import Lemmatheca.MathematicalLogic.PAFixedSyntaxPrograms
import Lemmatheca.MathematicalLogic.PANativeInstantiation

/-! Concrete Boolean programs for bounded arithmetic formulas. Their bounded
loops are verified by arithmetic-definable PA induction at internal lengths. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.BoundedTruthPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u

def lift {r : ℕ} (p : Program r) : Program (r + 1) :=
  .comp p (fun i => .proj i.castSucc)

def allLoop {r : ℕ} (q : Program (r + 1)) : Program (r + 1) :=
  .prec (constant 1)
    (binary multiplication (.proj (Fin.last (r + 1)))
      (.comp q (Fin.snoc (fun i : Fin r => Program.proj (i.castAdd 2))
        (.proj (Fin.last r).castSucc))))

def boundedAllTest {r : ℕ} (bound : Program r) (q : Program (r + 1)) : Program r :=
  .comp (allLoop q) (Fin.snoc (fun i => .proj i) (unary .succ bound))

def boundedExTest {r : ℕ} (bound : Program r) (q : Program (r + 1)) : Program r :=
  booleanNot (boundedAllTest bound (booleanNot q))

def termValueNamed {α : Type} [Fintype α] {r : ℕ} (name : α → Program r)
    (t : language.Term α) : Program r :=
  .comp (FixedSyntaxPrograms.termValue (t.relabel (Fintype.equivFin α)))
    (fun i => name ((Fintype.equivFin α).symm i))

def extendName {α : Type} {r : ℕ} (name : α → Program r) : α ⊕ Unit → Program (r + 1) :=
  Sum.elim (fun a => lift (name a)) (fun _ => .proj (Fin.last r))

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem lift_value {r : ℕ} (p : Program r) (x : Fin r → M) (a : M) :
    (lift p).value (Fin.snoc x a) = p.value x := by
  rw [lift, Program.value_comp]
  congr 1
  funext i
  rw [Program.value_proj, Fin.snoc_castSucc]

theorem termValueNamed_value {α : Type} [Fintype α] {r : ℕ} (name : α → Program r)
    (t : language.Term α) (x : Fin r → M) :
    (termValueNamed name t).value x = t.realize (fun a => (name a).value x) := by
  rw [termValueNamed, Program.value_comp, FixedSyntaxPrograms.termValue_value, Term.realize_relabel]
  congr 1
  funext a
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

theorem extendName_value {α : Type} {r : ℕ} (name : α → Program r)
    (x : Fin r → M) (a : M) :
    (fun i => (extendName name i).value (Fin.snoc x a)) =
      Sum.elim (fun i => (name i).value x) (fun _ : Unit => a) := by
  funext i
  cases i with
  | inl i => exact lift_value _ _ _
  | inr i =>
    change (Program.proj (Fin.last r)).value (Fin.snoc x a) = a
    rw [Program.value_proj, Fin.snoc_last]

theorem allLoop_zero_value {r : ℕ} (q : Program (r + 1)) (x : Fin r → M) :
    (allLoop q).value (Fin.snoc x (zeroValue M)) = numeralValue M 1 := by
  rw [allLoop, Program.value_rec_zero, constant_value]

theorem allLoop_successor_value {r : ℕ} (q : Program (r + 1)) (x : Fin r → M) (k : M) :
    (allLoop q).value (Fin.snoc x (succValue M k)) =
      mulValue M ((allLoop q).value (Fin.snoc x k)) (q.value (Fin.snoc x k)) := by
  have ht (u : M) :
      (Program.comp q (Fin.snoc (fun i : Fin r => Program.proj (i.castAdd 2))
        (.proj (Fin.last r).castSucc))).value (Fin.snoc (Fin.snoc x k) u) =
        q.value (Fin.snoc x k) := by
    rw [Program.value_comp]
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last, Program.value_proj, Fin.snoc_castSucc]
    · rw [Fin.snoc_castSucc, Program.value_proj, Fin.snoc_castSucc]
      change (Fin.snoc (Fin.snoc x k) u : Fin (r + 2) → M) i.castSucc.castSucc = x i
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
  change (Program.prec _ _).value _ = _
  rw [Program.value_rec_succ, binary_value, multiplication_value, ht,
    Program.value_proj, Fin.snoc_last]
  rfl

theorem allLoop_spec {r : ℕ} (q : Program (r + 1)) (x : Fin r → M)
    (hq : ∀ i : M, BooleanValue (q.value (Fin.snoc x i))) (k : M) :
    BooleanValue ((allLoop q).value (Fin.snoc x k)) ∧
      ((allLoop q).value (Fin.snoc x k) = numeralValue M 1 ↔
        ∀ i : M, leValue M (succValue M i) k → q.value (Fin.snoc x i) = numeralValue M 1) := by
  have hall : ∀ k : M,
      BooleanValue ((allLoop q).value (Fin.snoc x k)) ∧
      (((allLoop q).value (Fin.snoc x k) = numeralValue M 1 →
        ∀ i : M, leValue M (succValue M i) k → q.value (Fin.snoc x i) = numeralValue M 1) ∧
      ((∀ i : M, leValue M (succValue M i) k → q.value (Fin.snoc x i) = numeralValue M 1) →
        (allLoop q).value (Fin.snoc x k) = numeralValue M 1)) := by
    apply definable_induction
    · change DPred (fun v : Fin 1 → M =>
        BooleanValue ((allLoop q).value (Fin.snoc x (v 0))) ∧
        (((allLoop q).value (Fin.snoc x (v 0)) = numeralValue M 1 →
          ∀ i : M, leValue M (succValue M i) (v 0) → q.value (Fin.snoc x i) = numeralValue M 1) ∧
        ((∀ i : M, leValue M (succValue M i) (v 0) → q.value (Fin.snoc x i) = numeralValue M 1) →
          (allLoop q).value (Fin.snoc x (v 0)) = numeralValue M 1)))
      unfold BooleanValue
      pa_definable
    · rw [allLoop_zero_value]
      refine ⟨Or.inr rfl, ?_, fun _ => rfl⟩
      intro _ i hi
      exact False.elim (((successor_le_iff_lt i _).mp hi).2 (zero_le_value i))
    · intro k hk
      rw [allLoop_successor_value]
      refine ⟨multiplication_boolean hk.1 (hq k), ?_, ?_⟩
      · intro hh i hi
        obtain ⟨hprev, hnow⟩ := (mul_eq_one_model _ _).mp hh
        have hik : leValue M i k := (successor_le_successor_value_iff _ _).mp hi
        by_cases hieq : i = k
        · exact hieq ▸ hnow
        · apply hk.2.1 hprev i
          exact (successor_le_iff_lt i k).mpr
            ⟨hik, fun hki => hieq (le_antisymm_value hik hki)⟩
      · intro hh
        apply (mul_eq_one_model _ _).mpr
        refine ⟨hk.2.2 ?_, hh k (le_refl_value _)⟩
        intro i hi
        exact hh i (le_trans_value hi (le_successor_value k))
  exact ⟨(hall k).1, (hall k).2.1, (hall k).2.2⟩

theorem boundedAllTest_value {r : ℕ} (bound : Program r) (q : Program (r + 1))
    (x : Fin r → M) :
    (boundedAllTest bound q).value x =
      (allLoop q).value (Fin.snoc x (succValue M (bound.value x))) := by
  rw [boundedAllTest, Program.value_comp]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last, unary_value, Program.value_succ, Matrix.cons_val_zero]
  · simp only [Fin.snoc_castSucc, Program.value_proj]

omit [M ⊨ PA] in
theorem boolean_eq_truthValue {a : M} (ha : BooleanValue a) (P : Prop)
    (h : a = numeralValue M 1 ↔ P) : a = truthValue P := by
  by_cases hp : P
  · simpa only [truthValue, hp, ↓reduceIte] using h.mpr hp
  · rcases ha with hz | ho
    · simpa only [truthValue, hp, ↓reduceIte] using hz
    · exact False.elim (hp (h.mp ho))

theorem booleanNot_truthValue {r : ℕ} (p : Program r) (x : Fin r → M) (P : Prop)
    (hp : p.value x = truthValue P) :
    (booleanNot p).value x = truthValue (M := M) (¬P) := by
  rw [booleanNot_value, hp, truthValue_eq_zero_iff]
  rfl

theorem boundedAllTest_spec {r : ℕ} (bound : Program r) (q : Program (r + 1))
    (x : Fin r → M) (hq : ∀ i : M, BooleanValue (q.value (Fin.snoc x i))) :
    (boundedAllTest bound q).value x =
      truthValue (M := M) (∀ i : M, leValue M i (bound.value x) →
        q.value (Fin.snoc x i) = numeralValue M 1) := by
  rw [boundedAllTest_value]
  obtain ⟨hb, hs⟩ := allLoop_spec q x hq (succValue M (bound.value x))
  exact boolean_eq_truthValue hb _ (by
    simpa only [successor_le_successor_value_iff] using hs)

theorem boundedExTest_spec {r : ℕ} (bound : Program r) (q : Program (r + 1))
    (x : Fin r → M) (hq : ∀ i : M, BooleanValue (q.value (Fin.snoc x i))) :
    (boundedExTest bound q).value x =
      truthValue (M := M) (∃ i : M, leValue M i (bound.value x) ∧
        q.value (Fin.snoc x i) = numeralValue M 1) := by
  have hnot (i : M) : (booleanNot q).value (Fin.snoc x i) =
      truthValue (M := M) (q.value (Fin.snoc x i) ≠ numeralValue M 1) := by
    apply booleanNot_truthValue
    exact boolean_eq_truthValue (hq i) _ Iff.rfl
  rw [boundedExTest, booleanNot_value,
    boundedAllTest_spec bound (booleanNot q) x (fun i => hnot i ▸ truthValue_boolean _),
    truthValue_eq_zero_iff]
  simp only [hnot, truthValue_eq_one_iff, not_forall, not_not, exists_prop]
  rfl

end Internal

/-- An actual program together with its correctness in every model of PA. -/
def Correct {α : Type} {r : ℕ} (D : language.Formula α)
    (name : α → Program r) (p : Program r) : Prop :=
  ∀ (M : Type) [language.Structure M] [M ⊨ PA] (x : Fin r → M),
    p.value x = truthValue (M := M) (D.Realize (fun a => (name a).value x))

theorem exists_test {α : Type} {D : language.Formula α} (hD : DeltaZero D) :
    ∀ [Fintype α] (r : ℕ) (name : α → Program r), ∃ p : Program r, Correct D name p := by
  induction hD with
  | falsum =>
    intro _ r name
    refine ⟨constant 0, ?_⟩
    intro M _ _ x
    simp only [constant_value, Formula.realize_bot, truthValue, ↓reduceIte,
      numeral_value_zero]
  | equal s t =>
    intro _ r name
    refine ⟨binary equalTest (termValueNamed name s) (termValueNamed name t), ?_⟩
    intro M _ _ x
    rw [binary_value, equalTest_value, termValueNamed_value, termValueNamed_value]
    change truthValue (M := M) (s.realize _ = t.realize _) = _
    congr 1
    exact propext Formula.realize_equal.symm
  | le s t =>
    intro _ r name
    refine ⟨binary leq (termValueNamed name s) (termValueNamed name t), ?_⟩
    intro M _ _ x
    rw [binary_value, leq_value, termValueNamed_value, termValueNamed_value]
    congr 1
    exact propext (realize_leFormula _ _ _).symm
  | @imp α φ ψ hφ hψ ihφ ihψ =>
    intro _ r name
    obtain ⟨p, hp⟩ := ihφ r name
    obtain ⟨q, hq⟩ := ihψ r name
    refine ⟨binary disjoin (booleanNot p) q, ?_⟩
    intro M _ _ x
    rw [binary_value, booleanNot_truthValue p x _ (hp M x), hq M x,
      disjoin_truthValue]
    congr 1
    simp only [Formula.realize_imp, Classical.or_iff_not_imp_left, not_not]
  | @all α t φ hφ ih =>
    intro _ r name
    obtain ⟨q, hq⟩ := ih (r + 1) (extendName name)
    refine ⟨boundedAllTest (termValueNamed name t) q, ?_⟩
    intro M _ _ x
    rw [boundedAllTest_spec _ q x (fun i => (hq M (Fin.snoc x i)) ▸ truthValue_boolean _),
      termValueNamed_value]
    congr 1
    rw [realize_boundedAll]
    apply propext
    apply forall_congr'
    intro a
    rw [hq M (Fin.snoc x a), truthValue_eq_one_iff, extendName_value]
    rfl
  | @ex α t φ hφ ih =>
    intro _ r name
    obtain ⟨q, hq⟩ := ih (r + 1) (extendName name)
    refine ⟨boundedExTest (termValueNamed name t) q, ?_⟩
    intro M _ _ x
    rw [boundedExTest_spec _ q x (fun i => (hq M (Fin.snoc x i)) ▸ truthValue_boolean _),
      termValueNamed_value]
    congr 1
    rw [realize_boundedEx]
    apply propext
    apply exists_congr
    intro a
    rw [hq M (Fin.snoc x a), truthValue_eq_one_iff, extendName_value]
    rfl

/-- The choice is made from a construction proved correct in all PA models,
not merely from equality of functions on the standard natural numbers. -/
def test {α : Type} [Fintype α] {D : language.Formula α} (hD : DeltaZero D)
    {r : ℕ} (name : α → Program r) : Program r :=
  Classical.choose (exists_test hD r name)

theorem test_correct {α : Type} [Fintype α] {D : language.Formula α}
    (hD : DeltaZero D) {r : ℕ} (name : α → Program r) : Correct D name (test hD name) :=
  Classical.choose_spec (exists_test hD r name)

theorem test_value {α : Type} [Fintype α] {D : language.Formula α}
    (hD : DeltaZero D) {r : ℕ} (name : α → Program r)
    {M : Type} [language.Structure M] [M ⊨ PA] (x : Fin r → M) :
    (test hD name).value x =
      truthValue (M := M) (D.Realize (fun a => (name a).value x)) :=
  test_correct hD name M x

def formulaTest {r : ℕ} (D : language.Formula (Fin r)) (hD : DeltaZero D) : Program r :=
  test hD (fun i => .proj i)

theorem formulaTest_value {r : ℕ} (D : language.Formula (Fin r)) (hD : DeltaZero D)
    {M : Type} [language.Structure M] [M ⊨ PA] (x : Fin r → M) :
    (formulaTest D hD).value x = truthValue (M := M) (D.Realize x) := by
  rw [formulaTest, test_value]
  congr 2
  funext i
  exact Program.value_proj i x

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.BoundedTruthPrograms
