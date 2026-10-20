import Lemmatheca.MathematicalLogic.PABoundedTruthPrograms

/-! An explicit bounded witness selector, verified at internal PA bounds. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.BoundedTruthPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u

def witnessStep {r : ℕ} (q : Program (r + 1)) : Program (r + 2) :=
  ternary select
    (.comp q (Fin.snoc (fun i : Fin r => Program.proj (i.castAdd 2))
      (.proj (Fin.last r).castSucc)))
    (.proj (Fin.last r).castSucc) (.proj (Fin.last (r + 1)))

def witnessLoop {r : ℕ} (q : Program (r + 1)) : Program (r + 1) :=
  .prec (constant 0) (witnessStep q)

def boundedWitness {r : ℕ} (q : Program (r + 1)) : Program (r + 1) :=
  .comp (witnessLoop q)
    (Fin.snoc (fun i => .proj i.castSucc) (unary .succ (.proj (Fin.last r))))

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]
local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem witnessStep_value {r : ℕ} (q : Program (r + 1)) (x : Fin r → M) (k prev : M) :
    (witnessStep q).value (Fin.snoc (Fin.snoc x k) prev) =
      if q.value (Fin.snoc x k) = zeroValue M then prev else k := by
  have ht :
      (Program.comp q (Fin.snoc (fun i : Fin r => Program.proj (i.castAdd 2))
        (.proj (Fin.last r).castSucc))).value (Fin.snoc (Fin.snoc x k) prev) =
        q.value (Fin.snoc x k) := by
    rw [Program.value_comp]
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last, Program.value_proj, Fin.snoc_castSucc]
    · rw [Fin.snoc_castSucc, Program.value_proj, Fin.snoc_castSucc]
      change (Fin.snoc (Fin.snoc x k) prev : Fin (r + 2) → M) i.castSucc.castSucc = x i
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
  rw [witnessStep, ternary_value, ht, Program.value_proj, Fin.snoc_castSucc,
    Fin.snoc_last, Program.value_proj, Fin.snoc_last, select_value]

theorem witnessLoop_zero_value {r : ℕ} (q : Program (r + 1)) (x : Fin r → M) :
    (witnessLoop q).value (Fin.snoc x (zeroValue M)) = zeroValue M := by
  rw [witnessLoop, Program.value_rec_zero, constant_value, numeral_value_zero]

theorem witnessLoop_successor_value {r : ℕ} (q : Program (r + 1)) (x : Fin r → M) (k : M) :
    (witnessLoop q).value (Fin.snoc x (succValue M k)) =
      if q.value (Fin.snoc x k) = zeroValue M then
        (witnessLoop q).value (Fin.snoc x k) else k := by
  change (Program.prec _ _).value _ = _
  rw [Program.value_rec_succ, witnessStep_value]
  rfl

theorem witnessLoop_spec {r : ℕ} (q : Program (r + 1)) (x : Fin r → M)
    (hq : ∀ i : M, BooleanValue (q.value (Fin.snoc x i))) (k : M) :
    (∃ i : M, leValue M (succValue M i) k ∧ q.value (Fin.snoc x i) = numeralValue M 1) →
      q.value (Fin.snoc x ((witnessLoop q).value (Fin.snoc x k))) = numeralValue M 1 ∧
        leValue M (succValue M ((witnessLoop q).value (Fin.snoc x k))) k := by
  apply definable_induction
    (fun k => (∃ i : M, leValue M (succValue M i) k ∧
      q.value (Fin.snoc x i) = numeralValue M 1) →
      q.value (Fin.snoc x ((witnessLoop q).value (Fin.snoc x k))) = numeralValue M 1 ∧
        leValue M (succValue M ((witnessLoop q).value (Fin.snoc x k))) k)
  · change DPred (fun v : Fin 1 → M =>
      (∃ i : M, leValue M (succValue M i) (v 0) ∧
        q.value (Fin.snoc x i) = numeralValue M 1) →
      q.value (Fin.snoc x ((witnessLoop q).value (Fin.snoc x (v 0)))) = numeralValue M 1 ∧
        leValue M (succValue M ((witnessLoop q).value (Fin.snoc x (v 0)))) (v 0))
    pa_definable
  · rintro ⟨i, hi, _⟩
    exact False.elim (((successor_le_iff_lt i _).mp hi).2 (zero_le_value i))
  · intro j ih hex
    rw [witnessLoop_successor_value]
    by_cases hj : q.value (Fin.snoc x j) = zeroValue M
    · rw [ite_eq_left hj]
      have hprev : ∃ i : M, leValue M (succValue M i) j ∧
          q.value (Fin.snoc x i) = numeralValue M 1 := by
        obtain ⟨i, hi, hqi⟩ := hex
        have hij : leValue M i j := (successor_le_successor_value_iff _ _).mp hi
        have hne : i ≠ j := by
          intro he
          subst i
          rw [hj] at hqi
          exact (by decide : (1 : ℕ) ≠ 0) ((zero_eq_numeral_iff_model 1).mp hqi)
        exact ⟨i, (successor_le_iff_lt _ _).mpr
          ⟨hij, fun hji => hne (le_antisymm_value hij hji)⟩, hqi⟩
      have hh := ih hprev
      exact ⟨hh.1, le_trans_value hh.2 (le_successor_value j)⟩
    · rw [ite_eq_right hj]
      exact ⟨boolean_ne_one (hq j) hj, le_refl_value _⟩

theorem boundedWitness_value {r : ℕ} (q : Program (r + 1)) (x : Fin r → M) (n : M) :
    (boundedWitness q).value (Fin.snoc x n) =
      (witnessLoop q).value (Fin.snoc x (succValue M n)) := by
  rw [boundedWitness, Program.value_comp]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, unary_value, Program.value_succ, Matrix.cons_val_zero, Program.value_proj]
  · simp only [Fin.snoc_castSucc, Program.value_proj]

theorem boundedWitness_spec {r : ℕ} (q : Program (r + 1)) (x : Fin r → M)
    (hq : ∀ i : M, BooleanValue (q.value (Fin.snoc x i))) (n : M)
    (hex : ∃ i : M, leValue M i n ∧ q.value (Fin.snoc x i) = numeralValue M 1) :
    q.value (Fin.snoc x ((boundedWitness q).value (Fin.snoc x n))) = numeralValue M 1 ∧
      leValue M ((boundedWitness q).value (Fin.snoc x n)) n := by
  rw [boundedWitness_value]
  obtain ⟨i, hi, hqi⟩ := hex
  have h := witnessLoop_spec q x hq (succValue M n)
    ⟨i, (successor_le_successor_value_iff _ _).mpr hi, hqi⟩
  exact ⟨h.1, (successor_le_successor_value_iff _ _).mp h.2⟩

end Internal
end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.BoundedTruthPrograms
