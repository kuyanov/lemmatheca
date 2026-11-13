import Lemmatheca.IntuitionisticPropositionalFiniteModelProperty.Subformulas
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin

namespace Lemmatheca.ProofTheory.Intuitionistic.FiniteModels

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u

abbrev RelationCode (n : ℕ) := Fin n → Fin n → Bool
abbrev ValuationCode (n : ℕ) (S : Finset ℕ) := Fin n → S → Bool

/-- Every atom outside the supplied finite support has the specified false value. -/
def extendedValuation {n : ℕ} {S : Finset ℕ} (v : ValuationCode n S)
    (i : Fin n) (p : ℕ) : Bool :=
  if hp : p ∈ S then v i ⟨p, hp⟩ else false

/-- Exactly the three finite tests in the human candidate model definition. -/
def Admissible {n : ℕ} {S : Finset ℕ} (r : RelationCode n) (v : ValuationCode n S) : Prop :=
  (∀ i, r i i = true) ∧
  (∀ i j k, r i j = true → r j k = true → r i k = true) ∧
  (∀ i j p, r i j = true → v i p = true → v j p = true)

instance admissibleDecidable {n : ℕ} {S : Finset ℕ}
    (r : RelationCode n) (v : ValuationCode n S) : Decidable (Admissible r v) := by
  unfold Admissible
  infer_instance

def admissible {n : ℕ} {S : Finset ℕ} (r : RelationCode n) (v : ValuationCode n S) : Bool :=
  decide (Admissible r v)

/-- The candidate's actual relation, with preorder evidence from its finite test. -/
abbrev codePreorder {n : ℕ} {S : Finset ℕ} (r : RelationCode n) (v : ValuationCode n S)
    (h : Admissible r v) : Preorder (Fin n) where
  le i j := r i j = true
  lt i j := r i j = true ∧ ¬ r j i = true
  le_refl := h.1
  le_trans := h.2.1

def codeModel {n : ℕ} {S : Finset ℕ} (r : RelationCode n) (v : ValuationCode n S)
    (hn : 0 < n) (h : Admissible r v) : @Kripke.Model ℕ (Fin n) (codePreorder r v h) := by
  letI : Preorder (Fin n) := codePreorder r v h
  exact {
  world_nonempty := ⟨⟨0, hn⟩⟩
  valuation i p := extendedValuation v i p = true
  persistent {i j} hij p hp := by
    by_cases hS : p ∈ S
    · simp only [extendedValuation, dite_eq_left hS] at hp ⊢
      exact h.2.2 i j ⟨p, hS⟩ hij hp
    · simp only [extendedValuation, dite_eq_right hS] at hp
      exact Bool.noConfusion hp
  }

/-- Structural native-formula recursion with computable finite future-world loops. -/
def booleanForcing {n : ℕ} {S : Finset ℕ} (r : RelationCode n) (v : ValuationCode n S) :
    Formula → Fin n → Bool
  | .atom p, i => extendedValuation v i p
  | .falsum, _ => false
  | .neg A, i => decide (∀ j, r i j = true → booleanForcing r v A j = false)
  | .conj A B, i => booleanForcing r v A i && booleanForcing r v B i
  | .disj A B, i => booleanForcing r v A i || booleanForcing r v B i
  | .impl A B, i => decide (∀ j, r i j = true →
      booleanForcing r v A j = true → booleanForcing r v B j = true)

theorem booleanForcing_correct {n : ℕ} {S : Finset ℕ}
    (r : RelationCode n) (v : ValuationCode n S) (hn : 0 < n) (h : Admissible r v)
    (A : Formula) (i : Fin n) :
    booleanForcing r v A i = true ↔
      @Kripke.Forces ℕ (Fin n) (codePreorder r v h) (codeModel r v hn h) i A := by
  induction A generalizing i with
  | atom p => rfl
  | falsum => simp [booleanForcing, Kripke.Forces]
  | neg A ih =>
      simp only [booleanForcing, decide_eq_true_eq, Kripke.Forces]
      constructor
      · intro hf j hij hj
        have hf' := hf j hij
        have ht := (ih j).mpr hj
        have hh : false = true := hf'.symm.trans ht
        cases hh
      · intro hf j hij
        cases hb : booleanForcing r v A j with
        | false => rfl
        | true => exact (hf j hij ((ih j).mp hb)).elim
  | conj A B ihA ihB =>
      exact Bool.and_eq_true_iff.trans (and_congr (ihA i) (ihB i))
  | disj A B ihA ihB =>
      exact Bool.or_eq_true_iff.trans (or_congr (ihA i) (ihB i))
  | impl A B ihA ihB =>
      simp only [booleanForcing, decide_eq_true_eq, Kripke.Forces]
      constructor
      · intro hf j hij hj
        exact (ihB j).mp (hf j hij ((ihA j).mpr hj))
      · intro hf j hij hj
        exact (ihB j).mpr (hf j hij ((ihA j).mp hj))

/-- A mathematical presentation of a given finite model; not part of the executable scan. -/
noncomputable def presentRelation {W : Type u} [Preorder W] {n : ℕ} (b : Fin n ≃ W) :
    RelationCode n := fun i j => by classical exact decide (b i ≤ b j)

noncomputable def presentValuation {W : Type u} [Preorder W] {n : ℕ}
    (M : Kripke.Model ℕ W) (b : Fin n ≃ W) (S : Finset ℕ) : ValuationCode n S :=
  fun i p => by classical exact decide (M.valuation (b i) p.val)

theorem presentation_admissible {W : Type u} [Preorder W] {n : ℕ}
    (M : Kripke.Model ℕ W) (b : Fin n ≃ W) (S : Finset ℕ) :
    Admissible (presentRelation b) (presentValuation M b S) := by
  classical
  simp only [Admissible, presentRelation, presentValuation, decide_eq_true_eq]
  exact ⟨fun i => le_refl (b i), fun _ _ _ hij hjk => le_trans hij hjk,
    fun i j p hij hp => M.persistent hij p.val hp⟩

theorem presentation_forcing {W : Type u} [Preorder W] {n : ℕ}
    (M : Kripke.Model ℕ W) (b : Fin n ≃ W) (S : Finset ℕ)
    (A : Formula) (hA : atoms A ⊆ S) (i : Fin n) :
    booleanForcing (presentRelation b) (presentValuation M b S) A i = true ↔
      Kripke.Forces M (b i) A := by
  classical
  revert hA i
  induction A with
  | atom p =>
      intro hp i
      have hmem : p ∈ S := hp (by simp [atoms])
      simp [booleanForcing, extendedValuation, hmem, presentValuation, Kripke.Forces]
  | falsum =>
      intro _ i
      simp [booleanForcing, Kripke.Forces]
  | neg A ih =>
      intro hA i
      simp only [booleanForcing, decide_eq_true_eq, Kripke.Forces]
      constructor
      · intro hf z hiz hz
        obtain ⟨j, rfl⟩ := b.surjective z
        have hrel : presentRelation b i j = true := by
          simpa [presentRelation] using hiz
        have hf' := hf j hrel
        have ht := (ih hA j).mpr hz
        have hh : false = true := hf'.symm.trans ht
        cases hh
      · intro hf j hij
        have hrel : b i ≤ b j := by simpa [presentRelation] using hij
        cases hb : booleanForcing (presentRelation b) (presentValuation M b S) A j with
        | false => rfl
        | true => exact (hf (b j) hrel ((ih hA j).mp hb)).elim
  | conj A B ihA ihB =>
      intro hAB i
      have ha : atoms A ⊆ S := fun p hp => hAB (Finset.mem_union_left _ hp)
      have hb : atoms B ⊆ S := fun p hp => hAB (Finset.mem_union_right _ hp)
      exact Bool.and_eq_true_iff.trans (and_congr (ihA ha i) (ihB hb i))
  | disj A B ihA ihB =>
      intro hAB i
      have ha : atoms A ⊆ S := fun p hp => hAB (Finset.mem_union_left _ hp)
      have hb : atoms B ⊆ S := fun p hp => hAB (Finset.mem_union_right _ hp)
      exact Bool.or_eq_true_iff.trans (or_congr (ihA ha i) (ihB hb i))
  | impl A B ihA ihB =>
      intro hAB i
      have ha : atoms A ⊆ S := fun p hp => hAB (Finset.mem_union_left _ hp)
      have hb : atoms B ⊆ S := fun p hp => hAB (Finset.mem_union_right _ hp)
      simp only [booleanForcing, decide_eq_true_eq, Kripke.Forces]
      constructor
      · intro hf z hiz hz
        obtain ⟨j, rfl⟩ := b.surjective z
        have hrel : presentRelation b i j = true := by
          simpa [presentRelation] using hiz
        exact (ihB hb j).mp (hf j hrel ((ihA ha j).mpr hz))
      · intro hf j hij hj
        have hrel : b i ≤ b j := by simpa [presentRelation] using hij
        exact (ihB hb j).mpr (hf (b j) hrel ((ihA ha j).mp hj))

theorem relation_code_card (n : ℕ) : Fintype.card (RelationCode n) = 2 ^ (n * n) := by
  simp [RelationCode, Nat.pow_mul]

theorem valuation_code_card (n : ℕ) (S : Finset ℕ) :
    Fintype.card (ValuationCode n S) = 2 ^ (n * S.card) := by
  calc
    Fintype.card (ValuationCode n S) = (2 ^ S.card) ^ n := by simp [ValuationCode]
    _ = 2 ^ (n * S.card) := by rw [← Nat.pow_mul, Nat.mul_comm]

end Lemmatheca.ProofTheory.Intuitionistic.FiniteModels
