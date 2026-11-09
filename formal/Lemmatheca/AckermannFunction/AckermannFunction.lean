import Mathlib.Computability.Ackermann
import Lemmatheca.UniversalComputation.UniversalComputation
import Lemmatheca.MachinesAndComputationHistories.MachinesAndComputationHistories

/-! The Ackermann rows, their shared numerical program indices, and the
finite-arity representation bridges used by the human entry. The function,
row-program compiler, and the principal growth theorem are reused directly
from mathlib rather than redefined here. -/

namespace Lemmatheca.ComputabilityTheory.AckermannFunction

open Encodable
open Nat.Partrec (Code)
open PartialRecursiveFunctions

theorem ack_unique (f : ℕ → ℕ → ℕ)
    (hzero : ∀ n, f 0 n = n + 1)
    (hsucc_zero : ∀ m, f (m + 1) 0 = f m 1)
    (hsucc_succ : ∀ m n, f (m + 1) (n + 1) = f m (f (m + 1) n)) :
    f = ack := by
  funext m n
  induction m generalizing n with
  | zero => simpa only [ack_zero] using hzero n
  | succ m ih =>
    induction n with
    | zero => simpa only [hsucc_zero, ack_succ_zero] using ih 1
    | succ n hn => rw [hsucc_succ, ih, hn, ack_succ_succ]

theorem row_primitive (m : ℕ) : Nat.Primrec (ack m) := by
  induction m with
  | zero => exact Nat.Primrec.succ.of_eq (fun n => (ack_zero n).symm)
  | succ m ih =>
    apply (Nat.Primrec.prec1 (ack m 1) (ih.comp Nat.Primrec.right)).of_eq
    intro n
    induction n with
    | zero => exact (ack_succ_zero m).symm
    | succ n hn => simpa only [Nat.unpair_pair, ack_succ_succ] using congrArg (ack m) hn

theorem recursion_bound (f g : ℕ → ℕ) (a b : ℕ)
    (hf : ∀ x, f x < ack a x) (hg : ∀ x, g x < ack b x) (s t : ℕ) :
    Nat.rec (f s) (fun y z => g (Nat.pair s (Nat.pair y z))) t <
      ack (max a b + 9) (s + t) := by
  induction t with
  | zero =>
    exact (hf s).trans_le (ack_mono_left s (by omega))
  | succ t ih =>
    simp only
    apply (hg _).trans ((ack_pair_lt _ _ _).trans_le _)
    rcases lt_or_ge _ s with h₁ | h₁
    · rw [max_eq_left h₁.le]
      gcongr <;> omega
    rw [max_eq_right h₁]
    apply (ack_pair_lt _ _ _).le.trans
    rcases lt_or_ge _ t with h₂ | h₂
    · rw [max_eq_left h₂.le, Nat.add_assoc]
      exact ack_le_ack (Nat.add_le_add (le_max_right a b) (by simp))
        ((Nat.le_succ t).trans (Nat.le_add_left _ _))
    rw [max_eq_right h₂]
    apply (ack_strictMono_right _ ih).le.trans
    rw [Nat.add_succ s, Nat.add_succ _ 8, Nat.succ_eq_add_one, Nat.succ_eq_add_one,
      ack_succ_succ (_ + 8), Nat.add_assoc]
    exact ack_mono_left _ (Nat.add_le_add (le_max_right a b) le_rfl)

/-- The program index is taken in the corpus's fixed `Code` numbering. -/
def rowIndex (m : ℕ) : ℕ := encode (Code.pappAck m)

theorem rowIndex_primitive : Primrec rowIndex := by
  exact Primrec.encode.comp Code.primrec_pappAck

theorem rowIndex_evaluation (m n : ℕ) :
    UniversalComputation.phi (rowIndex m) n = Part.some (ack m n) := by
  simpa only [rowIndex, UniversalComputation.phi, Denumerable.ofNat_encode] using
    Code.eval_pappAck m n

theorem ack_total_recursive :
    TotalRecursive (lift (fun v : Args 2 => ack (v.get 0) (v.get 1))) := by
  refine ⟨MachinesAndComputationHistories.recursive_iff_partrec.mpr ?_, ?_⟩
  · exact (computable₂_ack.comp
      ((Primrec.vector_get.comp Primrec.id (Primrec.const 0)).to_comp)
      ((Primrec.vector_get.comp Primrec.id (Primrec.const 1)).to_comp)).partrec
  · intro v
    trivial

theorem diagonal_total_recursive :
    TotalRecursive (lift (fun v : Args 1 => ack (v.get 0) (v.get 0))) := by
  refine ⟨MachinesAndComputationHistories.recursive_iff_partrec.mpr ?_, ?_⟩
  · exact (computable₂_ack.comp
      ((Primrec.vector_get.comp Primrec.id (Primrec.const 0)).to_comp)
      ((Primrec.vector_get.comp Primrec.id (Primrec.const 0)).to_comp)).partrec
  · intro v
    trivial

theorem diagonal_eventually_dominates {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ m, ∀ n, m ≤ n → f n < ack n n := by
  obtain ⟨m, hm⟩ := exists_lt_ack_of_nat_primrec hf
  exact ⟨m, fun n hn => (hm n).trans_le (ack_mono_left n hn)⟩

theorem primitive_proper_subset :
    {f : Args 1 → ℕ | Nat.Primrec' f} ⊂
      {f | TotalRecursive (lift f)} := by
  refine ⟨fun f hf => primitive_recursive_inclusion hf, ?_⟩
  intro h
  have hp : Nat.Primrec' (fun v : Args 1 => ack (v.get 0) (v.get 0)) :=
    h diagonal_total_recursive
  exact not_nat_primrec_ack_self ((UniversalComputation.unary_primitive_iff _).mp hp)

theorem no_primitive_row_evaluator :
    ¬ ∃ E : ℕ → ℕ → ℕ, Primrec₂ E ∧ ∀ m n, E (rowIndex m) n = ack m n := by
  rintro ⟨E, hE, he⟩
  exact not_primrec_ack_self ((hE.comp rowIndex_primitive Primrec.id).of_eq (fun n => he n n))

end Lemmatheca.ComputabilityTheory.AckermannFunction
