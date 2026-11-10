import Lemmatheca.CraigReaxiomatization.Snapshots

/-! Literal repeated conjunction and its exact original-syntax numerical code. -/
namespace Lemmatheca.ComputabilityTheory.CraigReaxiomatization
open FirstOrder FirstOrder.Language
open Lemmatheca.ProofTheory.CodingFormalProofs
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v
variable {L : Language.{u, v}}
noncomputable section

def repeatConjunction (A : L.Sentence) : ℕ → L.Sentence
  | 0 => A
  | n + 1 => repeatConjunction A n ⊓ A

def paddingCode : ℕ → ℕ → ℕ
  | 0, a => a
  | n + 1, a => andCode (paddingCode n a) a

theorem padding_code_computable : Computable₂ paddingCode := by
  have hand : Primrec₂ andCode := by
    unfold Primrec₂ andCode negCode impCode botCode
    fun_prop
  have hs : Primrec₂ (fun (a : ℕ) (q : ℕ × ℕ) => andCode q.2 a) :=
    hand.comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  have hp : Primrec₂ (fun (a n : ℕ) => paddingCode n a) :=
    (Primrec.nat_rec Primrec.id hs).of_eq (fun a n => by
      induction n with
      | zero => rfl
      | succ n ih =>
        change andCode (Nat.rec a (fun _ v => andCode v a) n) a = andCode (paddingCode n a) a
        exact congrArg (fun v => andCode v a) ih)
  exact hp.swap.to_comp

theorem padding_code_eq (S : EffectiveSignature L) (A : L.Sentence) (n : ℕ) :
    paddingCode n (sentenceCode S A) = sentenceCode S (repeatConjunction A n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change andCode (paddingCode n (sentenceCode S A)) (sentenceCode S A) =
      andCode (sentenceCode S (repeatConjunction A n)) (sentenceCode S A)
    rw [ih]

theorem padding_derivability (T : L.Theory) (A : L.Sentence) (n : ℕ) :
    Derives T (repeatConjunction A n) ↔ Derives T A := by
  constructor
  · intro h
    cases n with
    | zero => exact h
    | succ n =>
      obtain ⟨Γ, hΓ, hp⟩ := h
      exact ⟨Γ, hΓ, .conjElimRight hp⟩
  · rintro ⟨Γ, hΓ, hp⟩
    refine ⟨Γ, hΓ, ?_⟩
    induction n with
    | zero => exact hp
    | succ n ih => exact .conjIntro ih hp

theorem left_lt_and_code (a b : ℕ) : a < andCode a b := by
  have h1 : a < impCode a (negCode b) := child_lt (by simp)
  have h2 : impCode a (negCode b) < andCode a b := child_lt (by simp)
  exact h1.trans h2

theorem padding_bound (n a : ℕ) : n ≤ paddingCode n a := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (left_lt_and_code _ _))

end
end Lemmatheca.ComputabilityTheory.CraigReaxiomatization
