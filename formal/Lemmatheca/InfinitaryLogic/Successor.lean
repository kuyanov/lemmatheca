import Lemmatheca.InfinitaryLogic.Syntax
import Lemmatheca.FirstOrderStructures.BasicStructures

/-! A countable disjunction specifies the standard zero-and-successor domain. -/
namespace Lemmatheca.MathematicalLogic.InfinitaryLogic

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lemmatheca.MathematicalLogic.BasicStructures

universe w

abbrev successorLanguage := naturalSuccessorLanguage

def successorZero {n : ℕ} : successorLanguage.Term (Empty ⊕ Fin n) :=
  .func .zero Fin.elim0

def successorTerm {n : ℕ} (t : successorLanguage.Term (Empty ⊕ Fin n)) :
    successorLanguage.Term (Empty ⊕ Fin n) := .func .succ (fun _ => t)

/-- Every element equals one of the shared, finite numeral terms. -/
def numeralExhaustion : Sentence successorLanguage :=
  .all (Formula.disj fun n => .equal (.var (.inr 0)) ((numeral n).relabel Sum.inl))

def successorSentence : Sentence successorLanguage :=
  Formula.and
    (.all (Formula.equal (successorTerm (.var (.inr 0))) successorZero).neg)
    (Formula.and
      (.all (.all (.imp
        (.equal (successorTerm (.var (.inr 0))) (successorTerm (.var (.inr 1))))
        (.equal (.var (.inr 0)) (.var (.inr 1)))))) numeralExhaustion)

variable (M : Type w) [successorLanguage.Structure M]

def zeroValue : M := funMap (L := successorLanguage) NaturalFunctionSymbol.zero Fin.elim0
def succValue (x : M) : M := funMap (L := successorLanguage) NaturalFunctionSymbol.succ (fun _ => x)
def numeralValue (n : ℕ) : M := (numeral n).realize Empty.elim

private theorem numeralValue_zero : numeralValue M 0 = zeroValue M := by
  unfold numeralValue numeral zeroValue Term.realize
  congr 1
  funext i
  exact i.elim0

private theorem numeralValue_succ (n : ℕ) :
    numeralValue M (n + 1) = succValue M (numeralValue M n) := rfl

private theorem successorZero_realize {n : ℕ} (a : Empty → M) (b : Fin n → M) :
    (successorZero : successorLanguage.Term (Empty ⊕ Fin n)).realize (Sum.elim a b) =
      zeroValue M := by
  unfold successorZero zeroValue Term.realize
  congr 1
  funext i
  exact i.elim0

private theorem successorTerm_realize {n : ℕ} (t : successorLanguage.Term (Empty ⊕ Fin n))
    (a : Empty → M) (b : Fin n → M) :
    (successorTerm t).realize (Sum.elim a b) = succValue M (t.realize (Sum.elim a b)) := rfl

private theorem realize_and {n : ℕ} (φ ψ : Formula successorLanguage Empty n)
    (a : Empty → M) (b : Fin n → M) :
    Realize (φ.and ψ) a b ↔ Realize φ a b ∧ Realize ψ a b :=
  (realize_abbreviations φ ψ a b).2.1

private theorem relabeled_numeral_realize {n : ℕ} (k : ℕ)
    (a : Empty → M) (b : Fin n → M) :
    ((numeral k).relabel (Sum.inl : Empty → Empty ⊕ Fin n)).realize (Sum.elim a b) =
      numeralValue M k := by
  rw [Term.realize_relabel]
  unfold numeralValue
  congr 1
  funext x
  exact x.elim

private theorem numeralExhaustion_realize : Sentence.Realize numeralExhaustion M ↔
    Function.Surjective (numeralValue M) := by
  change (∀ x : M, Realize (Formula.disj fun n =>
    Formula.equal (.var (.inr 0)) ((numeral n).relabel Sum.inl))
      Empty.elim (Fin.snoc Fin.elim0 x)) ↔ _
  simp_rw [realize_disj]
  simp only [Realize, Term.realize_var, Sum.elim_inr,
    relabeled_numeral_realize]
  exact forall_congr' fun x => exists_congr fun n => eq_comm

theorem successorSentence_realize : Sentence.Realize successorSentence M ↔
    (∀ x : M, succValue M x ≠ zeroValue M) ∧
    Function.Injective (succValue M) ∧ Function.Surjective (numeralValue M) := by
  unfold successorSentence Sentence.Realize
  rw [realize_and, realize_and]
  apply and_congr
  · simp only [Realize, Formula.neg, successorTerm_realize, successorZero_realize,
      Term.realize_var, Sum.elim_inr]
    rfl
  · apply and_congr
    · simp only [Realize, successorTerm_realize, Term.realize_var, Sum.elim_inr,
        Fin.snoc_apply_zero]
      rfl
    · exact numeralExhaustion_realize M

theorem nat_successorSentence : Sentence.Realize successorSentence ℕ := by
  apply (successorSentence_realize ℕ).mpr
  refine ⟨fun x => Nat.succ_ne_zero x, Nat.succ_injective, ?_⟩
  intro n
  exact ⟨n, numeral_value n⟩

theorem successor_canonical_isomorphism (h : Sentence.Realize successorSentence M) :
    ∃ e : ℕ ≃[successorLanguage] M, ∀ n, e n = numeralValue M n := by
  obtain ⟨hz, hs, hsurj⟩ := (successorSentence_realize M).mp h
  have hi : Function.Injective (numeralValue M) := by
    intro n
    induction n with
    | zero =>
      intro m hm
      cases m with
      | zero => rfl
      | succ m =>
        rw [numeralValue_zero, numeralValue_succ] at hm
        exact (hz (numeralValue M m) hm.symm).elim
    | succ n ih =>
      intro m hm
      cases m with
      | zero =>
        rw [numeralValue_zero, numeralValue_succ] at hm
        exact (hz (numeralValue M n) hm).elim
      | succ m => exact congrArg Nat.succ (ih (hs hm))
  let e : ℕ ≃ M := Equiv.ofBijective (numeralValue M) ⟨hi, hsurj⟩
  refine ⟨{ toEquiv := e, map_fun' := ?_, map_rel' := ?_ }, fun _ => rfl⟩
  · intro n f x
    cases f with
    | zero =>
      have hx : e.toFun ∘ x = Fin.elim0 := by
        funext i
        exact i.elim0
      rw [hx]
      exact numeralValue_zero M
    | succ =>
      have hx : e.toFun ∘ x = fun _ => numeralValue M (x 0) := by
        funext i
        have hi0 : i = 0 := Fin.eq_zero i
        subst i
        rfl
      rw [hx]
      change numeralValue M (x 0 + 1) = succValue M (numeralValue M (x 0))
      rfl
  · intro n r
    exact r.elim

theorem successor_categorical : Sentence.Realize successorSentence M ↔
    Nonempty (ℕ ≃[successorLanguage] M) := by
  constructor
  · intro h
    obtain ⟨e, _⟩ := successor_canonical_isomorphism M h
    exact ⟨e⟩
  · rintro ⟨e⟩
    exact (sentence_isomorphism e successorSentence).mp nat_successorSentence

end Lemmatheca.MathematicalLogic.InfinitaryLogic
