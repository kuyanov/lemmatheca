import Lemmatheca.MathematicalLogic.ArithmeticRepresentabilityBasic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-! Gödel's beta function: finite coding and its arithmetic formula. -/
namespace Lemmatheca.MathematicalLogic.ArithmeticRepresentability

/-- The modulus used to read position `i` of a beta code. -/
def betaModulus (d i : ℕ) : ℕ := (i + 1) * d + 1

/-- Zero-safe beta decoding; the modulus is positive even when `d = 0`. -/
def beta (c d i : ℕ) : ℕ := c % betaModulus d i

/-- A common multiple of the small positive differences makes the moduli coprime. -/
theorem betaModulus_coprime {n d : ℕ}
    (hd : ∀ k, 0 < k → k ≤ n → k ∣ d) {i j : ℕ}
    (hi : i < n) (hj : j < n) (hne : i ≠ j) :
    Nat.Coprime (betaModulus d i) (betaModulus d j) := by
  suffices h : ∀ i j, i < n → j < n → i < j →
      Nat.Coprime (betaModulus d i) (betaModulus d j) by
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact h i j hi hj hij
    · exact (h j i hj hi hji).symm
  intro i j hi hj hij
  dsimp only [betaModulus]
  let g := Nat.gcd ((i + 1) * d + 1) ((j + 1) * d + 1)
  have hgi : g ∣ (i + 1) * d + 1 := Nat.gcd_dvd_left _ _
  have hgj : g ∣ (j + 1) * d + 1 := Nat.gcd_dvd_right _ _
  have hid : Nat.Coprime ((i + 1) * d + 1) d := by
    simp [Nat.Coprime]
  have hgd : Nat.Coprime g d := hid.of_dvd_left hgi
  have hsum : (j + 1) * d + 1 = ((i + 1) * d + 1) + (j - i) * d := by
    have hindex : j + 1 = (i + 1) + (j - i) := by omega
    rw [hindex]
    ring
  have hdiff : g ∣ (j - i) * d := by
    apply (Nat.dvd_add_iff_right hgi).mpr
    rw [← hsum]
    exact hgj
  have hsmall : j - i ∣ d := hd _ (by omega) (by omega)
  exact Nat.eq_one_of_dvd_coprimes hid hgi ((hgd.dvd_mul_right.mp hdiff).trans hsmall)

/-- Every finite tuple can be read from two natural-number beta parameters. -/
theorem beta_codes_finite_tuple (n : ℕ) (a : Fin n → ℕ) :
    ∃ c d, 0 < d ∧ ∀ i : Fin n, beta c d i = a i := by
  classical
  let bound := Finset.univ.sup a
  let d := (n + 1).factorial * (bound + 1)
  have hdpos : 0 < d := Nat.mul_pos (Nat.factorial_pos _) (by omega)
  have hdiv : ∀ k, 0 < k → k ≤ n → k ∣ d := by
    intro k hk hkn
    exact dvd_mul_of_dvd_left (Nat.dvd_factorial hk (by omega : k ≤ n + 1)) _
  have hbound : ∀ i, a i < betaModulus d i.val := by
    intro i
    have ha : a i ≤ bound := Finset.le_sup (Finset.mem_univ i)
    have hd : bound + 1 ≤ d := Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    dsimp only [betaModulus]
    have hmul : d ≤ (i.val + 1) * d := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hnonzero : ∀ i : Fin n, i ∈ Finset.univ → betaModulus d i.val ≠ 0 := by
    intro i _
    dsimp only [betaModulus]
    omega
  have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin n)) : Set (Fin n))
      (fun (i j : Fin n) => Nat.Coprime (betaModulus d i.val) (betaModulus d j.val)) := by
    intro i _ j _ hij
    exact betaModulus_coprime hdiv i.isLt j.isLt (by exact fun h => hij (Fin.ext h))
  obtain ⟨c, hc⟩ := Nat.chineseRemainderOfFinset a (fun i => betaModulus d i.val)
    Finset.univ hnonzero hpair
  refine ⟨c, d, hdpos, ?_⟩
  intro i
  exact Eq.trans (hc i (Finset.mem_univ i)) (Nat.mod_eq_of_lt (hbound i))

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.ArithmeticTheories

noncomputable section
universe u

/-- An actual arithmetic term for the always-positive beta modulus. -/
def betaModulusTerm {α : Type*} (d i : language.Term α) : language.Term α :=
  succTerm (mulTerm (succTerm i) d)

/-- Bounded graph formula. The bound on the quotient is part of the formula. -/
def betaFormula {α : Type*} (c d i y : language.Term α) : language.Formula α :=
  ltFormula y (betaModulusTerm d i) ⊓
    boundedEx c ((c.relabel Sum.inl).equal
      (addTerm (mulTerm ((betaModulusTerm d i).relabel Sum.inl) (.var (.inr ())))
        (y.relabel Sum.inl)))

/-- The canonical three-input graph, with the output in the distinguished slot. -/
def betaGraph : language.Formula (Fin 3 ⊕ Unit) :=
  betaFormula (.var (.inl 0)) (.var (.inl 1)) (.var (.inl 2)) (.var (.inr ()))

private theorem deltaZero_and {α : Type} {φ ψ : language.Formula α}
    (hφ : DeltaZero φ) (hψ : DeltaZero ψ) : DeltaZero (φ ⊓ ψ) := by
  exact .imp (.imp hφ (.imp hψ .falsum)) .falsum

/-- The beta graph uses only bounded quantification in the shared syntax. -/
theorem deltaZero_betaFormula {α : Type} (c d i y : language.Term α) :
    DeltaZero (betaFormula c d i y) := by
  exact deltaZero_and (.le _ _) (.ex _ (.equal _ _))

/-- Strict bounds by a numeral have precisely their standard finite values. -/
theorem strict_finite_bound {M : Type u} [language.Structure M] [M ⊨ Q]
    (a : M) (n : ℕ) :
    leValue M (succValue M a) (numeralValue M n) ↔
      ∃ m < n, a = numeralValue M m := by
  rw [finite_bound]
  constructor
  · rintro ⟨m, hmn, hm⟩
    cases m with
    | zero =>
      exact False.elim ((model_Q_iff M).mp ‹M ⊨ Q› |>.1 a
        (by simpa only [numeral_value_zero] using hm))
    | succ m =>
      refine ⟨m, by omega, ?_⟩
      apply (model_Q_iff M).mp ‹M ⊨ Q› |>.2.1
      simpa only [numeral_value_succ] using hm
  · rintro ⟨m, hmn, rfl⟩
    exact ⟨m + 1, by omega, (numeral_value_succ M m).symm⟩

theorem realize_betaFormula {α : Type*} {M : Type u} [language.Structure M]
    (v : α → M) (c d i y : language.Term α) :
    (betaFormula c d i y).Realize v ↔
      leValue M (succValue M (y.realize v)) ((betaModulusTerm d i).realize v) ∧
        ∃ q, leValue M q (c.realize v) ∧
          c.realize v = addValue M
            (mulValue M ((betaModulusTerm d i).realize v) q) (y.realize v) := by
  simp only [betaFormula, Formula.realize_inf, ltFormula, realize_leFormula,
    realize_succTerm, realize_boundedEx, Formula.realize_equal, realize_addTerm,
    realize_mulTerm, Term.realize_relabel, Term.realize_var, extend,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr]

/-- Numeral inputs force the correct beta value even for arbitrary model outputs. -/
theorem beta_modelwise {M : Type u} [language.Structure M] [M ⊨ Q]
    (c d i : ℕ) (y : M) :
    (leValue M (succValue M y) (numeralValue M (betaModulus d i)) ∧
      ∃ q, leValue M q (numeralValue M c) ∧
        numeralValue M c = addValue M
          (mulValue M (numeralValue M (betaModulus d i)) q) y) ↔
      y = numeralValue M (beta c d i) := by
  constructor
  · rintro ⟨hy, q, hq, heq⟩
    obtain ⟨r, hr, rfl⟩ := (strict_finite_bound y _).mp hy
    obtain ⟨k, _, rfl⟩ := (finite_bound q c).mp hq
    rw [numeral_mul, numeral_add] at heq
    have hc : c = betaModulus d i * k + r := numeral_injective M heq
    have hmod : c % betaModulus d i = r := by
      rw [hc]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
    exact congrArg (numeralValue M) hmod.symm
  · rintro rfl
    have hm : 0 < betaModulus d i := by dsimp [betaModulus]; omega
    refine ⟨(strict_finite_bound _ _).mpr ⟨_, Nat.mod_lt c hm, rfl⟩,
      numeralValue M (c / betaModulus d i),
      (finite_bound _ _).mpr ⟨_, Nat.div_le_self c _, rfl⟩, ?_⟩
    rw [numeral_mul, numeral_add]
    apply congrArg (numeralValue M)
    have h := Nat.mod_add_div c (betaModulus d i)
    dsimp only [beta] at *
    omega

/-- The actual shared-language beta formula strongly represents beta in Q. -/
theorem beta_stronglyRepresents :
    StronglyRepresents (fun x : Fin 3 → ℕ => beta (x 0) (x 1) (x 2)) betaGraph := by
  apply stronglyRepresents_of_modelwise
  intro M x y
  rw [betaGraph, realize_betaFormula]
  simp only [Term.realize_var, extend, Sum.elim_inl, Sum.elim_inr,
    betaModulusTerm, realize_succTerm, realize_mulTerm,
    numeral_mul, ← numeral_value_succ]
  exact beta_modelwise (x 0) (x 1) (x 2) y

end
end Lemmatheca.MathematicalLogic.ArithmeticRepresentability
