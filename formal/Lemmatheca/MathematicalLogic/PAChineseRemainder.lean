import Lemmatheca.MathematicalLogic.PAOrderedArithmetic

namespace Lemmatheca.MathematicalLogic.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open FirstOrderProofs
noncomputable section
universe u

/-- Least witnesses for each fixed actual arithmetic formula, using PA induction. -/
theorem least_witness_model {k : ℕ} {M : Type u} [language.Structure M] [M ⊨ PA]
    (φ : language.Formula (Fin k ⊕ Unit)) (x : Fin k → M)
    (h : ∃ y, φ.Realize (extend x y)) :
    ∃ y, φ.Realize (extend x y) ∧
      ∀ z, leValue M (succValue M z) y → ¬ φ.Realize (extend x z) := by
  classical
  by_contra hn
  have smaller (y : M) (hy : φ.Realize (extend x y)) :
      ∃ z, leValue M (succValue M z) y ∧ φ.Realize (extend x z) := by
    by_contra hs
    apply hn
    refine ⟨y, hy, ?_⟩
    intro z hz hφ
    exact hs ⟨z, hz, hφ⟩
  let ψ : language.Formula (Fin k ⊕ Unit) :=
    boundedAll (.var (.inr ()))
      (φ.relabel (Sum.elim (fun i => .inl (.inl i)) (fun _ => .inr ()))).not
  have hψ (b : M) : ψ.Realize (extend x b) ↔
      ∀ z, leValue M z b → ¬ φ.Realize (extend x z) := by
    simp only [ψ, realize_boundedAll, Term.realize_var,
      Formula.realize_not, Formula.realize_relabel]
    have he (a : M) :
        extend (extend x b) a ∘
          Sum.elim (fun i => .inl (.inl i)) (fun _ : Unit => .inr ()) = extend x a := by
      funext i
      cases i <;> rfl
    simp only [he]
    rfl
  have hcut (a b : M) (hab : leValue M (succValue M a) (succValue M b)) :
      leValue M a b := by
    obtain ⟨d, hd⟩ := hab
    exact ⟨d, successor_injective (by simpa only [add_successor_value] using hd)⟩
  have hall : ∀ b z : M, leValue M z b → ¬ φ.Realize (extend x z) := by
    apply formula_induction ψ x _ (fun b => hψ b)
    · intro z hz hφ
      have he : z = zeroValue M := le_antisymm_value hz (zero_le_value z)
      subst z
      obtain ⟨w, hw, _⟩ := smaller _ hφ
      exact successor_ne_zero w (le_antisymm_value hw (zero_le_value _))
    · intro b hb z hz hφ
      rcases le_or_successor_le z b with hzb | hbz
      · exact hb z hzb hφ
      · have he : z = succValue M b := le_antisymm_value hz hbz
        subst z
        obtain ⟨w, hw, hφw⟩ := smaller _ hφ
        exact hb w (hcut w b hw) hφw
  obtain ⟨y, hy⟩ := h
  exact hall y y (le_refl_value y) hy

def DividesModel (M : Type u) [language.Structure M] (a b : M) : Prop :=
  ∃ q, mulValue M a q = b

def dividesFormula {α : Type} (a b : language.Term α) : language.Formula α :=
  ((mulTerm (a.relabel Sum.inl) (.var (.inr ()))).equal (b.relabel Sum.inl)).iExs Unit

theorem realize_dividesFormula {α : Type} {M : Type u} [language.Structure M]
    (a b : language.Term α) (v : α → M) :
    (dividesFormula a b).Realize v ↔ DividesModel M (a.realize v) (b.realize v) := by
  simp only [dividesFormula, Formula.realize_iExs, Formula.realize_equal,
    realize_mulTerm, Term.realize_relabel, Term.realize_var, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, DividesModel]
  exact ⟨fun ⟨q, hq⟩ => ⟨q (), hq⟩, fun ⟨q, hq⟩ => ⟨fun _ => q, hq⟩⟩

def CoprimeModel (M : Type u) [language.Structure M] (a b : M) : Prop :=
  ∀ r, DividesModel M r a → DividesModel M r b → r = numeralValue M 1

private def positiveCombination : language.Formula (Fin 2 ⊕ Unit) :=
  let m : language.Term ((Fin 2 ⊕ Unit) ⊕ Fin 4) := .var (.inl (.inl 0))
  let n : language.Term ((Fin 2 ⊕ Unit) ⊕ Fin 4) := .var (.inl (.inl 1))
  let z : language.Term ((Fin 2 ⊕ Unit) ⊕ Fin 4) := .var (.inl (.inr ()))
  (((Term.var (.inr ())).equal zeroTerm).not) ⊓
    ((addTerm (mulTerm m (.var (.inr 0))) (mulTerm n (.var (.inr 1)))).equal
      (addTerm z (addTerm (mulTerm m (.var (.inr 2)))
        (mulTerm n (.var (.inr 3)))))).iExs (Fin 4)

private theorem positiveCombination_realize {M : Type u} [language.Structure M]
    (m n z : M) :
    positiveCombination.Realize (extend ![m, n] z) ↔
      z ≠ zeroValue M ∧ ∃ v : Fin 4 → M,
        addValue M (mulValue M m (v 0)) (mulValue M n (v 1)) =
          addValue M z (addValue M (mulValue M m (v 2)) (mulValue M n (v 3))) := by
  simp only [positiveCombination, Formula.realize_inf, Formula.realize_not,
    Formula.realize_equal, Formula.realize_iExs, Term.realize_var,
    realize_zeroTerm, realize_addTerm, realize_mulTerm, extend,
    Sum.elim_inl, Sum.elim_inr]
  rfl

theorem bezout_model {M : Type u} [language.Structure M] [M ⊨ PA]
    (m n : M) (hm : m ≠ zeroValue M) (hcop : CoprimeModel M m n) :
    ∃ v : Fin 4 → M,
      addValue M (mulValue M m (v 0)) (mulValue M n (v 1)) =
        addValue M (numeralValue M 1)
          (addValue M (mulValue M m (v 2)) (mulValue M n (v 3))) := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have hex : ∃ z : M, positiveCombination.Realize (extend ![m, n] z) := by
    refine ⟨m, (positiveCombination_realize m n m).mpr ⟨hm, ![1, 0, 0, 0], ?_⟩⟩
    change m * 1 + n * 0 = m + (m * 0 + n * 0)
    ring
  obtain ⟨r, hr, hmin⟩ := least_witness_model positiveCombination ![m, n] hex
  obtain ⟨hrzero, v, hv⟩ := (positiveCombination_realize m n r).mp hr
  change m * v 0 + n * v 1 = r + (m * v 2 + n * v 3) at hv
  have hdvd (z u w : M) (hz : z = m * u + n * w) : DividesModel M r z := by
    obtain ⟨qr, hqr, _⟩ := division_model r hrzero z
    obtain ⟨hqe, hqr⟩ := hqr
    change z = r * qr.1 + qr.2 at hqe
    have hrem : qr.2 = 0 := by
      by_contra hs
      apply hmin qr.2 hqr
      apply (positiveCombination_realize m n qr.2).mpr
      refine ⟨hs, ![qr.1 * v 2 + u, qr.1 * v 3 + w, qr.1 * v 0, qr.1 * v 1], ?_⟩
      change m * (qr.1 * v 2 + u) + n * (qr.1 * v 3 + w) =
        qr.2 + (m * (qr.1 * v 0) + n * (qr.1 * v 1))
      calc
        _ = z + qr.1 * (m * v 2 + n * v 3) := by rw [hz]; ring
        _ = (r * qr.1 + qr.2) + qr.1 * (m * v 2 + n * v 3) := by rw [hqe]
        _ = qr.2 + qr.1 * (r + (m * v 2 + n * v 3)) := by ring
        _ = qr.2 + qr.1 * (m * v 0 + n * v 1) := by rw [← hv]
        _ = _ := by ring
    refine ⟨qr.1, ?_⟩
    change r * qr.1 = z
    simpa only [hrem, add_zero] using hqe.symm
  have hrm := hdvd m 1 0 (by ring)
  have hrn := hdvd n 0 1 (by ring)
  have hone := hcop r hrm hrn
  refine ⟨v, ?_⟩
  change m * v 0 + n * v 1 = numeralValue M 1 + (m * v 2 + n * v 3)
  simpa only [hone] using hv

theorem quotient_of_difference {M : Type u} [language.Structure M] [M ⊨ PA]
    (m x y a : M) (hm : m ≠ zeroValue M)
    (h : mulValue M m x = addValue M a (mulValue M m y)) : DividesModel M m a := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  change m * x = a + m * y at h
  have hmpos : (0 : M) < m := lt_of_le_of_ne (zero_le_value m) (Ne.symm hm)
  have hprod : m * y ≤ m * x := by
    rw [h]
    exact le_add_of_nonneg_left (zero_le_value a)
  have hyx : y ≤ x := le_of_not_gt (fun hxy =>
    (not_le_of_gt (mul_lt_mul_of_pos_left hxy hmpos)) hprod)
  obtain ⟨q, hq⟩ := hyx
  change q + y = x at hq
  refine ⟨q, ?_⟩
  apply add_right_cancel (b := m * y)
  change m * q + m * y = a + m * y
  calc
    _ = m * (q + y) := by ring
    _ = m * x := by rw [hq]
    _ = a + m * y := h

theorem coprime_cancellation_model {M : Type u} [language.Structure M] [M ⊨ PA]
    (m n a : M) (h : CoprimeModel M m n)
    (ha : DividesModel M m (mulValue M n a)) : DividesModel M m a := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  by_cases hm : m = zeroValue M
  · have hn : n = numeralValue M 1 := h n ⟨0, by change n * 0 = _; rw [mul_zero, hm]; rfl⟩
      ⟨1, by exact mul_one_value n⟩
    simpa only [hn, numeral_value_succ, numeral_value_zero, one_mul_value] using ha
  obtain ⟨v, hv⟩ := bezout_model m n hm h
  obtain ⟨t, ht⟩ := ha
  change m * t = n * a at ht
  rw [numeral_value_succ, numeral_value_zero] at hv
  change m * v 0 + n * v 1 = 1 + (m * v 2 + n * v 3) at hv
  have he : m * (v 0 * a + t * v 1) = a + m * (v 2 * a + t * v 3) := by
    calc
      _ = m * v 0 * a + (m * t) * v 1 := by ring
      _ = (m * v 0 + n * v 1) * a := by rw [ht]; ring
      _ = (1 + (m * v 2 + n * v 3)) * a := by rw [hv]
      _ = a + m * v 2 * a + (n * a) * v 3 := by ring
      _ = _ := by rw [← ht]; ring
  exact quotient_of_difference m _ _ a hm he

theorem two_modulus_model {M : Type u} [language.Structure M] [M ⊨ PA]
    (m n a b : M) (hm : m ≠ zeroValue M) (hn : n ≠ zeroValue M)
    (hcop : CoprimeModel M m n)
    (ha : leValue M (succValue M a) m) (hb : leValue M (succValue M b) n) :
    ∃ c q r, c = addValue M (mulValue M m q) a ∧
      c = addValue M (mulValue M n r) b := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  obtain ⟨v, hv⟩ := bezout_model m n hm hcop
  rw [numeral_value_succ, numeral_value_zero] at hv
  change m * v 0 + n * v 1 = 1 + (m * v 2 + n * v 3) at hv
  let s₀ : M := a * n * v 1 + b * m * v 0
  let s₁ : M := a * n * v 3 + b * m * v 2
  have hmn : (1 : M) ≤ m * n := by
    obtain ⟨d, hd⟩ := predecessor (mulValue M m n) (mul_ne_zero_value hm hn)
    exact ⟨d, (add_one_value d).trans hd.symm⟩
  have hle : s₁ ≤ s₀ + m * n * s₁ := calc
    s₁ = 1 * s₁ := (one_mul _).symm
    _ ≤ m * n * s₁ := mul_le_mul_of_nonneg_right hmn (zero_le_value _)
    _ ≤ s₀ + m * n * s₁ := le_add_of_nonneg_left (zero_le_value _)
  obtain ⟨c, hc⟩ := hle
  change c + s₁ = s₀ + m * n * s₁ at hc
  have hmodm : c + m * (a * v 0 + b * v 2) =
      a + m * (a * v 2 + b * v 0 + n * s₁) := by
    apply add_right_cancel (b := s₁)
    calc
      _ = (c + s₁) + m * (a * v 0 + b * v 2) := by ring
      _ = (s₀ + m * n * s₁) + m * (a * v 0 + b * v 2) := by rw [hc]
      _ = a * (m * v 0 + n * v 1) + b * m * (v 0 + v 2) + m * n * s₁ := by
        dsimp only [s₀]
        ring
      _ = a * (1 + (m * v 2 + n * v 3)) + b * m * (v 0 + v 2) + m * n * s₁ := by rw [hv]
      _ = _ := by dsimp only [s₁]; ring
  have hmodn : c + n * (b * v 1 + a * v 3) =
      b + n * (b * v 3 + a * v 1 + m * s₁) := by
    apply add_right_cancel (b := s₁)
    calc
      _ = (c + s₁) + n * (b * v 1 + a * v 3) := by ring
      _ = (s₀ + m * n * s₁) + n * (b * v 1 + a * v 3) := by rw [hc]
      _ = b * (m * v 0 + n * v 1) + a * n * (v 1 + v 3) + m * n * s₁ := by
        dsimp only [s₀]
        ring
      _ = b * (1 + (m * v 2 + n * v 3)) + a * n * (v 1 + v 3) + m * n * s₁ := by rw [hv]
      _ = _ := by dsimp only [s₁]; ring
  have hrem (m a u w : M) (hm : m ≠ zeroValue M)
      (ha : leValue M (succValue M a) m) (he : c + m * u = a + m * w) :
      ∃ q, c = m * q + a := by
    obtain ⟨qr, hqr, _⟩ := division_model m hm c
    change c = m * qr.1 + qr.2 ∧ leValue M (succValue M qr.2) m at hqr
    obtain ⟨z, _, huniq⟩ := division_model m hm (c + m * u)
    have h₁ : (qr.1 + u, qr.2) = z := huniq _ ⟨by
      change c + m * u = m * (qr.1 + u) + qr.2
      rw [hqr.1]
      ring, hqr.2⟩
    have h₂ : (w, a) = z := huniq _ ⟨by
      change c + m * u = m * w + a
      exact he.trans (add_comm _ _), ha⟩
    have hr : qr.2 = a := congrArg Prod.snd (h₁.trans h₂.symm)
    exact ⟨qr.1, by simpa only [hr] using hqr.1⟩
  obtain ⟨q, hq⟩ := hrem m a _ _ hm ha hmodm
  obtain ⟨r, hr⟩ := hrem n b _ _ hn hb hmodn
  exact ⟨c, q, r, hq, hr⟩

theorem common_multiple_model {M : Type u} [language.Structure M] [M ⊨ PA]
    (n : M) : ∃ d, d ≠ zeroValue M ∧ ∀ i,
      i ≠ zeroValue M → leValue M i n → DividesModel M i d := by
  let φ : language.Formula (Fin 0 ⊕ Unit) :=
    (((Term.var (.inr ())).equal zeroTerm).not ⊓
      boundedAll (.var (.inl (.inr ())))
        ((((Term.var (.inr ())).equal zeroTerm).not).imp
          (dividesFormula (.var (.inr ())) (.var (.inl (.inr ())))))).iExs Unit
  have hφ (b : M) : φ.Realize (extend (Fin.elim0 : Fin 0 → M) b) ↔
      ∃ d, d ≠ zeroValue M ∧ ∀ i, i ≠ zeroValue M → leValue M i b → DividesModel M i d := by
    simp only [φ, Formula.realize_iExs, Formula.realize_inf, Formula.realize_not,
      Formula.realize_equal, Term.realize_var, realize_zeroTerm, realize_boundedAll,
      Formula.realize_imp, realize_dividesFormula, extend, Sum.elim_inl, Sum.elim_inr]
    constructor
    · rintro ⟨d, hd, hi⟩
      exact ⟨d (), hd, fun i hi0 hib => hi i hib hi0⟩
    · rintro ⟨d, hd, hi⟩
      exact ⟨fun _ => d, hd, fun i hib hi0 => hi i hi0 hib⟩
  apply formula_induction φ Fin.elim0 _ (fun b => hφ b) _ _ n
  · refine ⟨succValue M (zeroValue M), successor_ne_zero _, ?_⟩
    intro i hi0 hi
    exact (hi0 (le_antisymm_value hi (zero_le_value i))).elim
  · intro b hb
    obtain ⟨d, hd, hdiv⟩ := hb
    refine ⟨mulValue M d (succValue M b), mul_ne_zero_value hd (successor_ne_zero b), ?_⟩
    intro i hi0 hib
    rcases le_or_successor_le i b with hi | hi
    · obtain ⟨q, hq⟩ := hdiv i hi0 hi
      exact ⟨mulValue M q (succValue M b), by rw [← mul_assoc_value, hq]⟩
    · have he : i = succValue M b := le_antisymm_value hib hi
      subst i
      exact ⟨d, mul_comm_value _ _⟩

theorem divides_trans_model {M : Type u} [language.Structure M]
    [M ⊨ PA] {a b c : M} (hab : DividesModel M a b) (hbc : DividesModel M b c) :
    DividesModel M a c := by
  obtain ⟨q, hq⟩ := hab
  obtain ⟨r, hr⟩ := hbc
  exact ⟨mulValue M q r, by rw [← mul_assoc_value, hq, hr]⟩

theorem one_le_nonzero_model {M : Type u} [language.Structure M] [M ⊨ PA]
    (a : M) (ha : a ≠ zeroValue M) : leValue M (numeralValue M 1) a := by
  obtain ⟨d, hd⟩ := predecessor a ha
  exact ⟨d, by rw [numeral_value_succ, numeral_value_zero, add_one_value, ← hd]⟩

theorem divisor_of_one_model {M : Type u} [language.Structure M] [M ⊨ PA]
    (a : M) (h : DividesModel M a (numeralValue M 1)) : a = numeralValue M 1 := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  obtain ⟨q, hq⟩ := h
  rw [numeral_value_succ, numeral_value_zero] at hq
  change a * q = 1 at hq
  have ha : a ≠ zeroValue M := by
    intro ha
    have he : (0 : M) = 1 := by
      rw [ha] at hq
      change (0 : M) * q = 1 at hq
      simpa only [zero_mul] using hq
    exact zero_ne_one he
  have hq0 : q ≠ zeroValue M := by
    intro hq0
    have he : (0 : M) = 1 := by
      rw [hq0] at hq
      change a * (0 : M) = 1 at hq
      simpa only [mul_zero] using hq
    exact zero_ne_one he
  have haq : a ≤ 1 := calc
    a = a * 1 := (mul_one _).symm
    _ ≤ a * q := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_value _)
      change leValue M (succValue M (zeroValue M)) q
      have hle := one_le_nonzero_model q hq0
      rw [numeral_value_succ, numeral_value_zero] at hle
      exact hle
    _ = 1 := hq
  rw [numeral_value_succ, numeral_value_zero]
  apply le_antisymm haq
  change leValue M (succValue M (zeroValue M)) a
  have hle := one_le_nonzero_model a ha
  rw [numeral_value_succ, numeral_value_zero] at hle
  exact hle

theorem coprime_product_model {M : Type u} [language.Structure M] [M ⊨ PA]
    (p q r : M) (hpq : CoprimeModel M p q) (hpr : CoprimeModel M p r) :
    CoprimeModel M p (mulValue M q r) := by
  intro a hap haqr
  have haq : CoprimeModel M a q := by
    intro d hda hdq
    exact hpq d (divides_trans_model hda hap) hdq
  exact hpr a hap (coprime_cancellation_model a q r haq haqr)

theorem coprime_succ_multiple_model {M : Type u} [language.Structure M] [M ⊨ PA]
    (d i : M) : CoprimeModel M (succValue M (mulValue M (succValue M i) d)) d := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  intro a ham had
  obtain ⟨q, hq⟩ := ham
  obtain ⟨r, hr⟩ := had
  have ha : a ≠ zeroValue M := by
    intro ha
    have he : zeroValue M = succValue M (mulValue M (succValue M i) d) := by
      simpa only [ha, zero_mul_value] using hq
    exact successor_ne_zero _ he.symm
  have he : a * q = 1 + a * ((i + 1) * r) := by
    calc
      _ = succValue M (mulValue M (succValue M i) d) := hq
      _ = (i + 1) * d + 1 := by rw [← add_one_value, ← add_one_value]; rfl
      _ = _ := by change a * r = d at hr; rw [← hr]; ring
  apply divisor_of_one_model a
  rw [numeral_value_succ, numeral_value_zero]
  have hdiv := quotient_of_difference a q ((i + 1) * r) 1 ha he
  change DividesModel M a (succValue M (zeroValue M)) at hdiv
  exact hdiv


end
end Lemmatheca.MathematicalLogic.PAComputations
