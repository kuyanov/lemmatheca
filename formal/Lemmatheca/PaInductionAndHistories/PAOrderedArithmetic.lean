import Lemmatheca.ArithmeticRepresentability.ArithmeticRepresentabilityBasic

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory

/-! Ordered arithmetic in every model of the corpus's actual PA theory.
All inductions below use a displayed formula of the shared first-order syntax.
No induction principle for arbitrary predicates on a nonstandard model is assumed.
-/
namespace Lemmatheca.ProofTheory.PAComputations

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open ArithmeticTheories ArithmeticRepresentability FirstOrderProofs

noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

local instance orderedArithmeticLocalInstance1 : Nonempty M := ⟨zeroValue M⟩

private theorem qfacts :
    (∀ a : M, succValue M a ≠ zeroValue M) ∧
    (∀ {a b : M}, succValue M a = succValue M b → a = b) ∧
    (∀ a : M, a ≠ zeroValue M → ∃ b, a = succValue M b) ∧
    (∀ a : M, addValue M a (zeroValue M) = a) ∧
    (∀ a b : M, addValue M a (succValue M b) = succValue M (addValue M a b)) ∧
    (∀ a : M, mulValue M a (zeroValue M) = zeroValue M) ∧
    (∀ a b : M, mulValue M a (succValue M b) =
      addValue M (mulValue M a b) a) :=
  (model_Q_iff M).mp (PA_models_Q M)

theorem successor_ne_zero (a : M) : succValue M a ≠ zeroValue M := qfacts.1 a
theorem successor_injective : Function.Injective (succValue M) := fun _ _ h => qfacts.2.1 h
theorem predecessor (a : M) (ha : a ≠ zeroValue M) : ∃ b, a = succValue M b :=
  qfacts.2.2.1 a ha
theorem add_zero_value (a : M) : addValue M a (zeroValue M) = a := qfacts.2.2.2.1 a
theorem add_successor_value (a b : M) :
    addValue M a (succValue M b) = succValue M (addValue M a b) := qfacts.2.2.2.2.1 a b
theorem mul_zero_value (a : M) : mulValue M a (zeroValue M) = zeroValue M :=
  qfacts.2.2.2.2.2.1 a
theorem mul_successor_value (a b : M) :
    mulValue M a (succValue M b) = addValue M (mulValue M a b) a :=
  qfacts.2.2.2.2.2.2 a b

/-- Definable induction, with an explicit realization equivalence. -/
theorem formula_induction {k : ℕ} (φ : language.Formula (Fin k ⊕ Unit))
    (v : Fin k → M) (P : M → Prop)
    (hφ : ∀ b, φ.Realize (Sum.elim v (fun _ => b)) ↔ P b)
    (hz : P (zeroValue M))
    (hs : ∀ b, P b → P (succValue M b)) : ∀ b, P b := by
  intro b
  exact (hφ b).mp (PA_induction M φ v ((hφ _).mpr hz)
    (fun c hc => (hφ _).mpr (hs c ((hφ c).mp hc))) b)

theorem zero_add_value (a : M) : addValue M (zeroValue M) a = a := by
  let φ : language.Formula (Fin 0 ⊕ Unit) :=
    (addTerm zeroTerm (.var (.inr ()))).equal (.var (.inr ()))
  apply formula_induction φ Fin.elim0 _ _ _ _ a
  · intro d
    simp [φ]
  · exact add_zero_value _
  · intro d hd
    rw [add_successor_value, hd]

theorem successor_add_value (a b : M) :
    addValue M (succValue M a) b = succValue M (addValue M a b) := by
  let φ : language.Formula (Fin 1 ⊕ Unit) :=
    (addTerm (succTerm (.var (.inl 0))) (.var (.inr ()))).equal
      (succTerm (addTerm (.var (.inl 0)) (.var (.inr ()))))
  apply formula_induction φ (fun _ => a) _ _ _ _ b
  · intro d
    simp [φ]
  · simp only [add_zero_value]
  · intro d hd
    simp only [add_successor_value, hd]

theorem add_comm_value (a b : M) : addValue M a b = addValue M b a := by
  let φ : language.Formula (Fin 1 ⊕ Unit) :=
    (addTerm (.var (.inl 0)) (.var (.inr ()))).equal
      (addTerm (.var (.inr ())) (.var (.inl 0)))
  apply formula_induction φ (fun _ => a) _ _ _ _ b
  · intro d
    simp [φ]
  · rw [add_zero_value, zero_add_value]
  · intro d hd
    rw [add_successor_value, successor_add_value, hd]

theorem add_assoc_value (a b c : M) :
    addValue M (addValue M a b) c = addValue M a (addValue M b c) := by
  let φ : language.Formula (Fin 2 ⊕ Unit) :=
    (addTerm (addTerm (.var (.inl 0)) (.var (.inl 1))) (.var (.inr ()))).equal
      (addTerm (.var (.inl 0)) (addTerm (.var (.inl 1)) (.var (.inr ()))))
  apply formula_induction φ ![a, b] _ _ _ _ c
  · intro d
    simp [φ]
  · simp only [add_zero_value]
  · intro d hd
    simp only [add_successor_value, hd]

theorem add_left_cancel_value (a b c : M)
    (h : addValue M a b = addValue M a c) : b = c := by
  let φ : language.Formula (Fin 2 ⊕ Unit) :=
    ((addTerm (.var (.inr ())) (.var (.inl 0))).equal
      (addTerm (.var (.inr ())) (.var (.inl 1)))).imp
      ((Term.var (.inl 0)).equal (.var (.inl 1)))
  have hi : ∀ d : M, addValue M d b = addValue M d c → b = c := by
    apply formula_induction φ ![b, c]
      (fun d => addValue M d b = addValue M d c → b = c) _ _ _
    · intro d
      simp [φ]
    · simpa only [zero_add_value] using (id : b = c → b = c)
    · intro d hd hh
      apply hd
      exact successor_injective (by simpa only [successor_add_value] using hh)
  exact hi a h

theorem add_right_cancel_value (a b c : M)
    (h : addValue M b a = addValue M c a) : b = c := by
  apply add_left_cancel_value a
  simpa only [add_comm_value] using h

theorem add_eq_zero_value {a b : M} (h : addValue M a b = zeroValue M) :
    a = zeroValue M ∧ b = zeroValue M := by
  by_cases ha : a = zeroValue M
  · exact ⟨ha, by simpa only [ha, zero_add_value] using h⟩
  · obtain ⟨a', rfl⟩ := predecessor a ha
    exact False.elim (successor_ne_zero _ (by simpa only [successor_add_value] using h))

/-- This structure uses exactly the addition and zero of the PA model. -/
abbrev modelAddCommMonoid (M : Type u) [language.Structure M] [M ⊨ PA] : AddCommMonoid M where
  zero := zeroValue M
  add := addValue M
  add_assoc := add_assoc_value
  zero_add := zero_add_value
  add_zero := add_zero_value
  add_comm := add_comm_value
  nsmul := fun n a => Nat.rec (zeroValue M) (fun _ b => addValue M b a) n

theorem zero_mul_value (a : M) : mulValue M (zeroValue M) a = zeroValue M := by
  let φ : language.Formula (Fin 0 ⊕ Unit) :=
    (mulTerm zeroTerm (.var (.inr ()))).equal zeroTerm
  apply formula_induction φ Fin.elim0 _ _ _ _ a
  · intro d
    simp [φ]
  · exact mul_zero_value _
  · intro d hd
    rw [mul_successor_value, hd, add_zero_value]

theorem successor_mul_value (a b : M) :
    mulValue M (succValue M a) b = addValue M (mulValue M a b) b := by
  let φ : language.Formula (Fin 1 ⊕ Unit) :=
    (mulTerm (succTerm (.var (.inl 0))) (.var (.inr ()))).equal
      (addTerm (mulTerm (.var (.inl 0)) (.var (.inr ()))) (.var (.inr ())))
  apply formula_induction φ (fun _ => a) _ _ _ _ b
  · intro d
    simp [φ]
  · simp only [mul_zero_value, add_zero_value]
  · intro d hd
    simp only [mul_successor_value, hd, add_successor_value]
    congr 1
    let := modelAddCommMonoid M
    change (mulValue M a d + d) + a = (mulValue M a d + a) + d
    ac_rfl

theorem mul_comm_value (a b : M) : mulValue M a b = mulValue M b a := by
  let φ : language.Formula (Fin 1 ⊕ Unit) :=
    (mulTerm (.var (.inl 0)) (.var (.inr ()))).equal
      (mulTerm (.var (.inr ())) (.var (.inl 0)))
  apply formula_induction φ (fun _ => a) _ _ _ _ b
  · intro d
    simp [φ]
  · rw [mul_zero_value, zero_mul_value]
  · intro d hd
    rw [mul_successor_value, successor_mul_value, hd]

theorem mul_add_value (a b c : M) :
    mulValue M a (addValue M b c) =
      addValue M (mulValue M a b) (mulValue M a c) := by
  let φ : language.Formula (Fin 2 ⊕ Unit) :=
    (mulTerm (.var (.inl 0)) (addTerm (.var (.inl 1)) (.var (.inr ())))).equal
      (addTerm (mulTerm (.var (.inl 0)) (.var (.inl 1)))
        (mulTerm (.var (.inl 0)) (.var (.inr ()))))
  apply formula_induction φ ![a, b] _ _ _ _ c
  · intro d
    simp [φ]
  · simp only [add_zero_value, mul_zero_value]
  · intro d hd
    rw [add_successor_value, mul_successor_value, hd, mul_successor_value,
      add_assoc_value]

theorem add_mul_value (a b c : M) :
    mulValue M (addValue M a b) c =
      addValue M (mulValue M a c) (mulValue M b c) := by
  rw [mul_comm_value, mul_add_value, mul_comm_value c a, mul_comm_value c b]

theorem mul_assoc_value (a b c : M) :
    mulValue M (mulValue M a b) c = mulValue M a (mulValue M b c) := by
  let φ : language.Formula (Fin 2 ⊕ Unit) :=
    (mulTerm (mulTerm (.var (.inl 0)) (.var (.inl 1))) (.var (.inr ()))).equal
      (mulTerm (.var (.inl 0)) (mulTerm (.var (.inl 1)) (.var (.inr ()))))
  apply formula_induction φ ![a, b] _ _ _ _ c
  · intro d
    simp [φ]
  · simp only [mul_zero_value]
  · intro d hd
    rw [mul_successor_value, hd, mul_successor_value, mul_add_value]

theorem add_one_value (a : M) :
    addValue M a (succValue M (zeroValue M)) = succValue M a := by
  rw [add_successor_value, add_zero_value]

theorem mul_one_value (a : M) : mulValue M a (succValue M (zeroValue M)) = a := by
  rw [mul_successor_value, mul_zero_value, zero_add_value]

theorem one_mul_value (a : M) : mulValue M (succValue M (zeroValue M)) a = a := by
  rw [mul_comm_value, mul_one_value]

/-- The semiring operations are the interpretation of the actual language symbols. -/
abbrev modelSemiring (M : Type u) [language.Structure M] [M ⊨ PA] : CommSemiring M where
  __ := modelAddCommMonoid M
  one := succValue M (zeroValue M)
  mul := mulValue M
  mul_assoc := mul_assoc_value
  one_mul := one_mul_value
  mul_one := mul_one_value
  zero_mul := zero_mul_value
  mul_zero := mul_zero_value
  left_distrib := mul_add_value
  right_distrib := add_mul_value
  mul_comm := mul_comm_value
  natCast := numeralValue M
  natCast_zero := numeral_value_zero M
  natCast_succ := fun n => (add_one_value (numeralValue M n)).symm

theorem le_refl_value (a : M) : leValue M a a :=
  ⟨zeroValue M, zero_add_value a⟩

theorem zero_le_value (a : M) : leValue M (zeroValue M) a :=
  ⟨a, add_zero_value a⟩

theorem le_trans_value {a b c : M} (hab : leValue M a b) (hbc : leValue M b c) :
    leValue M a c := by
  obtain ⟨d, rfl⟩ := hab
  obtain ⟨e, rfl⟩ := hbc
  exact ⟨addValue M e d, add_assoc_value _ _ _⟩

theorem le_antisymm_value {a b : M} (hab : leValue M a b) (hba : leValue M b a) : a = b := by
  obtain ⟨d, hd⟩ := hab
  obtain ⟨e, he⟩ := hba
  have hz : addValue M e d = zeroValue M := by
    apply add_right_cancel_value a
    rw [add_assoc_value, hd, he, zero_add_value]
  have hd0 := (add_eq_zero_value hz).2
  simpa only [hd0, zero_add_value] using hd

theorem le_successor_value (a : M) : leValue M a (succValue M a) :=
  ⟨succValue M (zeroValue M), by rw [successor_add_value, zero_add_value]⟩

theorem le_or_successor_le (a b : M) : leValue M a b ∨ leValue M (succValue M b) a := by
  let φ : language.Formula (Fin 1 ⊕ Unit) :=
    leFormula (.var (.inl 0)) (.var (.inr ())) ⊔
      leFormula (succTerm (.var (.inr ()))) (.var (.inl 0))
  apply formula_induction φ (fun _ => a) _ _ _ _ b
  · intro d
    simp only [φ, Formula.realize_sup, realize_leFormula, Term.realize_var,
      realize_succTerm, Sum.elim_inl, Sum.elim_inr]
  · by_cases ha : a = zeroValue M
    · exact Or.inl (ha ▸ le_refl_value _)
    · obtain ⟨a', rfl⟩ := predecessor a ha
      exact Or.inr ⟨a', add_one_value a'⟩
  · intro d hd
    rcases hd with hd | ⟨e, he⟩
    · exact Or.inl (le_trans_value hd (le_successor_value d))
    · by_cases he0 : e = zeroValue M
      · have hea : a = succValue M d := by simpa only [he0, zero_add_value] using he.symm
        exact Or.inl (hea ▸ le_refl_value (succValue M d))
      · obtain ⟨e', rfl⟩ := predecessor e he0
        exact Or.inr ⟨e', by simpa only [add_successor_value, successor_add_value] using he⟩

theorem le_total_value (a b : M) : leValue M a b ∨ leValue M b a := by
  rcases le_or_successor_le a b with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans_value (le_successor_value b) h)

/-- The order is the formula `∃d, d+a=b`, rather than an unrelated order on `M`. -/
abbrev modelLinearOrder (M : Type u) [language.Structure M] [M ⊨ PA] : LinearOrder M where
  le := leValue M
  le_refl := le_refl_value
  le_trans := fun _ _ _ => le_trans_value
  le_antisymm := fun _ _ => le_antisymm_value
  le_total := le_total_value
  toDecidableLE := Classical.decRel _

theorem successor_le_iff_lt (a b : M) :
    leValue M (succValue M a) b ↔ leValue M a b ∧ ¬ leValue M b a := by
  constructor
  · intro h
    refine ⟨le_trans_value (le_successor_value a) h, ?_⟩
    intro h'
    obtain ⟨d, hd⟩ := le_trans_value h h'
    have hz : succValue M d = zeroValue M := by
      apply add_right_cancel_value a
      simpa only [add_successor_value, successor_add_value, zero_add_value] using hd
    exact successor_ne_zero _ hz
  · rintro ⟨⟨d, hd⟩, hba⟩
    have hd0 : d ≠ zeroValue M := by
      intro hd0
      apply hba
      have hab : a = b := by simpa only [hd0, zero_add_value] using hd
      exact hab ▸ le_refl_value a
    obtain ⟨d', rfl⟩ := predecessor d hd0
    exact ⟨d', by simpa only [add_successor_value, successor_add_value] using hd⟩

theorem add_le_add_value {a b : M} (h : leValue M a b) (c : M) :
    leValue M (addValue M a c) (addValue M b c) := by
  obtain ⟨d, rfl⟩ := h
  exact ⟨d, (add_assoc_value _ _ _).symm⟩

theorem le_of_add_le_add_value (a b c : M)
    (h : leValue M (addValue M a b) (addValue M a c)) : leValue M b c := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, add_left_cancel_value a _ _ ?_⟩
  convert hd using 1
  let := modelAddCommMonoid M
  change a + (d + b) = d + (a + b)
  ac_rfl

theorem modelOrderedAdd (M : Type u) [language.Structure M] [M ⊨ PA] :
    let := modelSemiring M
    let := modelLinearOrder M
    IsOrderedCancelAddMonoid M := by
  let := modelSemiring M
  let := modelLinearOrder M
  exact { add_le_add_left := fun _ _ h c => add_le_add_value h c
          le_of_add_le_add_left := le_of_add_le_add_value }

theorem mul_le_mul_value {a b : M} (h : leValue M a b) (c : M) :
    leValue M (mulValue M c a) (mulValue M c b) := by
  obtain ⟨d, rfl⟩ := h
  exact ⟨mulValue M c d, (mul_add_value _ _ _).symm⟩

theorem mul_ne_zero_value {a b : M} (ha : a ≠ zeroValue M) (hb : b ≠ zeroValue M) :
    mulValue M a b ≠ zeroValue M := by
  obtain ⟨b', rfl⟩ := predecessor b hb
  intro h
  exact ha (add_eq_zero_value (by simpa only [mul_successor_value] using h)).2

theorem mul_lt_mul_value {a b : M}
    (h : leValue M a b ∧ ¬ leValue M b a) (c : M) (hc : c ≠ zeroValue M) :
    leValue M (mulValue M c a) (mulValue M c b) ∧
      ¬ leValue M (mulValue M c b) (mulValue M c a) := by
  refine ⟨mul_le_mul_value h.1 c, ?_⟩
  obtain ⟨d, hd⟩ := h.1
  have hd0 : d ≠ zeroValue M := by
    intro hd0
    apply h.2
    have hab : a = b := by simpa only [hd0, zero_add_value] using hd
    exact hab ▸ le_refl_value a
  intro hr
  have he := le_antisymm_value (mul_le_mul_value h.1 c) hr
  have hz : mulValue M c d = zeroValue M := by
    apply add_right_cancel_value (mulValue M c a)
    rw [zero_add_value, ← mul_add_value, hd, he]
  exact mul_ne_zero_value hc hd0 hz

theorem modelStrictOrderedRing (M : Type u) [language.Structure M] [M ⊨ PA] :
    let := modelSemiring M
    let := modelLinearOrder M
    IsStrictOrderedRing M := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  have hne : (0 : M) ≠ 1 := (successor_ne_zero (zeroValue M)).symm
  have hn : Nontrivial M := ⟨⟨0, 1, hne⟩⟩
  have hz : ZeroLEOneClass M := ⟨zero_le_value _⟩
  have hl : PosMulStrictMono M := ⟨fun a ha b c hbc =>
    mul_lt_mul_value hbc a (ne_of_gt ha)⟩
  have hr : MulPosStrictMono M := ⟨fun c hc a b hab => by
    change leValue M (mulValue M a c) (mulValue M b c) ∧
      ¬ leValue M (mulValue M b c) (mulValue M a c)
    simpa only [mul_comm_value] using mul_lt_mul_value hab c (ne_of_gt hc)⟩
  exact { toNontrivial := hn
          toZeroLEOneClass := hz
          toPosMulStrictMono := hl
          toMulPosStrictMono := hr }

private def divisionFormula : language.Formula (Fin 1 ⊕ Unit) :=
  (((Term.var (.inl (.inr ()))).equal
    (addTerm (mulTerm (.var (.inl (.inl 0))) (.var (.inr 0))) (.var (.inr 1)))) ⊓
    ltFormula (.var (.inr 1)) (.var (.inl (.inl 0)))).iExs (Fin 2)

omit [M ⊨ PA] in
private theorem divisionFormula_realize (m c : M) :
    divisionFormula.Realize (Sum.elim (fun _ => m) (fun _ => c)) ↔
      ∃ q r : M, c = addValue M (mulValue M m q) r ∧
        leValue M (succValue M r) m := by
  simp only [divisionFormula, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_equal, realize_addTerm, realize_mulTerm, ltFormula, realize_leFormula,
    realize_succTerm, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v 0, v 1, hv⟩
  · rintro ⟨q, r, h⟩
    exact ⟨![q, r], h⟩

/-- Division with remainder for arbitrary, including nonstandard, PA-model inputs. -/
theorem division_model (m : M) (hm : m ≠ zeroValue M) (c : M) :
    ∃! qr : M × M, c = addValue M (mulValue M m qr.1) qr.2 ∧
      leValue M (succValue M qr.2) m := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have hs (a : M) : succValue M a = a + 1 := (add_one_value a).symm
  have hz (a : M) : (0 : M) ≤ a := zero_le_value a
  have hmpos : (0 : M) < m := lt_of_le_of_ne (hz m) (Ne.symm hm)
  have hex : ∀ d : M, ∃ q r : M,
      d = addValue M (mulValue M m q) r ∧ leValue M (succValue M r) m := by
    apply formula_induction divisionFormula (fun _ => m) _
      (fun d => divisionFormula_realize m d)
    · refine ⟨0, 0, ?_, ?_⟩
      · exact (zero_add (0 : M)).symm.trans (congrArg (fun z : M => z + 0) (mul_zero m).symm)
      · exact (successor_le_iff_lt _ _).mpr hmpos
    · intro d hd
      obtain ⟨q, r, he, hr⟩ := hd
      change d = m * q + r at he
      have hr' : succValue M r ≤ m := hr
      rcases lt_or_eq_of_le hr' with hlt | heq
      · refine ⟨q, succValue M r, ?_, (successor_le_iff_lt _ _).mpr hlt⟩
        exact (congrArg (succValue M) he).trans (add_successor_value (mulValue M m q) r).symm
      · refine ⟨succValue M q, 0, ?_, (successor_le_iff_lt _ _).mpr hmpos⟩
        change succValue M d = addValue M (mulValue M m (succValue M q)) (zeroValue M)
        rw [add_zero_value, mul_successor_value]
        exact (congrArg (succValue M) he).trans
          ((add_successor_value (mulValue M m q) r).symm.trans
            (congrArg (addValue M (mulValue M m q)) heq))
  obtain ⟨q, r, he, hr⟩ := hex c
  refine ⟨(q, r), ⟨he, hr⟩, ?_⟩
  rintro ⟨q', r'⟩ ⟨he', hr'⟩
  change c = m * q + r at he
  change c = m * q' + r' at he'
  have hrl : r < m := (successor_le_iff_lt _ _).mp hr
  have hrl' : r' < m := (successor_le_iff_lt _ _).mp hr'
  have hnot (q r q' r' : M) (he : c = m * q + r) (he' : c = m * q' + r')
      (hr : r < m) : ¬ q < q' := by
    intro hq
    have hsq : succValue M q ≤ q' := (successor_le_iff_lt _ _).mpr hq
    have hc : c < c := calc
      c = m * q + r := he
      _ < m * q + m := add_lt_add_right hr _
      _ = m * succValue M q := (mul_successor_value m q).symm
      _ ≤ m * q' := mul_le_mul_value hsq m
      _ ≤ m * q' + r' := le_add_of_nonneg_right (hz r')
      _ = c := he'.symm
    exact (lt_irrefl c) hc
  have hq : q' = q := le_antisymm (le_of_not_gt (hnot q r q' r' he he' hrl))
    (le_of_not_gt (hnot q' r' q r he' he hrl'))
  have hrr : r' = r := by
    apply add_left_cancel (a := m * q)
    simpa only [hq] using he'.symm.trans he
  exact Prod.ext hq hrr

end
end Lemmatheca.ProofTheory.PAComputations
