import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

/-! Reusable ContinuumFunction definitions and results. -/

set_option autoImplicit false
universe u
namespace Lemmatheca.SetTheory.ContinuumFunction
open Order
open scoped Cardinal Ordinal

/-- Every infinite cardinal has the next cardinal as its power-set size. -/
def GCH : Prop := ∀ κ : Cardinal.{u}, ℵ₀ ≤ κ → 2 ^ κ = Order.succ κ

/-- GCH is equivalent to equality of the beth and aleph sequences. -/
theorem gch_iff_beth_aleph : GCH.{u} ↔ ∀ a : Ordinal.{u}, Cardinal.beth a = Cardinal.aleph a := by
  constructor
  · intro h
    have he : Cardinal.beth = Cardinal.aleph := by
      apply (Cardinal.isNormal_beth.ext_iff Cardinal.isNormal_aleph).mpr
      refine ⟨by simp, ?_⟩
      intro a hsame
      rw [Cardinal.beth_succ, hsame, h _ (Cardinal.aleph0_le_aleph a),
        Cardinal.succ_aleph, ← Order.succ_eq_add_one]
    exact congrFun he
  · intro h κ hi
    obtain ⟨a, rfl⟩ := Cardinal.mem_range_aleph_iff.mpr hi
    rw [← h a, ← Cardinal.beth_succ, h, h a, Cardinal.succ_aleph,
      ← Order.succ_eq_add_one]

/-- An infinite exponent absorbs every base between two and its binary power. -/
theorem large_exponents (κ τ : Cardinal.{u}) (hτ : ℵ₀ ≤ τ) (hκ : 2 ≤ κ)
    (hupper : κ ≤ 2 ^ τ) : κ ^ τ = 2 ^ τ := by
  apply le_antisymm
  · calc
      κ ^ τ ≤ (2 ^ τ) ^ τ := Cardinal.power_le_power_right hupper
      _ = 2 ^ (τ * τ) := Cardinal.power_mul.symm
      _ = 2 ^ τ := by rw [Cardinal.mul_eq_self hτ]
  · exact Cardinal.power_le_power_right hκ

/-- Count functions by a strict bound on their range and the functions below each bound. -/
private theorem bounded_function_count {α β : Type u} [LinearOrder α]
    (hcf : Cardinal.mk β < Order.cof α) (c : Cardinal.{u})
    (hpower : ∀ a : α, Cardinal.mk (Set.Iio a) ^ Cardinal.mk β ≤ c) :
    Cardinal.mk (β → α) ≤ Cardinal.mk α * c := by
  classical
  have hbound (f : β → α) : ∃ a, ∀ b, f b < a := by
    have hn : ¬ IsCofinal (Set.range f) := by
      intro h
      exact hcf.not_ge ((Order.cof_le h).trans Cardinal.mk_range_le)
    obtain ⟨a, ha⟩ := not_isCofinal_iff.mp hn
    exact ⟨a, fun b => ha (f b) ⟨b, rfl⟩⟩
  let code : (β → α) → Σ a : α, β → Set.Iio a :=
    fun f => ⟨(hbound f).choose, fun b => ⟨f b, (hbound f).choose_spec b⟩⟩
  have hi : Function.Injective code := by
    intro f g h
    have hval := congrArg (fun p : Σ a : α, β → Set.Iio a => fun b => (p.2 b).val) h
    exact hval
  calc
    Cardinal.mk (β → α) ≤ Cardinal.mk (Σ a : α, β → Set.Iio a) := Cardinal.mk_le_of_injective hi
    _ = Cardinal.sum (fun a : α => Cardinal.mk (Set.Iio a) ^ Cardinal.mk β) := by
      simp only [Cardinal.mk_sigma, Cardinal.mk_arrow, Cardinal.lift_id]
    _ ≤ Cardinal.sum (fun _ : α => c) := Cardinal.sum_le_sum _ _ hpower
    _ = Cardinal.mk α * c := by rw [Cardinal.sum_const, Cardinal.lift_id, Cardinal.lift_id]

private theorem initial_segment_card_lt (κ : Cardinal.{u}) (a : κ.ord.ToType) :
    Cardinal.mk (Set.Iio a) < κ := by
  have he : (Cardinal.mk κ.ord.ToType).ord = Ordinal.type ((· < ·) : κ.ord.ToType → κ.ord.ToType → Prop) := by
    rw [Cardinal.mk_toType, Cardinal.card_ord, Ordinal.type_toType]
  simpa only [Cardinal.mk_toType, Cardinal.card_ord] using Cardinal.mk_Iio_lt a he

private theorem bounded_power_le (κ τ c : Cardinal.{u}) (hcf : τ < κ.ord.cof)
    (hpower : ∀ μ < κ, μ ^ τ ≤ c) : κ ^ τ ≤ κ * c := by
  have hcf' : Cardinal.mk τ.out < Order.cof κ.ord.ToType := by
    rwa [Cardinal.mk_out, ← Ordinal.cof_type, Ordinal.type_toType]
  have hbound := bounded_function_count hcf' c (fun a =>
    by simpa only [Cardinal.mk_out] using hpower _ (initial_segment_card_lt κ a))
  simpa only [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.mk_out, Cardinal.mk_toType,
    Cardinal.card_ord] using hbound

/-- Cofinal restrictions, with an outside marker, determine a function. -/
private theorem cofinal_power_bound (κ τ : Cardinal.{u}) (hi : ℵ₀ ≤ κ)
    (hsmall : ∀ μ < κ, μ ^ τ ≤ κ) : κ ^ τ ≤ κ ^ κ.ord.cof := by
  classical
  let A := κ.ord.ToType
  obtain ⟨S, hS, hcard⟩ := Order.exists_cof_eq (α := A)
  let code : (τ.out → A) → ((i : S) → τ.out → Option (Set.Iic i.val)) :=
    fun f i b => if h : f b ≤ i.val then some ⟨f b, h⟩ else none
  have hinj : Function.Injective code := by
    intro f g he
    funext b
    obtain ⟨i, hiS, hfi⟩ := hS (max (f b) (g b))
    have hfa : f b ≤ i := (le_max_left _ _).trans hfi
    have hga : g b ≤ i := (le_max_right _ _).trans hfi
    have hc := congrFun (congrFun he ⟨i, hiS⟩) b
    dsimp only [code] at hc
    simp only [hfa, hga, dite_true] at hc
    exact congrArg (fun z : Set.Iic i => z.val) (Option.some.inj hc)
  have hcoord : ∀ i : S, Cardinal.mk (τ.out → Option (Set.Iic i.val)) ≤ κ := by
    intro i
    have hIio := initial_segment_card_lt κ i.val
    have hone : (1 : Cardinal.{u}) < κ := Cardinal.one_lt_aleph0.trans_le hi
    have hIic : Cardinal.mk (Set.Iic i.val) < κ := by
      have he : Set.Iic i.val = insert i.val (Set.Iio i.val) := by
        ext x
        simp only [Set.mem_Iic, Set.mem_insert_iff, Set.mem_Iio]
        exact le_iff_eq_or_lt
      rw [he]
      exact Cardinal.mk_insert_le.trans_lt (Cardinal.add_lt_of_lt hi hIio hone)
    have hopt : Cardinal.mk (Option (Set.Iic i.val)) < κ := by
      rw [Cardinal.mk_option]
      exact Cardinal.add_lt_of_lt hi hIic hone
    simpa only [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.mk_out] using hsmall _ hopt
  calc
    κ ^ τ = Cardinal.mk (τ.out → A) := by
      simp only [A, Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.mk_out,
        Cardinal.mk_toType, Cardinal.card_ord]
    _ ≤ Cardinal.mk ((i : S) → τ.out → Option (Set.Iic i.val)) := Cardinal.mk_le_of_injective hinj
    _ = Cardinal.prod (fun i : S => Cardinal.mk (τ.out → Option (Set.Iic i.val))) := Cardinal.mk_pi _
    _ ≤ Cardinal.prod (fun _ : S => κ) := Cardinal.prod_le_prod _ _ hcoord
    _ = κ ^ κ.ord.cof := by
      rw [Cardinal.prod_const, Cardinal.lift_id, Cardinal.lift_id, hcard]
      congr 1
      rw [← Ordinal.cof_type, Ordinal.type_toType]

/-- Hausdorff's formula for an infinite successor base and an infinite exponent. -/
theorem hausdorff_formula (κ τ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hτ : ℵ₀ ≤ τ) :
    (Order.succ κ) ^ τ = κ ^ τ * Order.succ κ := by
  have hsucc : ℵ₀ ≤ Order.succ κ := hκ.trans (Order.le_succ κ)
  by_cases hτκ : Order.succ κ ≤ τ
  · have htwo : 2 ≤ κ := Cardinal.natCast_le_aleph0.trans hκ
    have hk := large_exponents κ τ hτ htwo ((Order.le_succ κ).trans hτκ |>.trans (Cardinal.cantor τ).le)
    have hs := large_exponents (Order.succ κ) τ hτ (htwo.trans (Order.le_succ κ))
      (hτκ.trans (Cardinal.cantor τ).le)
    rw [hk, hs]
    exact (Cardinal.mul_eq_left (hτ.trans (Cardinal.cantor τ).le)
      (hτκ.trans (Cardinal.cantor τ).le) (Cardinal.aleph0_pos.trans_le hsucc).ne').symm
  · have hcf : τ < (Order.succ κ).ord.cof := by
      rw [(Cardinal.isRegular_succ hκ).cof_ord]
      exact lt_of_not_ge hτκ
    apply le_antisymm
    · have hb := bounded_power_le (Order.succ κ) τ (κ ^ τ) hcf (fun μ hμ =>
        Cardinal.power_le_power_right (Order.le_of_lt_succ hμ))
      exact hb.trans_eq (mul_comm _ _)
    · rw [Cardinal.mul_eq_max (hκ.trans (Cardinal.self_le_power κ
        (Cardinal.one_lt_aleph0.le.trans hτ))) hsucc]
      apply max_le
      · exact Cardinal.power_le_power_right (Order.le_succ κ)
      · exact Cardinal.self_le_power _ (Cardinal.one_lt_aleph0.le.trans hτ)

/-- When a smaller base has power at least kappa, its power equals kappa's power. -/
theorem smaller_base_reduction (κ τ μ : Cardinal.{u}) (hτ : ℵ₀ ≤ τ)
    (hμ : μ < κ) (hpower : κ ≤ μ ^ τ) : κ ^ τ = μ ^ τ := by
  apply le_antisymm
  · calc
      κ ^ τ ≤ (μ ^ τ) ^ τ := Cardinal.power_le_power_right hpower
      _ = μ ^ (τ * τ) := Cardinal.power_mul.symm
      _ = μ ^ τ := by rw [Cardinal.mul_eq_self hτ]
  · exact Cardinal.power_le_power_right hμ.le

/-- Below cofinality, small powers of all smaller bases force the power to equal the base. -/
theorem power_below_cofinality (κ τ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hτ : ℵ₀ ≤ τ)
    (hsmall : ∀ μ < κ, μ ^ τ < κ) (hcf : τ < κ.ord.cof) : κ ^ τ = κ := by
  apply le_antisymm
  · exact (bounded_power_le κ τ κ hcf (fun μ hμ => (hsmall μ hμ).le)).trans
      (Cardinal.mul_eq_self hκ).le
  · exact Cardinal.self_le_power κ (Cardinal.one_lt_aleph0.le.trans hτ)

/-- At or above cofinality, small powers of all smaller bases reduce to the cofinal power. -/
theorem power_at_cofinality (κ τ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (_hτ : ℵ₀ ≤ τ)
    (hsmall : ∀ μ < κ, μ ^ τ < κ) (hcf : κ.ord.cof ≤ τ) : κ ^ τ = κ ^ κ.ord.cof := by
  apply le_antisymm
  · exact cofinal_power_bound κ τ hκ (fun μ hμ => (hsmall μ hμ).le)
  · exact Cardinal.power_le_power_left (Cardinal.aleph0_pos.trans_le hκ).ne' hcf

/-- GCH determines powers by the three cofinality cases. -/
theorem gch_powers (h : GCH.{u}) (κ τ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hτ : ℵ₀ ≤ τ) :
    κ ^ τ = if κ ≤ τ then Order.succ τ else
      if τ < κ.ord.cof then κ else Order.succ κ := by
  have htwo : 2 ≤ κ := Cardinal.natCast_le_aleph0.trans hκ
  by_cases hκτ : κ ≤ τ
  · rw [ite_eq_left hκτ, large_exponents κ τ hτ htwo (hκτ.trans (Cardinal.cantor τ).le), h τ hτ]
  · rw [ite_eq_right hκτ]
    have hτκ : τ < κ := lt_of_not_ge hκτ
    have hupper : κ ^ τ ≤ Order.succ κ := by
      calc
        κ ^ τ ≤ κ ^ κ := Cardinal.power_le_power_left (Cardinal.aleph0_pos.trans_le hκ).ne' hτκ.le
        _ = 2 ^ κ := Cardinal.power_self_eq hκ
        _ = Order.succ κ := h κ hκ
    by_cases hcf : τ < κ.ord.cof
    · rw [ite_eq_left hcf]
      apply le_antisymm
      · have hsmall : ∀ μ < κ, μ ^ τ ≤ κ := by
          intro μ hμ
          let θ := max μ τ
          have hi : ℵ₀ ≤ θ := hτ.trans (le_max_right _ _)
          have hθκ : θ < κ := max_lt hμ hτκ
          calc
            μ ^ τ ≤ (2 ^ θ) ^ τ := Cardinal.power_le_power_right
              ((le_max_left μ τ).trans (Cardinal.cantor θ).le)
            _ = 2 ^ (θ * τ) := Cardinal.power_mul.symm
            _ = 2 ^ θ := by rw [Cardinal.mul_eq_left hi (le_max_right _ _) (Cardinal.aleph0_pos.trans_le hτ).ne']
            _ = Order.succ θ := h θ hi
            _ ≤ κ := Order.succ_le_of_lt hθκ
        exact (bounded_power_le κ τ κ hcf hsmall).trans_eq (Cardinal.mul_eq_self hκ)
      · exact Cardinal.self_le_power κ (Cardinal.one_lt_aleph0.le.trans hτ)
    · rw [ite_eq_right hcf]
      apply le_antisymm hupper
      apply Order.succ_le_of_lt
      exact (Cardinal.lt_power_cof_ord hκ).trans_le
        (Cardinal.power_le_power_left (Cardinal.aleph0_pos.trans_le hκ).ne' (le_of_not_gt hcf))

/-- SCH fixes the cofinal power of singular cardinals when the smaller binary power is below the base. -/
def SCH : Prop := ∀ κ : Cardinal.{u}, ℵ₀ ≤ κ → κ.ord.cof < κ →
  2 ^ κ.ord.cof < κ → κ ^ κ.ord.cof = Order.succ κ

/-- GCH implies SCH. -/
theorem gch_implies_sch : GCH.{u} → SCH.{u} := by
  intro h κ hi hs hp
  have he := gch_powers h κ κ.ord.cof hi
    (Ordinal.aleph0_le_cof_iff.mpr
      (Ordinal.one_lt_cof_iff.mpr (Cardinal.isSuccLimit_ord hi)))
  simpa only [not_le_of_gt hs, ite_false, lt_self_iff_false] using he

/-- A singular strong limit has binary power equal to its cofinal power. -/
theorem strong_limit_cofinal_power (κ : Cardinal.{u}) (hi : ℵ₀ ≤ κ)
    (hs : κ.ord.cof < κ) (hstrong : Cardinal.IsStrongLimit κ) : 2 ^ κ = κ ^ κ.ord.cof := by
  classical
  let A := κ.ord.ToType
  obtain ⟨S, hS, hcard⟩ := Order.exists_cof_eq (α := A)
  let code : (A → ULift.{u} Bool) → ((i : S) → Set.Iic i.val → ULift.{u} Bool) := fun f _ a => f a.val
  have hinj : Function.Injective code := by
    intro f g he
    funext a
    obtain ⟨i, hiS, hai⟩ := hS a
    exact congrFun (congrFun he ⟨i, hiS⟩) ⟨a, hai⟩
  have hcoord : ∀ i : S, Cardinal.mk (Set.Iic i.val → ULift.{u} Bool) ≤ κ := by
    intro i
    have hIio := initial_segment_card_lt κ i.val
    have hone : (1 : Cardinal.{u}) < κ := Cardinal.one_lt_aleph0.trans_le hi
    have hIic : Cardinal.mk (Set.Iic i.val) < κ := by
      have he : Set.Iic i.val = insert i.val (Set.Iio i.val) := by
        ext x
        simp only [Set.mem_Iic, Set.mem_insert_iff, Set.mem_Iio]
        exact le_iff_eq_or_lt
      rw [he]
      exact Cardinal.mk_insert_le.trans_lt (Cardinal.add_lt_of_lt hi hIio hone)
    simpa only [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.mk_uLift, Cardinal.mk_bool, Cardinal.lift_two] using
      (hstrong.2 hIic).le
  have hupper : 2 ^ κ ≤ κ ^ κ.ord.cof := by
    calc
      2 ^ κ = Cardinal.mk (A → ULift.{u} Bool) := by
        simp only [A, Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.mk_uLift, Cardinal.mk_bool,
          Cardinal.lift_two, Cardinal.mk_toType, Cardinal.card_ord]
      _ ≤ Cardinal.mk ((i : S) → Set.Iic i.val → ULift.{u} Bool) := Cardinal.mk_le_of_injective hinj
      _ = Cardinal.prod (fun i : S => Cardinal.mk (Set.Iic i.val → ULift.{u} Bool)) := Cardinal.mk_pi _
      _ ≤ Cardinal.prod (fun _ : S => κ) := Cardinal.prod_le_prod _ _ hcoord
      _ = κ ^ κ.ord.cof := by
        rw [Cardinal.prod_const, Cardinal.lift_id, Cardinal.lift_id, hcard]
        congr 1
        rw [← Ordinal.cof_type, Ordinal.type_toType]
  apply le_antisymm hupper
  calc
    κ ^ κ.ord.cof ≤ κ ^ κ := Cardinal.power_le_power_left (Cardinal.aleph0_pos.trans_le hi).ne' hs.le
    _ = 2 ^ κ := Cardinal.power_self_eq hi

/-- Under SCH the power set of a singular strong limit has successor size. -/
theorem sch_strong_limit (h : SCH.{u}) (κ : Cardinal.{u}) (hi : ℵ₀ ≤ κ)
    (hs : κ.ord.cof < κ) (hstrong : Cardinal.IsStrongLimit κ) : 2 ^ κ = Order.succ κ := by
  rw [strong_limit_cofinal_power κ hi hs hstrong]
  exact h κ hi hs (hstrong.2 hs)

/-- Without GCH aleph one's countable power is the continuum. -/
theorem aleph_one_countable_power :
    (Cardinal.aleph 1 : Cardinal.{u}) ^ ℵ₀ = 2 ^ (ℵ₀ : Cardinal.{u}) := by
  apply large_exponents _ _ le_rfl
  · exact Cardinal.natCast_le_aleph0.trans (Cardinal.aleph0_le_aleph 1)
  · simpa only [Cardinal.two_power_aleph0] using Cardinal.aleph_one_le_continuum

end Lemmatheca.SetTheory.ContinuumFunction
