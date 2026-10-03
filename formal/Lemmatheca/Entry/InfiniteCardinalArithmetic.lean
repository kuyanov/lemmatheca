import Lemmatheca.SetTheory.Choice
import Lemmatheca.Entry.FiniteAndCountableSets
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Analysis.SpecificLimits.Basic

/-! Explicit witnesses for infinite arithmetic. The square order compares
(maximum, first coordinate, second coordinate) lexicographically.
The witnesses below include their boundary and convergence arguments. -/
namespace Lemmatheca.Entry.InfiniteCardinalArithmetic
open Set Function Ordinal Order
open scoped Ordinal
universe u

/-- Move the new final point to zero, shift finite positions, and fix all others. -/
noncomputable def successorShift (a b : Ordinal.{u}) : Ordinal.{u} :=
  if b = a then 0 else if b < ω then b + 1 else b

theorem successorShift_bijection (a : Ordinal.{u}) (ha : ω ≤ a) :
    Set.BijOn (successorShift a) (Set.Iio (a + 1)) (Set.Iio a) := by
  classical
  have ha0 : 0 < a := Ordinal.omega0_pos.trans_le ha
  have hfin (b : Ordinal.{u}) (hb : b < ω) : b + 1 < ω := by
    simpa only [Order.succ_eq_add_one] using Ordinal.isSuccLimit_omega0.succ_lt hb
  have hpos (b : Ordinal.{u}) : 0 < b + 1 := (zero_le : 0 ≤ b).trans_lt (lt_add_one b)
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    change b < a + 1 at hb
    change successorShift a b < a
    dsimp [successorShift]
    split_ifs with hba hbw
    · exact ha0
    · exact (hfin b hbw).trans_le ha
    · exact lt_of_le_of_ne (lt_add_one_iff.mp hb) hba
  · intro b _ c _ he
    have hnz (x : Ordinal.{u}) (hxa : x ≠ a) : successorShift a x ≠ 0 := by
      dsimp [successorShift]
      rw [ite_eq_right hxa]
      split_ifs with hx
      · exact (hpos x).ne'
      · exact ((Ordinal.omega0_pos.trans_le (le_of_not_gt hx))).ne'
    by_cases hba : b = a
    · subst b
      by_contra hca
      apply hnz c (Ne.symm hca)
      simpa [successorShift] using he.symm
    by_cases hca : c = a
    · subst c
      exact False.elim (hnz b hba (by simpa [successorShift] using he))
    simp only [successorShift, ite_eq_right hba, ite_eq_right hca] at he
    by_cases hbw : b < ω <;> by_cases hcw : c < ω
    · simp only [ite_eq_left hbw, ite_eq_left hcw] at he
      exact succ_injective (by simpa only [Order.succ_eq_add_one] using he)
    · simp only [ite_eq_left hbw, ite_eq_right hcw] at he
      exact False.elim (hcw (he ▸ hfin b hbw))
    · simp only [ite_eq_right hbw, ite_eq_left hcw] at he
      exact False.elim (hbw (he.symm ▸ hfin c hcw))
    · simpa only [ite_eq_right hbw, ite_eq_right hcw] using he
  · intro b hb
    change b < a at hb
    by_cases hbw : b < ω
    · obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hbw
      cases n with
      | zero =>
        refine ⟨a, lt_add_one a, ?_⟩
        simp [successorShift]
      | succ n =>
        refine ⟨(n : Ordinal.{u}), (Ordinal.natCast_lt_omega0 n).trans_le (ha.trans (lt_add_one a).le), ?_⟩
        simp [successorShift, ((Ordinal.natCast_lt_omega0 n).trans_le ha).ne, Ordinal.natCast_lt_omega0,
          Nat.cast_add_one]
    · refine ⟨b, hb.trans (lt_add_one a), ?_⟩
      simp [successorShift, hb.ne, hbw]

/-- The maximum is the primary key; the two coordinates break ties. -/
def squareLT {α : Type u} [LinearOrder α] (p q : α × α) : Prop :=
  Prod.Lex ((· < ·) : α → α → Prop)
    (Prod.Lex ((· < ·) : α → α → Prop) ((· < ·) : α → α → Prop))
    (max p.1 p.2, p) (max q.1 q.2, q)

theorem squareLT_wellOrder {α : Type u} [LinearOrder α] [WellFoundedLT α] :
    IsWellOrder (α × α) squareLT := by
  let e : α × α ↪ α ×ₗ (α ×ₗ α) :=
    ⟨fun p => toLex (max p.1 p.2, toLex p), fun p q h => congrArg Prod.snd h⟩
  exact (RelEmbedding.preimage e (· < ·)).isWellOrder

theorem squareLT_predecessors {α : Type u} [LinearOrder α] (p q : α × α)
    (hp : squareLT p q) : p.1 ≤ max q.1 q.2 ∧ p.2 ≤ max q.1 q.2 := by
  simp only [squareLT, Prod.lex_iff] at hp
  have hm : max p.1 p.2 ≤ max q.1 q.2 := by rcases hp with h | ⟨h, _⟩ <;> order
  exact ⟨(le_max_left _ _).trans hm, (le_max_right _ _).trans hm⟩

/-- The small domain keeps ranks in the cardinal's original universe. -/
noncomputable def squareRank (c : Cardinal.{u})
    (h : IsWellOrder (c.ord.ToType × c.ord.ToType) squareLT)
    (p : c.ord.ToType × c.ord.ToType) : Ordinal.{u} :=
  @Ordinal.typein (c.ord.ToType × c.ord.ToType) squareLT h p

theorem squareRank_injection (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : IsWellOrder (c.ord.ToType × c.ord.ToType) squareLT) :
    Function.Injective (squareRank c h) ∧ ∀ p, squareRank c h p < c.ord := by
  letI := h
  refine ⟨Ordinal.typein_injective squareLT, ?_⟩
  intro p
  have : NoMaxOrder c.ord.ToType := by
    rw [← isSuccPrelimit_type_lt_iff, Ordinal.type_toType]
    exact (Cardinal.isSuccLimit_ord hc).isSuccPrelimit
  obtain ⟨q, hq⟩ := exists_gt (max p.1 p.2)
  rw [Cardinal.lt_ord]
  change (Ordinal.typein squareLT p).card < c
  rw [Ordinal.card_typein]
  let e : {x // squareLT x p} ↪ Set.Iio q × Set.Iio q :=
    ⟨fun x => (⟨x.val.1, (squareLT_predecessors x.val p x.property).1.trans_lt hq⟩,
      ⟨x.val.2, (squareLT_predecessors x.val p x.property).2.trans_lt hq⟩),
      fun x y he => Subtype.ext (Prod.ext
        (congrArg (fun z => z.1.val) he) (congrArg (fun z => z.2.val) he))⟩
  apply e.cardinal_le.trans_lt
  rw [Cardinal.mk_prod]
  simp only [Cardinal.lift_id]
  have hsmall : Cardinal.mk (Set.Iio q) < c := by
    simpa using Cardinal.mk_Iio_lt q (by simp [Cardinal.mk_toType, Ordinal.type_toType])
  exact Cardinal.mul_lt_of_lt hc hsmall hsmall

/-- Finite shell ranks displayed in the figure. -/
def shellRank (p : ℕ × ℕ) : ℕ :=
  let m := max p.1 p.2
  m * m + if p.1 < m then p.1 else m + p.2

private theorem shellRank_bounds (p : ℕ × ℕ) :
    (max p.1 p.2) * (max p.1 p.2) ≤ shellRank p ∧
    shellRank p < (max p.1 p.2 + 1) * (max p.1 p.2 + 1) := by
  have h1 := le_max_left p.1 p.2
  have h2 := le_max_right p.1 p.2
  dsimp [shellRank]
  split_ifs <;> constructor <;> nlinarith

private theorem shellRank_strict (p q : ℕ × ℕ) (h : max p.1 p.2 < max q.1 q.2) :
    shellRank p < shellRank q := by
  have hp := (shellRank_bounds p).2
  have hq := (shellRank_bounds q).1
  have hs : max p.1 p.2 + 1 ≤ max q.1 q.2 := h
  exact hp.trans_le ((Nat.mul_self_le_mul_self hs).trans hq)

theorem shellRank_order_iso :
    Function.Bijective shellRank ∧
    ∀ p q : ℕ × ℕ, squareLT p q ↔ shellRank p < shellRank q := by
  have ho : ∀ p q : ℕ × ℕ, squareLT p q ↔ shellRank p < shellRank q := by
    intro p q
    by_cases hpq : max p.1 p.2 < max q.1 q.2
    · exact ⟨fun _ => shellRank_strict p q hpq, fun _ => Prod.Lex.left _ _ hpq⟩
    by_cases hqp : max q.1 q.2 < max p.1 p.2
    · have hn := (shellRank_strict q p hqp).not_gt
      simp only [squareLT, Prod.lex_iff]
      constructor
      · rintro (h | ⟨h, _⟩) <;> omega
      · exact fun h => False.elim (hn h)
    have hm : max p.1 p.2 = max q.1 q.2 := by omega
    have hp1 := le_max_left p.1 p.2
    have hp2 := le_max_right p.1 p.2
    have hq1 := le_max_left q.1 q.2
    have hq2 := le_max_right q.1 q.2
    have hpe : p.1 = max p.1 p.2 ∨ p.2 = max p.1 p.2 := by omega
    have hqe : q.1 = max q.1 q.2 ∨ q.2 = max q.1 q.2 := by omega
    simp only [squareLT, Prod.lex_iff, hm, lt_self_iff_false, false_or, true_and, shellRank]
    split_ifs <;> omega
  refine ⟨⟨?_, ?_⟩, ho⟩
  · intro p q he
    haveI := squareLT_wellOrder (α := ℕ)
    rcases trichotomous_of squareLT p q with h | h | h
    · exact False.elim ((ho p q).mp h |>.ne he)
    · exact h
    · exact False.elim ((ho q p).mp h |>.ne he.symm)
  · intro n
    let m := n.sqrt
    let d := n - m * m
    have hlow : m * m ≤ n := Nat.sqrt_le n
    have hupp : n ≤ m * m + m + m := Nat.sqrt_le_add n
    have hd : d ≤ m + m := by dsimp [d]; omega
    by_cases hdm : d < m
    · refine ⟨(d, m), ?_⟩
      simp only [shellRank, max_eq_right hdm.le, ite_eq_left hdm]
      dsimp [d]
      omega
    · have hsub : d - m ≤ m := by omega
      refine ⟨(m, d - m), ?_⟩
      simp only [shellRank, max_eq_left hsub, lt_self_iff_false, ite_false]
      dsimp [d] at *
      omega

theorem shellRank_figure :
    (List.range 5).map (fun i => (List.range 5).map (fun j => shellRank (i, j))) =
      [[0, 1, 4, 9, 16], [2, 3, 5, 10, 17], [6, 7, 8, 11, 18],
       [12, 13, 14, 15, 19], [20, 21, 22, 23, 24]] := by decide +kernel

/-- Use the least containing index and that set's supplied encoding. -/
noncomputable def unionCode {α : Type u} (A : ℕ → Set α)
    (e : ∀ n, A n → ℕ) (x : ⋃ n, A n) : ℕ × ℕ := by
  classical
  let hx : ∃ n, x.val ∈ A n := Set.mem_iUnion.mp x.property
  let n := Nat.find hx
  exact (n, e n ⟨x.val, Nat.find_spec hx⟩)

theorem unionCode_injective {α : Type u} (A : ℕ → Set α) (e : ∀ n, A n → ℕ)
    (he : ∀ n, Function.Injective (e n)) : Function.Injective (unionCode A e) := by
  classical
  intro x y h
  have hi := congrArg Prod.fst h
  have hj := congrArg Prod.snd h
  dsimp [unionCode] at hi hj
  have hv : ∀ i j (hx : x.val ∈ A i) (hy : y.val ∈ A j),
      i = j → e i ⟨x.val, hx⟩ = e j ⟨y.val, hy⟩ → x.val = y.val := by
    intro i j hx hy hij heq
    subst j
    exact congrArg (fun z : A i => z.val) (he i heq)
  exact Subtype.ext (hv _ _ _ _ hi hj)

/-- Which enumerated rationals lie below the real number? -/
def rationalCut (x : ℝ) : Set ℕ :=
  {n | (Lemmatheca.Entry.FiniteAndCountableSets.rationalList n : ℝ) < x}

theorem rationalCut_injective : Function.Injective rationalCut := by
  intro x y he
  have hle (x y : ℝ) (he : rationalCut x = rationalCut y) : x ≤ y := by
    by_contra h
    obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn (lt_of_not_ge h)
    obtain ⟨n, rfl⟩ := Lemmatheca.Entry.FiniteAndCountableSets.rationalList_surjective q
    have hn : n ∈ rationalCut x := hqx
    rw [he] at hn
    exact hyq.not_gt hn
  exact le_antisymm (hle x y he) (hle y x he.symm)

/-- The explicit rational between x and y in the density argument. -/
theorem separating_rational (x y : ℝ) (hxy : x < y) (n : ℕ)
    (hn : 1 < (n : ℝ) * (y - x)) :
    let q : ℚ := ((Int.floor ((n : ℝ) * x) + 1 : ℤ) : ℚ) / (n : ℚ)
    x < (q : ℝ) ∧ (q : ℝ) < y := by
  have hn0 : (0 : ℝ) < n := by
    have : n ≠ 0 := by intro h; subst n; norm_num at hn
    exact_mod_cast Nat.pos_of_ne_zero this
  dsimp
  push_cast
  constructor
  · apply (lt_div_iff₀ hn0).mpr
    simpa [mul_comm] using Int.lt_floor_add_one ((n : ℝ) * x)
  · apply (div_lt_iff₀ hn0).mpr
    have hf := Int.floor_le ((n : ℝ) * x)
    nlinarith

noncomputable def ternaryTerm (S : Set ℕ) (n : ℕ) : ℝ :=
  @ite ℝ (n ∈ S) (Classical.propDecidable _) (2 / (3 : ℝ) ^ (n + 1)) 0

noncomputable def ternaryCode (S : Set ℕ) : ℝ := ∑' n, ternaryTerm S n

private theorem ternaryGeometric (k : ℕ) :
    HasSum (fun n : ℕ => (2 : ℝ) / 3 ^ (n + k + 1)) ((1 : ℝ) / 3 ^ k) := by
  have h := (hasSum_geometric_of_lt_one (r := (1 : ℝ) / 3)
    (by norm_num) (by norm_num)).mul_left ((2 : ℝ) / 3 ^ (k + 1))
  convert h using 1
  · funext n
    simp only [div_pow, one_pow, pow_add, pow_one]
    ring
  · simp only [pow_succ]
    ring

private theorem ternaryTerm_nonneg (S : Set ℕ) (n : ℕ) : 0 ≤ ternaryTerm S n := by
  unfold ternaryTerm
  split_ifs <;> positivity

private theorem ternaryTerm_bound (S : Set ℕ) (n : ℕ) : ternaryTerm S n ≤ 2 / 3 ^ (n + 1) := by
  unfold ternaryTerm
  split_ifs <;> first | rfl | positivity

private theorem ternaryTerm_summable (S : Set ℕ) : Summable (ternaryTerm S) :=
  Summable.of_nonneg_of_le (ternaryTerm_nonneg S) (ternaryTerm_bound S)
    (by simpa using (ternaryGeometric 0).summable)

private theorem ternaryTail_bounds (S : Set ℕ) (k : ℕ) :
    0 ≤ (∑' n, ternaryTerm S (n + k)) ∧ (∑' n, ternaryTerm S (n + k)) ≤ 1 / 3 ^ k := by
  refine ⟨tsum_nonneg (fun n => ternaryTerm_nonneg S _), ?_⟩
  rw [← (ternaryGeometric k).tsum_eq]
  exact Summable.tsum_le_tsum (fun n => ternaryTerm_bound S _)
    ((ternaryTerm_summable S).comp_injective (add_left_injective k)) (ternaryGeometric k).summable

/-- The first differing digit dominates all subsequent digits. -/
theorem ternaryCode_first_difference (S T : Set ℕ) (k : ℕ)
    (hbefore : ∀ n < k, n ∈ S ↔ n ∈ T) (hkS : k ∈ S) (hkT : k ∉ T) :
    (1 : ℝ) / 3 ^ (k + 1) ≤ ternaryCode S - ternaryCode T := by
  classical
  have hp : ∑ n ∈ Finset.range k, ternaryTerm S n = ∑ n ∈ Finset.range k, ternaryTerm T n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [ternaryTerm, hbefore n (Finset.mem_range.mp hn)]
  have hs : ternaryTerm S k = 2 / 3 ^ (k + 1) := by simp [ternaryTerm, hkS]
  have ht : ternaryTerm T k = 0 := by simp [ternaryTerm, hkT]
  have hS := ternaryTail_bounds S (k + 1)
  have hT := ternaryTail_bounds T (k + 1)
  unfold ternaryCode
  rw [← (ternaryTerm_summable S).sum_add_tsum_nat_add (k + 1),
    ← (ternaryTerm_summable T).sum_add_tsum_nat_add (k + 1),
    Finset.sum_range_succ, Finset.sum_range_succ, hp, hs, ht]
  have hd : (2 : ℝ) / 3 ^ (k + 1) = 1 / 3 ^ (k + 1) + 1 / 3 ^ (k + 1) := by ring
  rw [hd]
  linarith

theorem ternaryCode_spec :
    (∀ S, Summable (ternaryTerm S)) ∧
    (∀ S, ternaryCode S ∈ Set.Icc (0 : ℝ) 1) ∧
    Function.Injective ternaryCode := by
  classical
  refine ⟨ternaryTerm_summable, ?_, ?_⟩
  · intro S
    simpa [ternaryCode] using ternaryTail_bounds S 0
  · intro S T he
    by_contra hne
    have hd : ∃ n, ¬ (n ∈ S ↔ n ∈ T) := by
      by_contra h
      push Not at h
      exact hne (Set.ext h)
    let k := Nat.find hd
    have hk : ¬ (k ∈ S ↔ k ∈ T) := Nat.find_spec hd
    have hb : ∀ n < k, n ∈ S ↔ n ∈ T := by
      intro n hn
      exact not_not.mp (Nat.find_min hd hn)
    have hpos : (0 : ℝ) < 1 / 3 ^ (k + 1) := by positivity
    by_cases hS : k ∈ S
    · have hT : k ∉ T := by tauto
      have h := ternaryCode_first_difference S T k hb hS hT
      rw [he, _root_.sub_self] at h
      exact hpos.not_ge h
    · have hT : k ∈ T := by tauto
      have h := ternaryCode_first_difference T S k (fun n hn => (hb n hn).symm) hT hS
      rw [he, _root_.sub_self] at h
      exact hpos.not_ge h

/-- CH asserts that the continuum is the least uncountable cardinal. -/
def ContinuumHypothesis : Prop := Cardinal.continuum.{u} = Cardinal.aleph.{u} 1

end Lemmatheca.Entry.InfiniteCardinalArithmetic
