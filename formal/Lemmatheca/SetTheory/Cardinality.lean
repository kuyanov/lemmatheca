import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.Real.OfDigits
import Mathlib.Data.Fintype.Powerset
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# Cardinality: displayed witnesses beyond the library existence theorems

Types represent arbitrary sets, and subtypes represent specified subsets. Binary
digits use `Bool` (`false` = 0, `true` = 1). Decimal digits use `Fin 10`.
The proofs retain the displayed witnesses and base-ten expansion convention.
-/

namespace Lemmatheca.SetTheory

universe u v
variable {α : Type u} {β : Type v}

/-- The successive regions in the displayed Bernstein construction. -/
def bernsteinStage (f : α → β) (g : β → α) : ℕ → Set α
  | 0 => (Set.range g)ᶜ
  | n + 1 => g '' (f '' bernsteinStage f g n)

def bernsteinRegion (f : α → β) (g : β → α) : Set α :=
  ⋃ n, bernsteinStage f g n

/-- The last branch only totalizes the definition; the specification rules it out. -/
noncomputable def bernsteinMap (f : α → β) (g : β → α)
    (hg : Function.Injective g) (a : α) : β := by
  classical
  exact if a ∈ bernsteinRegion f g then f a
    else if ha : a ∈ Set.range g then (Equiv.ofInjective g hg).symm ⟨a, ha⟩ else f a

theorem bernstein_map_spec (f : α → β) (g : β → α) (hg : Function.Injective g) :
    (∀ a ∈ bernsteinRegion f g, bernsteinMap f g hg a = f a) ∧
    (∀ a ∉ bernsteinRegion f g, a ∈ Set.range g ∧ g (bernsteinMap f g hg a) = a) := by
  classical
  constructor
  · intro a ha
    simp [bernsteinMap, ha]
  · intro a ha
    have hr : a ∈ Set.range g := by
      by_contra hn
      exact ha (Set.mem_iUnion.mpr ⟨0, hn⟩)
    refine ⟨hr, ?_⟩
    simp only [bernsteinMap, ite_eq_right ha, dite_eq_left hr]
    exact congrArg Subtype.val ((Equiv.ofInjective g hg).apply_symm_apply ⟨a, hr⟩)

theorem bernstein_map_bijective (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Bijective (bernsteinMap f g hg) := by
  classical
  have hc : ∀ a ∈ bernsteinRegion f g, g (f a) ∈ bernsteinRegion f g := by
    intro a ha
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
    exact Set.mem_iUnion.mpr ⟨n + 1, ⟨f a, ⟨a, hn, rfl⟩, rfl⟩⟩
  obtain ⟨hon, hoff⟩ := bernstein_map_spec f g hg
  constructor
  · intro a a' he
    by_cases ha : a ∈ bernsteinRegion f g <;> by_cases ha' : a' ∈ bernsteinRegion f g
    · exact hf (by rwa [hon a ha, hon a' ha'] at he)
    · have hga' := (hoff a' ha').2
      rw [← he, hon a ha] at hga'
      exact False.elim (ha' (hga' ▸ hc a ha))
    · have hga := (hoff a ha).2
      rw [he, hon a' ha'] at hga
      exact False.elim (ha (hga ▸ hc a' ha'))
    · have := congrArg g he
      rwa [(hoff a ha).2, (hoff a' ha').2] at this
  · intro b
    by_cases hb : g b ∈ bernsteinRegion f g
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hb
      cases n with
      | zero => exact False.elim (hn ⟨b, rfl⟩)
      | succ n =>
        obtain ⟨c, ⟨a, ha, rfl⟩, he⟩ := hn
        refine ⟨a, ?_⟩
        rw [hon a (Set.mem_iUnion.mpr ⟨n, ha⟩)]
        exact hg he
    · exact ⟨g b, hg (hoff (g b) hb).2⟩

def diagonalSubset (F : α → Set α) : Set α := {a | a ∉ F a}

theorem diagonalSubset_omitted (F : α → Set α) :
    ∀ a, diagonalSubset F ≠ F a := by
  intro a he
  have h : a ∈ diagonalSubset F ↔ a ∈ F a := by rw [he]
  change (a ∉ F a) ↔ a ∈ F a at h
  tauto

noncomputable def characteristicSequence (s : Set α) (a : α) : Bool := by
  classical
  exact decide (a ∈ s)

def sequenceSubset (s : α → Bool) : Set α := {a | s a = true}

theorem characteristic_inverse_laws :
    Function.LeftInverse (sequenceSubset (α := α)) characteristicSequence ∧
    Function.RightInverse (sequenceSubset (α := α)) characteristicSequence := by
  classical
  constructor
  · intro s
    ext a
    simp [sequenceSubset, characteristicSequence]
  · intro s
    funext a
    cases hs : s a <;> simp [characteristicSequence, sequenceSubset, hs]

def binaryDiagonal (s : ℕ → ℕ → Bool) (n : ℕ) : Bool := !(s n n)

theorem binaryDiagonal_omitted (s : ℕ → ℕ → Bool) :
    ∀ n, binaryDiagonal s ≠ s n := by
  intro n he
  have hn := congrFun he n
  cases h : s n n <;> simp [binaryDiagonal, h] at hn

/-- The first word digit is the least significant binary digit. -/
def binaryWordCode (w : List Bool) : ℕ :=
  2 ^ w.length + w.foldr (fun b acc => b.toNat + 2 * acc) 0

private theorem binaryWordCode_cons (b : Bool) (w : List Bool) :
    binaryWordCode (b :: w) = b.toNat + 2 * binaryWordCode w := by
  simp only [binaryWordCode, List.length_cons, List.foldr_cons, pow_succ]
  ring

private theorem binaryWordCode_bounds (w : List Bool) :
    2 ^ w.length ≤ binaryWordCode w ∧ binaryWordCode w < 2 ^ (w.length + 1) := by
  induction w with
  | nil => norm_num [binaryWordCode]
  | cons b w ih =>
    rw [binaryWordCode_cons]
    simp only [List.length_cons, pow_succ]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> constructor <;> omega

theorem binaryWordCode_spec :
    Function.Injective binaryWordCode ∧ binaryWordCode [] = 1 ∧
    ∀ w, 2 ^ w.length ≤ binaryWordCode w ∧ binaryWordCode w < 2 ^ (w.length + 1) := by
  refine ⟨?_, rfl, binaryWordCode_bounds⟩
  intro w
  induction w with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons b v =>
      have hb := (binaryWordCode_bounds (b :: v)).1
      have hp : 1 ≤ 2 ^ v.length := Nat.one_le_two_pow
      simp only [List.length_cons, pow_succ] at hb
      change 1 = binaryWordCode (b :: v) at h
      omega
  | cons b w ih =>
    intro v h
    cases v with
    | nil =>
      have hb := (binaryWordCode_bounds (b :: w)).1
      have hp : 1 ≤ 2 ^ w.length := Nat.one_le_two_pow
      simp only [List.length_cons, pow_succ] at hb
      change binaryWordCode (b :: w) = 1 at h
      omega
    | cons c v =>
      rw [binaryWordCode_cons, binaryWordCode_cons] at h
      have hbc : b = c := by
        cases b <;> cases c <;> simp_all [Bool.toNat] <;> omega
      subst c
      have htail : binaryWordCode w = binaryWordCode v := by omega
      exact congrArg (List.cons b) (ih htail)

def FiniteSupportBinary := {s : ℕ → Bool // {j | s j = true}.Finite}

noncomputable def finiteSupportCode (s : FiniteSupportBinary) : ℕ :=
  ∑ j ∈ s.property.toFinset, 2 ^ j

private theorem binary_sum_range (n : ℕ) : (∑ i ∈ Finset.range n, 2 ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

private theorem binary_sum_bound (s : Finset ℕ) (n : ℕ) (hs : s ⊆ Finset.range n) :
    (∑ i ∈ s, 2 ^ i) < 2 ^ n := by
  have hle : (∑ i ∈ s, 2 ^ i) ≤ ∑ i ∈ Finset.range n, 2 ^ i :=
    Finset.sum_le_sum_of_subset hs
  have := binary_sum_range n
  omega

private theorem binary_sum_injective (s t : Finset ℕ) (n : ℕ)
    (hs : s ⊆ Finset.range n) (ht : t ⊆ Finset.range n)
    (he : (∑ i ∈ s, 2 ^ i) = ∑ i ∈ t, 2 ^ i) : s = t := by
  classical
  induction n generalizing s t with
  | zero =>
    have : s = ∅ := Finset.subset_empty.mp (by simpa using hs)
    have : t = ∅ := Finset.subset_empty.mp (by simpa using ht)
    simp_all
  | succ n ih =>
    have hse : s.erase n ⊆ Finset.range n := by
      intro i hi
      have := hs (Finset.mem_of_mem_erase hi)
      simp only [Finset.mem_range] at this ⊢
      have := (Finset.mem_erase.mp hi).1
      omega
    have hte : t.erase n ⊆ Finset.range n := by
      intro i hi
      have := ht (Finset.mem_of_mem_erase hi)
      simp only [Finset.mem_range] at this ⊢
      have := (Finset.mem_erase.mp hi).1
      omega
    have hbs := binary_sum_bound (s.erase n) n hse
    have hbt := binary_sum_bound (t.erase n) n hte
    have split (u : Finset ℕ) :
        (∑ i ∈ u, 2 ^ i) = (∑ i ∈ u.erase n, 2 ^ i) + (if n ∈ u then 2 ^ n else 0) := by
      by_cases hn : n ∈ u
      · simpa [hn] using (Finset.sum_erase_add u (fun i => 2 ^ i) hn).symm
      · simp [hn]
    rw [split s, split t] at he
    have hm : n ∈ s ↔ n ∈ t := by
      by_cases hns : n ∈ s <;> by_cases hnt : n ∈ t <;>
        simp only [hns, hnt, ite_true, ite_false] at he ⊢ <;> omega
    have he' : (∑ i ∈ s.erase n, 2 ^ i) = ∑ i ∈ t.erase n, 2 ^ i := by
      simp only [hm] at he
      omega
    have herase := ih (s.erase n) (t.erase n) hse hte he'
    ext i
    by_cases hi : i = n
    · simpa [hi] using hm
    · have := Finset.ext_iff.mp herase i
      simpa [Finset.mem_erase, hi] using this

theorem finiteSupportCode_spec : Function.Injective finiteSupportCode ∧
    ∀ s : FiniteSupportBinary, s.val = (fun _ => false) → finiteSupportCode s = 0 := by
  classical
  constructor
  · intro s t h
    let a := s.property.toFinset
    let b := t.property.toFinset
    obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range (a ∪ b)
    have ha : a ⊆ Finset.range n := Finset.Subset.trans Finset.subset_union_left hn
    have hb : b ⊆ Finset.range n := Finset.Subset.trans Finset.subset_union_right hn
    have he : a = b := binary_sum_injective a b n ha hb h
    apply Subtype.ext
    funext j
    have hj := Finset.ext_iff.mp he j
    change (j ∈ s.property.toFinset ↔ j ∈ t.property.toFinset) at hj
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hj
    cases hs : s.val j <;> cases ht : t.val j <;> simp_all
  · intro s hs
    have he : s.property.toFinset = ∅ := by
      ext j
      simp [hs]
    simp [finiteSupportCode, he]

def DecimalDigits := ℕ → Fin 10

/-- The n-th digit has place value 10^(-(n+1)). -/
noncomputable def decimalValue (d : DecimalDigits) : ℝ :=
  ∑' n : ℕ, (d n).val / (10 : ℝ) ^ (n + 1)

def CanonicalDecimal (d : DecimalDigits) : Prop :=
  ¬ ∃ N : ℕ, ∀ n ≥ N, d n = 9

/-- The entry's division notation agrees with the library's base-ten digit sum. -/
theorem decimalValue_eq_ofDigits (d : DecimalDigits) : decimalValue d = Real.ofDigits d := by
  simp only [decimalValue, Real.ofDigits, Real.ofDigitsTerm, div_eq_mul_inv, Nat.cast_ofNat]

theorem decimalValue_const (k : Fin 10) : decimalValue (fun _ => k) = (k.val : ℝ) / 9 := by
  simp only [decimalValue, div_eq_mul_inv, pow_succ, mul_inv, ← inv_pow]
  erw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 10⁻¹)
    (by norm_num : (10 : ℝ)⁻¹ < 1)]
  norm_num

theorem decimalValue_head (d : DecimalDigits) :
    decimalValue d = ((d 0).val + decimalValue (fun i => d (i + 1))) / 10 := by
  erw [decimalValue_eq_ofDigits, Real.ofDigits_eq_sum_add_ofDigits d 1]
  simp only [Finset.sum_range_one, Real.ofDigitsTerm, pow_one, Nat.cast_ofNat]
  erw [← decimalValue_eq_ofDigits (fun i => d (i + 1))]
  ring

private theorem canonical_shift (d : DecimalDigits) (hd : CanonicalDecimal d) (n : ℕ) :
    CanonicalDecimal (fun i => d (i + n)) := by
  rintro ⟨k, hk⟩
  apply hd
  refine ⟨k + n, ?_⟩
  intro i hi
  have h := hk (i - n) (by omega)
  simpa [Nat.sub_add_cancel (by omega : n ≤ i)] using h

private theorem canonical_value_lt_one (d : DecimalDigits) (hd : CanonicalDecimal d) :
    decimalValue d < 1 := by
  classical
  have hn : ∃ n, d n ≠ 9 := by
    by_contra h
    push Not at h
    exact hd ⟨0, fun n _ => h n⟩
  obtain ⟨n, hn⟩ := hn
  have hle : ∀ i, Real.ofDigitsTerm d i ≤ Real.ofDigitsTerm (fun _ => (9 : Fin 10)) i := by
    intro i
    simp only [Real.ofDigitsTerm]
    gcongr
    exact_mod_cast (by have := (d i).isLt; omega : (d i).val ≤ (9 : Fin 10).val)
  have hlt : Real.ofDigitsTerm d n < Real.ofDigitsTerm (fun _ => (9 : Fin 10)) n := by
    simp only [Real.ofDigitsTerm]
    apply mul_lt_mul_of_pos_right _ (by positivity)
    exact_mod_cast (by have := (d n).isLt; have := Fin.val_ne_of_ne hn; omega :
      (d n).val < (9 : Fin 10).val)
  have h := Summable.tsum_lt_tsum hle hlt Real.summable_ofDigitsTerm Real.summable_ofDigitsTerm
  change Real.ofDigits d < Real.ofDigits (fun _ => (9 : Fin 10)) at h
  erw [← decimalValue_eq_ofDigits d, ← decimalValue_eq_ofDigits (fun _ => (9 : Fin 10)),
    decimalValue_const] at h
  norm_num at h
  exact h

private theorem canonical_head_eq (d e : DecimalDigits)
    (hd : CanonicalDecimal d) (he : CanonicalDecimal e) (hv : decimalValue d = decimalValue e) :
    d 0 = e 0 := by
  have hdt := canonical_value_lt_one _ (canonical_shift d hd 1)
  have het := canonical_value_lt_one _ (canonical_shift e he 1)
  have hd0 := Real.ofDigits_nonneg (fun i => d (i + 1))
  have he0 := Real.ofDigits_nonneg (fun i => e (i + 1))
  erw [← decimalValue_eq_ofDigits] at hd0 he0
  erw [decimalValue_head d, decimalValue_head e] at hv
  apply Fin.ext
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have hgap : ((d 0).val : ℝ) + 1 ≤ (e 0).val := by exact_mod_cast Nat.succ_le_of_lt hlt
    linarith
  · have hgap : ((e 0).val : ℝ) + 1 ≤ (d 0).val := by exact_mod_cast Nat.succ_le_of_lt hgt
    linarith

private theorem canonical_value_injective (d e : DecimalDigits)
    (hd : CanonicalDecimal d) (he : CanonicalDecimal e) (hv : decimalValue d = decimalValue e) :
    d = e := by
  have hshift : ∀ n, decimalValue (fun i => d (i + n)) = decimalValue (fun i => e (i + n)) := by
    intro n
    induction n with
    | zero => simpa using hv
    | succ n ih =>
      have hhead := canonical_head_eq _ _ (canonical_shift d hd n) (canonical_shift e he n) ih
      simp only [zero_add] at hhead
      erw [decimalValue_head (fun i => d (i + n)),
        decimalValue_head (fun i => e (i + n))] at ih
      simp only [Nat.zero_add, hhead] at ih
      have heq : decimalValue (fun i => d (i + 1 + n)) =
          decimalValue (fun i => e (i + 1 + n)) := by linarith
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq
  funext n
  simpa using canonical_head_eq _ _ (canonical_shift d hd n) (canonical_shift e he n) (hshift n)

theorem canonical_decimal_expansion {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    ∃! d : DecimalDigits, CanonicalDecimal d ∧ decimalValue d = x := by
  have hx' : x ∈ Set.Ico 0 1 := ⟨hx.1.le, hx.2⟩
  have hv : decimalValue (Real.digits x 10) = x := by
    erw [decimalValue_eq_ofDigits]
    exact Real.ofDigits_digits (by norm_num) hx'
  have hc : CanonicalDecimal (Real.digits x 10) := by
    rintro ⟨n, hn⟩
    have htail : (fun i => Real.digits x 10 (i + n)) = (fun _ => (Fin.last 9)) := by
      funext i
      exact hn (i + n) (by omega)
    have hsplit := Real.ofDigits_eq_sum_add_ofDigits (Real.digits x 10) n
    erw [Real.ofDigits_digits (by norm_num) hx', htail, Real.ofDigits_const_last_eq_one] at hsplit
    have hfloor := Real.ofDigits_digits_sum_eq (b := 10) hx' n
    have hlt := Nat.lt_floor_add_one ((10 : ℝ) ^ n * x)
    norm_num only [Nat.cast_ofNat] at hfloor hsplit
    erw [← hfloor] at hlt
    have hcancel : (10 : ℝ) ^ n * ((10 : ℝ) ^ n)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have hmul := congrArg (fun y : ℝ => (10 : ℝ) ^ n * y) hsplit
    simp only [mul_one, mul_add, hcancel] at hmul
    linarith
  refine ⟨Real.digits x 10, ⟨hc, hv⟩, ?_⟩
  intro d hd
  exact canonical_value_injective d _ hd.1 hc (hd.2.trans hv.symm)

def decimalDiagonal (d : ℕ → DecimalDigits) (n : ℕ) : Fin 10 :=
  if d n n = 1 then 2 else 1

private theorem decimalValue_mono (d e : DecimalDigits) (h : ∀ i, (d i).val ≤ (e i).val) :
    decimalValue d ≤ decimalValue e := by
  erw [decimalValue_eq_ofDigits, decimalValue_eq_ofDigits]
  apply Summable.tsum_mono Real.summable_ofDigitsTerm Real.summable_ofDigitsTerm
  intro i
  simp only [Real.ofDigitsTerm]
  gcongr
  exact_mod_cast h i

theorem decimalDiagonal_spec (x : ℕ → ℝ) (d : ℕ → DecimalDigits)
    (hx : ∀ n, x n ∈ Set.Ioo 0 1)
    (hd : ∀ n, CanonicalDecimal (d n) ∧ decimalValue (d n) = x n) :
    decimalValue (decimalDiagonal d) ∈ Set.Ioo 0 1 ∧
    (1 / 9 : ℝ) ≤ decimalValue (decimalDiagonal d) ∧
    decimalValue (decimalDiagonal d) ≤ (2 / 9 : ℝ) ∧
    CanonicalDecimal (decimalDiagonal d) ∧
    ∀ n, decimalValue (decimalDiagonal d) ≠ x n := by
  have hdigit (n : ℕ) : decimalDiagonal d n = 1 ∨ decimalDiagonal d n = 2 := by
    simp only [decimalDiagonal]
    split <;> simp
  have hcanon : CanonicalDecimal (decimalDiagonal d) := by
    rintro ⟨n, hn⟩
    have h := hn n le_rfl
    rcases hdigit n with he | he <;> rw [he] at h <;> norm_num at h
  have hlo : (1 / 9 : ℝ) ≤ decimalValue (decimalDiagonal d) := by
    have h := decimalValue_mono (fun _ => 1) (decimalDiagonal d) (fun n => by
      rcases hdigit n with h | h <;> simp [h])
    simpa [decimalValue_const] using h
  have hhi : decimalValue (decimalDiagonal d) ≤ (2 / 9 : ℝ) := by
    have h := decimalValue_mono (decimalDiagonal d) (fun _ => 2) (fun n => by
      rcases hdigit n with h | h <;> simp [h])
    simpa [decimalValue_const] using h
  refine ⟨⟨by linarith, by linarith⟩, hlo, hhi, hcanon, ?_⟩
  intro n he
  have hs := canonical_value_injective (decimalDiagonal d) (d n) hcanon (hd n).1
    (he.trans (hd n).2.symm)
  have hn := congrFun hs n
  unfold decimalDiagonal at hn
  split at hn <;> grind

theorem irrational_uncountable : ¬ Countable {x : ℝ // Irrational x} := by
  intro h
  have hi : Set.Countable {x : ℝ | Irrational x} := h
  have hr := Set.countable_range ((↑) : ℚ → ℝ)
  have hu : (Set.univ : Set ℝ).Countable := by
    convert hi.union hr using 1
    ext x
    simp [Irrational]
    classical
    by_cases hq : ∃ q : ℚ, (q : ℝ) = x
    · exact Or.inr hq
    · exact Or.inl (fun q he => hq ⟨q, he⟩)
  exact Cardinal.not_countable_real hu

noncomputable def lineToSymmetricInterval (x : ℝ) : ℝ := x / (1 + |x|)

noncomputable def symmetricIntervalToLine (t : ℝ) : ℝ := t / (1 - |t|)

theorem line_interval_inverse_laws :
    Set.MapsTo lineToSymmetricInterval Set.univ (Set.Ioo (-1) 1) ∧
    (∀ x, symmetricIntervalToLine (lineToSymmetricInterval x) = x) ∧
    (∀ t ∈ Set.Ioo (-1) 1, lineToSymmetricInterval (symmetricIntervalToLine t) = t) := by
  have hu (x : ℝ) : |lineToSymmetricInterval x| < 1 := by
    rw [lineToSymmetricInterval, abs_div, abs_of_pos (by positivity : 0 < 1 + |x|)]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hux (x : ℝ) : |lineToSymmetricInterval x| = |x| / (1 + |x|) := by
    simp [lineToSymmetricInterval, abs_div, abs_of_pos (by positivity : 0 < 1 + |x|)]
  have hvt (t : ℝ) (ht : |t| < 1) : |symmetricIntervalToLine t| = |t| / (1 - |t|) := by
    simp [symmetricIntervalToLine, abs_div, abs_of_pos (by linarith : 0 < 1 - |t|)]
  refine ⟨?_, ?_, ?_⟩
  · intro x _
    exact abs_lt.mp (hu x)
  · intro x
    unfold symmetricIntervalToLine
    rw [hux]
    unfold lineToSymmetricInterval
    have hp : 1 + |x| ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring
  · intro t ht
    have ht' : |t| < 1 := abs_lt.mpr ht
    unfold lineToSymmetricInterval
    rw [hvt t ht']
    unfold symmetricIntervalToLine
    have hp : 1 - |t| ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring

theorem affine_interval_inverse_laws (a b : ℝ) (hab : a < b) :
    Set.BijOn (fun t : ℝ => a + (b - a) * t) (Set.Ioo 0 1) (Set.Ioo a b) ∧
    (∀ t ∈ Set.Ioo 0 1, (a + (b - a) * t - a) / (b - a) = t) ∧
    (∀ x ∈ Set.Ioo a b, (x - a) / (b - a) ∈ Set.Ioo 0 1 ∧
      a + (b - a) * ((x - a) / (b - a)) = x) := by
  have hp : 0 < b - a := sub_pos.mpr hab
  have hinv (x : ℝ) : a + (b - a) * ((x - a) / (b - a)) = x := by
    field_simp
    ring
  have hleft (t : ℝ) : (a + (b - a) * t - a) / (b - a) = t := by
    field_simp
    ring
  have hmaps : Set.MapsTo (fun t : ℝ => a + (b - a) * t) (Set.Ioo 0 1) (Set.Ioo a b) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2]
  have hback : Set.MapsTo (fun x : ℝ => (x - a) / (b - a)) (Set.Ioo a b) (Set.Ioo 0 1) := by
    intro x hx
    constructor
    · exact div_pos (sub_pos.mpr hx.1) hp
    · exact (div_lt_one hp).mpr (by linarith [hx.2])
  refine ⟨⟨hmaps, ?_, ?_⟩, (fun t _ => hleft t), ?_⟩
  · intro t _ u _ he
    have := congrArg (fun x => (x - a) / (b - a)) he
    simpa only [hleft] using this
  · intro x hx
    exact ⟨(x - a) / (b - a), hback hx, hinv x⟩
  · intro x hx
    exact ⟨hback hx, hinv x⟩

end Lemmatheca.SetTheory
