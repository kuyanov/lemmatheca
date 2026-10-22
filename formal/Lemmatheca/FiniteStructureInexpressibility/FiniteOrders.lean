import Lemmatheca.FiniteRoundComparison.CharacteristicFormulas
import Lemmatheca.ExpressiveLimits.ExpressiveLimits
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Finset.Sort

/-! Finite ordered gaps and their exact finite-round extension invariant. -/

namespace Lemmatheca.ModelTheory.FiniteStructureInexpressibility

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.FiniteRoundComparison

instance : ExpressiveLimits.language.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance finiteRelations : Finite (Σ r : ℕ, ExpressiveLimits.language.Relations r) := by
  let f : (Σ r : ℕ, ExpressiveLimits.language.Relations r) → Unit := fun _ => ()
  apply Finite.of_injective f
  rintro ⟨r, R⟩ ⟨s, S⟩ _
  cases R
  cases S
  rfl

/-- Definability on a stated ambient class of finite nonempty relation structures. -/
def RelativelyFiniteDefinable
    (D P : (M : Type) → (M → M → Prop) → Prop) : Prop :=
  ∃ σ : ExpressiveLimits.language.Sentence,
    ∀ (M : Type) [Finite M] [Nonempty M] (r : M → M → Prop), D M r →
      (@Sentence.Realize ExpressiveLimits.language M (ExpressiveLimits.relationStructure r) σ ↔ P M r)

/-- The specified order interpretation, supplied explicitly to avoid graph/order instance ambiguity. -/
@[instance_reducible] def orderStructure (n : ℕ) : ExpressiveLimits.language.Structure (Fin n) :=
  ExpressiveLimits.relationStructure (· < ·)

theorem finite_order_enumeration {M : Type} [Finite M] [Nonempty M]
    (r : M → M → Prop) (hr : IsStrictTotalOrder M r) :
    ∃ n : ℕ, 0 < n ∧ ∃ e : M ≃ Fin n, ∀ a b, r a b ↔ e a < e b := by
  classical
  let : IsStrictTotalOrder M r := hr
  let : LinearOrder M := linearOrderOfSTO r
  let : Fintype M := Fintype.ofFinite M
  let e := Fintype.orderIsoFinOfCardEq M rfl
  exact ⟨Fintype.card M, Fintype.card_pos, e.symm.toEquiv, fun a b => e.symm.lt_iff_lt.symm⟩

/-- Left and right endpoints, or a coordinate of the selected tuple. -/
abbrev Marker (p : ℕ) := Bool ⊕ Fin p

/-- Shift actual points by one; the two sentinels have positions zero and one past the carrier. -/
def markerPosition {n p : ℕ} (a : Fin p → Fin n) : Marker p → ℕ
  | .inl false => 0
  | .inl true => n + 1
  | .inr i => (a i).val + 1

/-- The two markers are consecutive distinct selected positions or endpoints. -/
def AdjacentGap {n p : ℕ} (a : Fin p → Fin n) (s t : Marker p) : Prop :=
  markerPosition a s < markerPosition a t ∧
    ∀ i : Fin p, ¬ (markerPosition a s < (a i).val + 1 ∧
      (a i).val + 1 < markerPosition a t)

def gapSize {n p : ℕ} (a : Fin p → Fin n) (s t : Marker p) : ℕ :=
  markerPosition a t - markerPosition a s - 1

/-- Small gaps match exactly; unequal gaps both exceed the remaining-round threshold. -/
def GapProperty (k : ℕ) {m n p : ℕ} (a : Fin p → Fin m) (b : Fin p → Fin n) : Prop :=
  @AtomicMatch ExpressiveLimits.language (Fin m) (Fin n) (orderStructure m) (orderStructure n) p a b ∧
    ∀ s t : Marker p, AdjacentGap a s t →
      gapSize a s t = gapSize b s t ∨
        (2 ^ k - 1 ≤ gapSize a s t ∧ 2 ^ k - 1 ≤ gapSize b s t)

private theorem order_atomic_iff {m n p : ℕ} (a : Fin p → Fin m) (b : Fin p → Fin n) :
    @AtomicMatch ExpressiveLimits.language (Fin m) (Fin n) (orderStructure m) (orderStructure n) p a b ↔
      ∀ i j, (a i).val < (a j).val ↔ (b i).val < (b j).val := by
  rw [@atomicMatch_iff ExpressiveLimits.language (Fin m) (Fin n)
    (orderStructure m) (orderStructure n)]
  constructor
  · intro h i j
    exact h.2 2 ExpressiveLimits.edgeSymbol ![i,j]
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j
      have h₁ := h i j
      have h₂ := h j i
      rw [Fin.ext_iff, Fin.ext_iff]
      omega
    · intro r R v
      cases R
      exact h (v 0) (v 1)

private theorem marker_lt_iff {m n p : ℕ} {a : Fin p → Fin m} {b : Fin p → Fin n}
    (h : @AtomicMatch ExpressiveLimits.language (Fin m) (Fin n) (orderStructure m) (orderStructure n) p a b)
    (s t : Marker p) : markerPosition a s < markerPosition a t ↔
      markerPosition b s < markerPosition b t := by
  have ho := (order_atomic_iff a b).mp h
  rcases s with (s | i) <;> rcases t with (t | j)
  · cases s <;> cases t <;> simp [markerPosition]
  · cases s <;> simp only [markerPosition]
    · omega
    · have ha := (a j).isLt; have hb := (b j).isLt; omega
  · cases t <;> simp only [markerPosition]
    · omega
    · have ha := (a i).isLt; have hb := (b i).isLt; omega
  · simpa only [markerPosition, Nat.add_lt_add_iff_right] using ho i j

private theorem marker_eq_iff {m n p : ℕ} {a : Fin p → Fin m} {b : Fin p → Fin n}
    (h : @AtomicMatch ExpressiveLimits.language (Fin m) (Fin n) (orderStructure m) (orderStructure n) p a b)
    (s t : Marker p) : markerPosition a s = markerPosition a t ↔
      markerPosition b s = markerPosition b t := by
  have h₁ := marker_lt_iff h s t
  have h₂ := marker_lt_iff h t s
  omega

private theorem marker_le_bound {n p} (a : Fin p → Fin n) (s : Marker p) :
    markerPosition a s ≤ n + 1 := by
  rcases s with (s | i)
  · cases s <;> simp [markerPosition]
  · have h := (a i).isLt; simp only [markerPosition]; omega

private theorem marker_interior {n p} (a : Fin p → Fin n) (s : Marker p)
    (h₀ : 0 < markerPosition a s) (hₙ : markerPosition a s < n + 1) :
    ∃ i, markerPosition a s = (a i).val + 1 := by
  rcases s with (s | i)
  · cases s <;> simp [markerPosition] at h₀ hₙ
  · exact ⟨i, rfl⟩

private theorem new_marker {n m p} (a : Fin p → Fin n) (b : Fin p → Fin m)
    (x : Fin n) (y : Fin m) (u : Marker (p+1)) :
    (∃ s : Marker p, markerPosition (Fin.snoc a x) u = markerPosition a s ∧
      markerPosition (Fin.snoc b y) u = markerPosition b s) ∨
    (markerPosition (Fin.snoc a x) u = x.val + 1 ∧
      markerPosition (Fin.snoc b y) u = y.val + 1) := by
  rcases u with (u | i)
  · cases u
    · exact Or.inl ⟨.inl false, rfl, rfl⟩
    · exact Or.inl ⟨.inl true, rfl, rfl⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Or.inr ⟨by simp [markerPosition], by simp [markerPosition]⟩
    · exact Or.inl ⟨.inr j, by simp [markerPosition], by simp [markerPosition]⟩

private theorem atomic_snoc {m n p} {a : Fin p → Fin m} {b : Fin p → Fin n}
    (h : @AtomicMatch ExpressiveLimits.language (Fin m) (Fin n) (orderStructure m) (orderStructure n) p a b)
    (x : Fin m) (y : Fin n)
    (hl : ∀ i, (a i).val < x.val ↔ (b i).val < y.val)
    (hr : ∀ i, x.val < (a i).val ↔ y.val < (b i).val) :
    @AtomicMatch ExpressiveLimits.language (Fin m) (Fin n) (orderStructure m) (orderStructure n)
      (p+1) (Fin.snoc a x) (Fin.snoc b y) := by
  apply (order_atomic_iff _ _).mpr
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · simpa using hr j
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hl i
    · simpa using (order_atomic_iff a b).mp h i j

private theorem gap_weakening {k m n p} {a : Fin p → Fin m} {b : Fin p → Fin n}
    (h : GapProperty (k+1) a b) : GapProperty k a b := by
  refine ⟨h.1, fun s t hadj => ?_⟩
  rcases h.2 s t hadj with he | ⟨ha,hb⟩
  · exact Or.inl he
  · right
    have hp : 2^k ≤ 2^(k+1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

theorem corresponding_gaps {m n p : ℕ} (a : Fin p → Fin m) (b : Fin p → Fin n)
    (h : @AtomicMatch ExpressiveLimits.language (Fin m) (Fin n) (orderStructure m) (orderStructure n) p a b)
    (s t : Marker p) : AdjacentGap a s t ↔ AdjacentGap b s t := by
  have hst := marker_lt_iff h s t
  have hl (i : Fin p) := marker_lt_iff h s (.inr i)
  have hr (i : Fin p) := marker_lt_iff h (.inr i) t
  change ∀ i, markerPosition a s < (a i).val+1 ↔ markerPosition b s < (b i).val+1 at hl
  change ∀ i, (a i).val+1 < markerPosition a t ↔ (b i).val+1 < markerPosition b t at hr
  simp only [AdjacentGap, hst, hl, hr]

private theorem split_lengths {q S T X S' T' : ℕ}
    (hx : S < X ∧ X < T) (ht : S' < T')
    (h : T-S-1 = T'-S'-1 ∨ (2*q+1 ≤ T-S-1 ∧ 2*q+1 ≤ T'-S'-1)) :
    ∃ Y, S' < Y ∧ Y < T' ∧
      (X-S-1 = Y-S'-1 ∨ (q ≤ X-S-1 ∧ q ≤ Y-S'-1)) ∧
      (T-X-1 = T'-Y-1 ∨ (q ≤ T-X-1 ∧ q ≤ T'-Y-1)) := by
  rcases h with he | ⟨ha,hb⟩
  · exact ⟨S'+(X-S), by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩
  · by_cases hl : X-S-1 < q
    · exact ⟨S'+(X-S), by omega, by omega, Or.inl (by omega), Or.inr ⟨by omega, by omega⟩⟩
    · by_cases hr : T-X-1 < q
      · exact ⟨T'-(T-X), by omega, by omega, Or.inr ⟨by omega, by omega⟩, Or.inl (by omega)⟩
      · exact ⟨S'+q+1, by omega, by omega, Or.inr ⟨by omega, by omega⟩,
          Or.inr ⟨by omega, by omega⟩⟩

private theorem enclosing_gap {m p} (a : Fin p → Fin m) (x : Fin m)
    (hfresh : ∀ i, a i ≠ x) :
    ∃ s t : Marker p, AdjacentGap a s t ∧
      markerPosition a s < x.val+1 ∧ x.val+1 < markerPosition a t := by
  classical
  let S := Finset.univ.filter (fun s : Marker p => markerPosition a s < x.val+1)
  let T := Finset.univ.filter (fun t : Marker p => x.val+1 < markerPosition a t)
  have hs : S.Nonempty := ⟨.inl false, by simp [S, markerPosition]⟩
  have ht : T.Nonempty := ⟨.inl true, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    change x.val+1 < m+1
    exact Nat.add_lt_add_right x.isLt 1⟩⟩
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image S (markerPosition a) hs
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image T (markerPosition a) ht
  have hsl : markerPosition a s < x.val+1 := (Finset.mem_filter.mp hs).2
  have htr : x.val+1 < markerPosition a t := (Finset.mem_filter.mp ht).2
  refine ⟨s,t,⟨by omega, ?_⟩,hsl,htr⟩
  intro i hi
  have hne : (a i).val ≠ x.val := fun he => hfresh i (Fin.ext he)
  by_cases hil : (a i).val+1 < x.val+1
  · have him := hmax (.inr i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hil⟩)
    change (a i).val+1 ≤ markerPosition a s at him
    omega
  · have hir : x.val+1 < (a i).val+1 := by omega
    have him := hmin (.inr i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hir⟩)
    change markerPosition a t ≤ (a i).val+1 at him
    omega

private theorem repeated_gap {k m n p} {a : Fin p → Fin m} {b : Fin p → Fin n}
    (h : GapProperty k a b) (i : Fin p) :
    GapProperty k (Fin.snoc a (a i)) (Fin.snoc b (b i)) := by
  have hm := (order_atomic_iff a b).mp h.1
  refine ⟨atomic_snoc h.1 _ _ (fun j => hm j i) (fun j => hm i j), ?_⟩
  intro u v huv
  have lower (w : Marker (p+1)) : ∃ s : Marker p,
      markerPosition (Fin.snoc a (a i)) w = markerPosition a s ∧
      markerPosition (Fin.snoc b (b i)) w = markerPosition b s := by
    rcases new_marker a b (a i) (b i) w with hs | hnew
    · exact hs
    · exact ⟨.inr i, hnew⟩
  obtain ⟨s,hsa,hsb⟩ := lower u
  obtain ⟨t,hta,htb⟩ := lower v
  have hold : AdjacentGap a s t := by
    refine ⟨by simpa only [hsa,hta] using huv.1, ?_⟩
    intro j hj
    have hh := huv.2 j.castSucc
    simp only [Fin.snoc_castSucc] at hh
    exact hh (by simpa only [hsa,hta] using hj)
  simpa only [gapSize, hsa, hta, hsb, htb] using h.2 s t hold

private theorem unique_left {m p} (a : Fin p → Fin m) (x : Fin m) (s u : Marker p)
    (hs : markerPosition a s < x.val+1) (hu : markerPosition a u < x.val+1)
    (hsmax : ∀ i, ¬(markerPosition a s < (a i).val+1 ∧ (a i).val+1 < x.val+1))
    (humax : ∀ i, ¬(markerPosition a u < (a i).val+1 ∧ (a i).val+1 < x.val+1)) :
    markerPosition a s = markerPosition a u := by
  have bound := x.isLt
  by_contra he
  rcases lt_or_gt_of_ne he with h | h
  · obtain ⟨i,hi⟩ := marker_interior a u (by omega) (by omega)
    exact hsmax i (by omega)
  · obtain ⟨i,hi⟩ := marker_interior a s (by omega) (by omega)
    exact humax i (by omega)

private theorem unique_right {m p} (a : Fin p → Fin m) (x : Fin m) (s u : Marker p)
    (hs : x.val+1 < markerPosition a s) (hu : x.val+1 < markerPosition a u)
    (hsmin : ∀ i, ¬(x.val+1 < (a i).val+1 ∧ (a i).val+1 < markerPosition a s))
    (humin : ∀ i, ¬(x.val+1 < (a i).val+1 ∧ (a i).val+1 < markerPosition a u)) :
    markerPosition a s = markerPosition a u := by
  have bs := marker_le_bound a s
  have bu := marker_le_bound a u
  by_contra he
  rcases lt_or_gt_of_ne he with h | h
  · obtain ⟨i,hi⟩ := marker_interior a s (by omega) (by omega)
    exact humin i (by omega)
  · obtain ⟨i,hi⟩ := marker_interior a u (by omega) (by omega)
    exact hsmin i (by omega)

private theorem fresh_gap {k m n p} {a : Fin p → Fin m} {b : Fin p → Fin n}
    (h : GapProperty (k+1) a b) (x : Fin m) (s t : Marker p)
    (hadj : AdjacentGap a s t)
    (hsx : markerPosition a s < x.val+1) (hxt : x.val+1 < markerPosition a t) :
    ∃ y : Fin n, GapProperty k (Fin.snoc a x) (Fin.snoc b y) := by
  have hb := (corresponding_gaps a b h.1 s t).mp hadj
  have hp : 0 < 2^k := Nat.two_pow_pos k
  have ht : 2^(k+1)-1 = 2*(2^k-1)+1 := by rw [pow_succ]; omega
  have hg := h.2 s t hadj
  change markerPosition a t-markerPosition a s-1 = markerPosition b t-markerPosition b s-1 ∨
    (2^(k+1)-1 ≤ markerPosition a t-markerPosition a s-1 ∧
     2^(k+1)-1 ≤ markerPosition b t-markerPosition b s-1) at hg
  rw [ht] at hg
  obtain ⟨Y,hsy,hyt,hl,hr⟩ := split_lengths ⟨hsx,hxt⟩ hb.1 hg
  have hbound := marker_le_bound b t
  have hy₀ : 0 < Y := by omega
  let y : Fin n := ⟨Y-1, by omega⟩
  have hy : y.val+1 = Y := by dsimp [y]; omega
  have hleft (i : Fin p) : (a i).val < x.val ↔ (b i).val < y.val := by
    have h₁ := marker_lt_iff h.1 s (.inr i)
    have h₂ := marker_lt_iff h.1 (.inr i) t
    change markerPosition a s < (a i).val+1 ↔ markerPosition b s < (b i).val+1 at h₁
    change (a i).val+1 < markerPosition a t ↔ (b i).val+1 < markerPosition b t at h₂
    have ha := hadj.2 i
    have hc := hb.2 i
    omega
  have hright (i : Fin p) : x.val < (a i).val ↔ y.val < (b i).val := by
    have h₁ := marker_lt_iff h.1 s (.inr i)
    have h₂ := marker_lt_iff h.1 (.inr i) t
    change markerPosition a s < (a i).val+1 ↔ markerPosition b s < (b i).val+1 at h₁
    change (a i).val+1 < markerPosition a t ↔ (b i).val+1 < markerPosition b t at h₂
    have ha := hadj.2 i
    have hc := hb.2 i
    omega
  refine ⟨y, atomic_snoc h.1 x y hleft hright, ?_⟩
  intro u v huv
  have hlow := gap_weakening h
  have hsmax (i : Fin p) : ¬(markerPosition a s < (a i).val+1 ∧ (a i).val+1 < x.val+1) := by
    intro hi; exact hadj.2 i ⟨hi.1, by omega⟩
  have htmin (i : Fin p) : ¬(x.val+1 < (a i).val+1 ∧ (a i).val+1 < markerPosition a t) := by
    intro hi; exact hadj.2 i ⟨by omega, hi.2⟩
  rcases new_marker a b x y u with ⟨u',hua,hub⟩ | ⟨hua,hub⟩ <;>
    rcases new_marker a b x y v with ⟨v',hva,hvb⟩ | ⟨hva,hvb⟩
  · have hold : AdjacentGap a u' v' := by
      refine ⟨by simpa only [hua,hva] using huv.1, ?_⟩
      intro j hj
      have hh := huv.2 j.castSucc
      simp only [Fin.snoc_castSucc] at hh
      exact hh (by simpa only [hua,hva] using hj)
    simpa only [gapSize,hua,hva,hub,hvb] using hlow.2 u' v' hold
  · have hu : markerPosition a u' < x.val+1 := by simpa only [hua,hva] using huv.1
    have humax (i : Fin p) : ¬(markerPosition a u' < (a i).val+1 ∧ (a i).val+1 < x.val+1) := by
      intro hi
      have hh := huv.2 i.castSucc
      simp only [Fin.snoc_castSucc] at hh
      exact hh (by simpa only [hua,hva] using hi)
    have he := unique_left a x s u' hsx hu hsmax humax
    have he' := (marker_eq_iff h.1 s u').mp he
    simpa only [gapSize,hua,hva,hub,hvb,← he,← he',hy] using hl
  · have hv : x.val+1 < markerPosition a v' := by simpa only [hua,hva] using huv.1
    have hvmin (i : Fin p) : ¬(x.val+1 < (a i).val+1 ∧ (a i).val+1 < markerPosition a v') := by
      intro hi
      have hh := huv.2 i.castSucc
      simp only [Fin.snoc_castSucc] at hh
      exact hh (by simpa only [hua,hva] using hi)
    have he := unique_right a x t v' hxt hv htmin hvmin
    have he' := (marker_eq_iff h.1 t v').mp he
    simpa only [gapSize,hua,hva,hub,hvb,← he,← he',hy] using hr
  · have hc := huv.1
    rw [hua,hva] at hc
    omega

private theorem gap_symm {k m n p} {a : Fin p → Fin m} {b : Fin p → Fin n}
    (h : GapProperty k a b) : GapProperty k b a := by
  have hat : @AtomicMatch ExpressiveLimits.language (Fin n) (Fin m)
      (orderStructure n) (orderStructure m) p b a := fun i => (h.1 i).symm
  refine ⟨hat, fun s t hst => ?_⟩
  rcases h.2 s t ((corresponding_gaps a b h.1 s t).mpr hst) with he | ⟨ha,hb⟩
  · exact Or.inl he.symm
  · exact Or.inr ⟨hb,ha⟩

private theorem gap_forth {k m n p} {a : Fin p → Fin m} {b : Fin p → Fin n}
    (h : GapProperty (k+1) a b) (x : Fin m) :
    ∃ y : Fin n, GapProperty k (Fin.snoc a x) (Fin.snoc b y) := by
  classical
  by_cases hex : ∃ i, a i = x
  · obtain ⟨i,rfl⟩ := hex
    exact ⟨b i, repeated_gap (gap_weakening h) i⟩
  · obtain ⟨s,t,hadj,hs,ht⟩ := enclosing_gap a x (by simpa using hex)
    exact fresh_gap h x s t hadj hs ht

theorem split_gap {k m n p : ℕ} (_hm : 0 < m) (_hn : 0 < n)
    {a : Fin p → Fin m} {b : Fin p → Fin n} (h : GapProperty (k + 1) a b) :
    (∀ x : Fin m, ∃ y : Fin n, GapProperty k (Fin.snoc a x) (Fin.snoc b y)) ∧
    (∀ y : Fin n, ∃ x : Fin m, GapProperty k (Fin.snoc a x) (Fin.snoc b y)) := by
  refine ⟨gap_forth h, ?_⟩
  intro y
  obtain ⟨x,hx⟩ := gap_forth (gap_symm h) y
  exact ⟨x,gap_symm hx⟩

theorem gap_wins {k m n p : ℕ} (hm : 0 < m) (hn : 0 < n)
    {a : Fin p → Fin m} {b : Fin p → Fin n} (h : GapProperty k a b) :
    @Wins ExpressiveLimits.language (Fin m) (Fin n) (orderStructure m) (orderStructure n) k p a b := by
  induction k generalizing p with
  | zero => exact h.1
  | succ k ih =>
    obtain ⟨hf, hb⟩ := split_gap hm hn h
    refine ⟨h.1, fun x => ?_, fun y => ?_⟩
    · obtain ⟨y, hy⟩ := hf x
      exact ⟨y, ih hy⟩
    · obtain ⟨x, hx⟩ := hb y
      exact ⟨x, ih hx⟩

theorem large_orders (k m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hkm : 2 ^ k - 1 ≤ m) (hkn : 2 ^ k - 1 ≤ n) :
    @RankAgreement ExpressiveLimits.language (Fin m) (Fin n) (orderStructure m) (orderStructure n)
      k 0 Fin.elim0 Fin.elim0 := by
  let : ExpressiveLimits.language.Structure (Fin m) := orderStructure m
  let : ExpressiveLimits.language.Structure (Fin n) := orderStructure n
  apply wins_preserves_formulas
  apply gap_wins hm hn
  constructor
  · apply (atomicMatch_iff _ _).mpr
    refine ⟨fun i => i.elim0, ?_⟩
    intro r R v
    cases R
    exact (v 0).elim0
  · intro s t hadj
    rcases s with s | s
    · rcases t with t | t
      · cases s <;> cases t <;> simp_all [AdjacentGap, gapSize, markerPosition]
      · exact t.elim0
    · exact s.elim0

private theorem adjacent_sizes (σ : ExpressiveLimits.language.Sentence) :
    ∃ m : ℕ, 0 < m ∧ Even m ∧ Odd (m + 1) ∧
      (@Sentence.Realize ExpressiveLimits.language (Fin m) (orderStructure m) σ ↔
        @Sentence.Realize ExpressiveLimits.language (Fin (m + 1)) (orderStructure (m + 1)) σ) := by
  let k := quantifierRank σ
  let m := 2 * 2 ^ k
  have hp : 0 < 2 ^ k := Nat.pow_pos (by omega)
  have hm : 0 < m := by dsimp [m]; omega
  have hkm : 2 ^ k - 1 ≤ m := by dsimp [m]; omega
  have hkn : 2 ^ k - 1 ≤ m + 1 := by omega
  let : ExpressiveLimits.language.Structure (Fin m) := orderStructure m
  let : ExpressiveLimits.language.Structure (Fin (m + 1)) := orderStructure (m + 1)
  have h := large_orders k m (m + 1) hm (by omega) hkm hkn
    (tupleFormula σ) (by simpa only [quantifierRank_tupleFormula] using (le_rfl : quantifierRank σ ≤ quantifierRank σ))
  have hs : @Sentence.Realize ExpressiveLimits.language (Fin m) (orderStructure m) σ ↔
      @Sentence.Realize ExpressiveLimits.language (Fin (m + 1)) (orderStructure (m + 1)) σ := by
    exact (tupleFormula_realize _ _).symm.trans (h.trans (tupleFormula_realize _ _))
  refine ⟨m, hm, ⟨2 ^ k, ?_⟩, ⟨2 ^ k, ?_⟩, hs⟩
  · dsimp [m]; omega
  · rfl

theorem finite_order_parity_not_definable :
    ¬ ∃ σ : ExpressiveLimits.language.Sentence, ∀ n : ℕ, 0 < n →
      (@Sentence.Realize ExpressiveLimits.language (Fin n) (orderStructure n) σ ↔ Even n) := by
  rintro ⟨σ, hσ⟩
  obtain ⟨m, hm, heven, hodd, heq⟩ := adjacent_sizes σ
  obtain ⟨j, hj⟩ := (hσ (m + 1) (by omega)).mp (heq.mp ((hσ m hm).mpr heven))
  obtain ⟨l, hl⟩ := hodd
  omega

theorem finite_order_oddness_not_definable :
    ¬ ∃ σ : ExpressiveLimits.language.Sentence, ∀ n : ℕ, 0 < n →
      (@Sentence.Realize ExpressiveLimits.language (Fin n) (orderStructure n) σ ↔ Odd n) := by
  rintro ⟨σ, hσ⟩
  obtain ⟨m, hm, heven, hodd, heq⟩ := adjacent_sizes σ
  obtain ⟨j, hj⟩ := (hσ m hm).mp (heq.mpr ((hσ (m + 1) (by omega)).mpr hodd))
  obtain ⟨l, hl⟩ := heven
  omega

end Lemmatheca.ModelTheory.FiniteStructureInexpressibility
