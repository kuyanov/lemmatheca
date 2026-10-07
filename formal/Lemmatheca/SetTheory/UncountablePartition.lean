import Lemmatheca.SetTheory.PartitionRelations
import Lemmatheca.SetTheory.Clubs
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Regular

/-! Two-colour asymmetric pair relations, Sierpiński at omega one and
Dushnik–Miller at regular infinite cardinals. Colours are 0 and 1 in Fin 2;
the domain consists of finite subsets of cardinality two, not ordered pairs. -/

noncomputable section
namespace Lemmatheca.SetTheory.UncountablePartition
open Set Cardinal
universe u

abbrev PairColoring (α : Type u) := PartitionRelations.Coloring α 2 (Fin 2)
abbrev OmegaOne := Clubs.Carrier (ℵ₁ : Cardinal.{0})

def AsymmetricRelation (α : Type u) (k₀ k₁ : Cardinal.{u}) : Prop :=
  ∀ c : PairColoring α,
    (∃ H : Set α, Cardinal.mk H = k₀ ∧ PartitionRelations.IsHomogeneousIn c H 0) ∨
    ∃ H : Set α, Cardinal.mk H = k₁ ∧ PartitionRelations.IsHomogeneousIn c H 1

def pairValue {α : Type u} (c : PairColoring α) (x y : α) : Fin 2 := by
  classical
  exact if h : x = y then 0 else c ⟨{x, y}, by simp [h]⟩

def oneNeighbors {α : Type u} (c : PairColoring α) (x : α) : Set α :=
  {y | y ≠ x ∧ pairValue c x y = 1}

theorem pairValue_symm {α : Type u} (c : PairColoring α) (x y : α) :
    pairValue c x y = pairValue c y x := by
  classical
  by_cases h : x = y
  · subst y; rfl
  · simp [pairValue, h, Ne.symm h, Finset.pair_comm]

theorem homogeneous_iff_pairwise {α : Type u} (c : PairColoring α) (H : Set α) (i : Fin 2) :
    PartitionRelations.IsHomogeneousIn c H i ↔
      H.Pairwise (fun x y => pairValue c x y = i) := by
  classical
  constructor
  · intro h x hx y hy hxy
    have hs : (↑({x, y} : Finset α) : Set α) ⊆ H := by
      intro z hz
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    simpa [pairValue, hxy] using h ⟨{x, y}, by simp [hxy]⟩ hs
  · intro h s hs
    obtain ⟨x, y, hxy, he⟩ := Finset.card_eq_two.mp s.property
    have hx : x ∈ H := hs (by simp [he])
    have hy : y ∈ H := hs (by simp [he])
    have hp := h hx hy hxy
    have hs' : s = ⟨{x, y}, by simp [hxy]⟩ := Subtype.ext he
    simpa [hs', pairValue, hxy] using hp

private theorem monotone_real_countable {α : Type} [LinearOrder α] [WellFoundedLT α]
    (f : α → ℝ) (hf : StrictMono f) : Countable α := by
  classical
  let : SuccOrder α := SuccOrder.ofLinearWellFoundedLT α
  let A : Set α := {x | ¬ IsMax x}
  have hex (x : A) : ∃ q : ℚ, f x.val < q ∧ (q : ℝ) < f (Order.succ x.val) :=
    exists_rat_btwn (hf (Order.lt_succ_of_not_isMax x.property))
  choose q hq₀ hq₁ using hex
  have hqi : Function.Injective q := by
    intro x y he
    apply Subtype.ext
    rcases lt_trichotomy x.val y.val with h | h | h
    · have hh := (hq₁ x).trans_le (hf.monotone (Order.succ_le_of_lt h))
      rw [he] at hh
      exact ((hq₀ y).not_gt hh).elim
    · exact h
    · have hh := (hq₁ y).trans_le (hf.monotone (Order.succ_le_of_lt h))
      rw [← he] at hh
      exact ((hq₀ x).not_gt hh).elim
  have hAc : A.Countable := Set.countable_coe_iff.mp (Function.Injective.countable hqi)
  have hBc : ({x : α | IsMax x} : Set α).Countable := by
    apply Set.Subsingleton.countable
    intro x hx y hy
    rcases le_total x y with h | h
    · exact le_antisymm h (hx h)
    · exact le_antisymm (hy h) h
  apply Set.countable_univ_iff.mp
  have hu : A ∪ {x : α | IsMax x} = Set.univ := by
    ext x
    exact ⟨fun _ => trivial, fun _ => Classical.em (IsMax x) |>.symm⟩
  exact hu ▸ hAc.union hBc

theorem no_long_monotone_reals (f : OmegaOne → ℝ) :
    ¬ StrictMono f ∧ ¬ StrictAnti f := by
  have hn : ¬ Countable OmegaOne := by
    intro h
    have hc := Cardinal.mk_le_aleph0_iff.mpr h
    have he : Cardinal.mk OmegaOne = ℵ₁ := by simp [OmegaOne, Clubs.Carrier]
    rw [he] at hc
    exact Cardinal.aleph0_lt_aleph_one.not_ge hc
  refine ⟨fun h => hn (monotone_real_countable f h), ?_⟩
  intro h
  exact hn (monotone_real_countable (fun x => -f x) fun x y hxy => neg_lt_neg (h hxy))

def sierpinskiColoring (r : OmegaOne → ℝ) : PairColoring OmegaOne := by
  classical
  exact fun s =>
    have hs : s.val.Nonempty := Finset.card_pos.mp (by rw [s.property]; decide)
    if r (s.val.min' hs) < r (s.val.max' hs) then 0 else 1

theorem sierpinskiColoring_pair (r : OmegaOne → ℝ) {x y : OmegaOne} (hxy : x < y) :
    pairValue (sierpinskiColoring r) x y = if r x < r y then 0 else 1 := by
  classical
  let : DecidableEq OmegaOne := Classical.decEq _
  have hs : ({x, y} : Finset OmegaOne).Nonempty := Finset.insert_nonempty _ _
  have hmin : ({x, y} : Finset OmegaOne).min' hs = x := by
    apply le_antisymm (Finset.min'_le _ _ (by simp))
    apply Finset.le_min'
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact le_rfl
    · exact hxy.le
  have hmax : ({x, y} : Finset OmegaOne).max' hs = y := by
    apply le_antisymm
    · apply Finset.max'_le
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hxy.le
      · exact le_rfl
    · exact Finset.le_max' _ _ (by simp)
  simp only [pairValue, dite_eq_right hxy.ne]
  unfold sierpinskiColoring
  simp only [hmin, hmax]

theorem sierpinskiColoring_no_uncountable (r : OmegaOne → ℝ)
    (hr : Function.Injective r) (H : Set OmegaOne) (hH : ¬ H.Countable) :
    ¬ PartitionRelations.IsHomogeneous (sierpinskiColoring r) H := by
  rintro ⟨i, hi⟩
  have hp := (homogeneous_iff_pairwise _ _ _).mp hi
  fin_cases i
  · have hm : StrictMono (fun x : H => r x.val) := by
      intro x y hxy
      have hc := hp x.property y.property (ne_of_lt hxy)
      change pairValue (sierpinskiColoring r) x.val y.val = 0 at hc
      rw [sierpinskiColoring_pair r hxy] at hc
      split_ifs at hc with h
      · exact h
      · contradiction
    exact hH (Set.countable_coe_iff.mp (monotone_real_countable _ hm))
  · have hm : StrictMono (fun x : H => -r x.val) := by
      intro x y hxy
      have hc := hp x.property y.property (ne_of_lt hxy)
      change pairValue (sierpinskiColoring r) x.val y.val = 1 at hc
      rw [sierpinskiColoring_pair r hxy] at hc
      have hle : r y.val ≤ r x.val := by
        split_ifs at hc with h
        · contradiction
        · exact le_of_not_gt h
      exact neg_lt_neg (hle.lt_of_ne fun he => (ne_of_lt hxy) (Subtype.ext (hr he).symm))
    exact hH (Set.countable_coe_iff.mp (monotone_real_countable _ hm))

theorem sierpinski :
    ∃ c : PairColoring OmegaOne, ∀ H : Set OmegaOne, ¬ H.Countable →
      ¬ PartitionRelations.IsHomogeneous c H := by
  have hc : Cardinal.mk OmegaOne ≤ Cardinal.mk ℝ := by
    simpa [OmegaOne, Clubs.Carrier, Cardinal.mk_real] using Cardinal.aleph_one_le_continuum
  obtain ⟨r⟩ := (Cardinal.le_def _ _).mp hc
  exact ⟨sierpinskiColoring r, fun H hH => sierpinskiColoring_no_uncountable r r.injective H hH⟩

theorem neighborhood_dichotomy {α : Type u} (c : PairColoring α) (κ : Cardinal.{u}) :
    ((∀ X : Set α, Cardinal.mk X = κ →
      ∃ x ∈ X, Cardinal.mk ((oneNeighbors c x ∩ X) : Set α) = κ) ∨
    ∃ X : Set α, Cardinal.mk X = κ ∧
      ∀ x ∈ X, Cardinal.mk ((oneNeighbors c x ∩ X) : Set α) < κ) ∧
    ¬ ((∀ X : Set α, Cardinal.mk X = κ →
      ∃ x ∈ X, Cardinal.mk ((oneNeighbors c x ∩ X) : Set α) = κ) ∧
    ∃ X : Set α, Cardinal.mk X = κ ∧
      ∀ x ∈ X, Cardinal.mk ((oneNeighbors c x ∩ X) : Set α) < κ) := by
  classical
  refine ⟨?_, ?_⟩
  · by_cases h : ∀ X : Set α, Cardinal.mk X = κ →
        ∃ x ∈ X, Cardinal.mk ((oneNeighbors c x ∩ X) : Set α) = κ
    · exact Or.inl h
    · right
      push Not at h
      obtain ⟨X, hX, hn⟩ := h
      refine ⟨X, hX, fun x hx => ?_⟩
      exact lt_of_le_of_ne ((Cardinal.mk_le_mk_of_subset inter_subset_right).trans_eq hX)
        (hn x hx)
  · rintro ⟨hlarge, X, hX, hsmall⟩
    obtain ⟨x, hx, he⟩ := hlarge X hX
    exact (hsmall x hx).ne he

theorem dushnik_miller {α : Type u} (hα : (Cardinal.mk α).IsRegular) :
    AsymmetricRelation α (Cardinal.mk α) ℵ₀ := by
  classical
  intro c
  let κ := Cardinal.mk α
  rcases (neighborhood_dichotomy c κ).1 with hlarge | ⟨X, hX, hsmall⟩
  · right
    let State := {X : Set α // Cardinal.mk X = κ}
    have hex (S : State) : ∃ x ∈ S.val,
        Cardinal.mk ((oneNeighbors c x ∩ S.val) : Set α) = κ := hlarge S.val S.property
    choose pick hpick hnext using hex
    let next : State → State := fun S => ⟨oneNeighbors c (pick S) ∩ S.val, hnext S⟩
    let states : ℕ → State := fun n => next^[n] ⟨Set.univ, Cardinal.mk_univ⟩
    let x : ℕ → α := fun n => pick (states n)
    have hstep (n : ℕ) : (states (n + 1)).val = oneNeighbors c (x n) ∩ (states n).val := by
      dsimp only [states]
      rw [Function.iterate_succ_apply']
    have hdesc : Antitone (fun n => (states n).val) := by
      apply antitone_nat_of_succ_le
      intro n
      rw [hstep]
      exact inter_subset_right
    have hx (n : ℕ) : x n ∈ (states n).val := hpick (states n)
    have hpair (m n : ℕ) (hmn : m < n) : x n ≠ x m ∧ pairValue c (x m) (x n) = 1 := by
      have hmem := hdesc (Nat.succ_le_of_lt hmn) (hx n)
      change x n ∈ (states (m + 1)).val at hmem
      rw [hstep] at hmem
      exact hmem.1
    have hxi : Function.Injective x := by
      intro m n he
      rcases lt_trichotomy m n with h | h | h
      · exact ((hpair m n h).1 he.symm).elim
      · exact h
      · exact ((hpair n m h).1 he).elim
    refine ⟨range x, ?_, (homogeneous_iff_pairwise c (range x) 1).mpr ?_⟩
    · simpa using Cardinal.mk_range_eq_of_injective hxi
    · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ hne
      have hmn : m ≠ n := fun he => hne (congrArg x he)
      rcases lt_or_gt_of_ne hmn with h | h
      · exact (hpair m n h).2
      · rw [pairValue_symm]
        exact (hpair n m h).2
  · left
    let good : Set (Set α) := {Z | Z ⊆ X ∧ Z.Pairwise (fun x y => pairValue c x y = 0)}
    have hchains : ∀ C ⊆ good, IsChain (· ⊆ ·) C → C.Nonempty →
        ∃ ub ∈ good, ∀ Z ∈ C, Z ⊆ ub := by
      intro C hC hchain _
      refine ⟨⋃₀ C, ⟨sUnion_subset fun Z hZ => (hC hZ).1, ?_⟩,
        fun Z hZ => subset_sUnion_of_mem hZ⟩
      rintro x ⟨Z, hZ, hx⟩ y ⟨W, hW, hy⟩ hxy
      rcases hchain.total hZ hW with hZW | hWZ
      · exact (hC hW).2 (hZW hx) hy hxy
      · exact (hC hZ).2 hx (hWZ hy) hxy
    obtain ⟨Z, _, hZ⟩ := zorn_subset_nonempty good hchains ∅ ⟨empty_subset _, Set.pairwise_empty _⟩
    have hcover : X ⊆ Z ∪ ⋃ z : Z, oneNeighbors c z.val ∩ X := by
      intro x hx
      by_contra h
      have hxZ : x ∉ Z := fun hZ => h (Or.inl hZ)
      have hzero (z : α) (hz : z ∈ Z) : pairValue c x z = 0 := by
        have hn : pairValue c z x ≠ 1 := by
          intro he
          exact h (Or.inr (mem_iUnion.mpr ⟨⟨z, hz⟩,
            ⟨⟨fun heq => hxZ (heq ▸ hz), he⟩, hx⟩⟩))
        rw [pairValue_symm]
        apply Fin.ext
        have hv := (pairValue c z x).isLt
        have hv' : (pairValue c z x).val ≠ 1 := fun he => hn (Fin.ext he)
        simp only [Fin.val_zero]
        omega
      have hins : insert x Z ∈ good := by
        refine ⟨insert_subset hx hZ.1.1, hZ.1.2.insert ?_⟩
        intro z hz _
        exact ⟨hzero z hz, (pairValue_symm c z x).trans (hzero z hz)⟩
      have he := hZ.2 hins (subset_insert x Z)
      exact hxZ (he (mem_insert x Z))
    have hcard : Cardinal.mk Z = κ := by
      apply le_antisymm_iff.mpr
      refine ⟨(Cardinal.mk_le_mk_of_subset hZ.1.1).trans_eq hX, ?_⟩
      by_contra h
      have hZsmall : Cardinal.mk Z < κ := lt_of_not_ge h
      have hUsmall : Cardinal.mk (⋃ z : Z, oneNeighbors c z.val ∩ X) < κ :=
        (Cardinal.card_iUnion_lt_iff_forall_of_isRegular hα hZsmall).mpr
          (fun z => hsmall z.val (hZ.1.1 z.property))
      have hsum : Cardinal.mk Z + Cardinal.mk (⋃ z : Z, oneNeighbors c z.val ∩ X) < κ :=
        Cardinal.add_lt_of_lt hα.aleph0_le hZsmall hUsmall
      have hc := (Cardinal.mk_le_mk_of_subset hcover).trans
        (Cardinal.mk_union_le _ _) |>.trans_lt hsum
      exact (hX ▸ hc).false
    exact ⟨Z, hcard, (homogeneous_iff_pairwise c Z 0).mpr hZ.1.2⟩


theorem sierpinski_countable_second_colour (c : PairColoring OmegaOne)
    (hc : ∀ H : Set OmegaOne, ¬ H.Countable → ¬ PartitionRelations.IsHomogeneous c H) :
    ∃ H : Set OmegaOne, Cardinal.mk H = ℵ₀ ∧
      PartitionRelations.IsHomogeneousIn c H 1 := by
  have hr : (ℵ₁ : Cardinal.{0}).IsRegular := Cardinal.isRegular_aleph_one
  have he : Cardinal.mk OmegaOne = ℵ₁ := by simp [OmegaOne, Clubs.Carrier]
  have hregular : (Cardinal.mk OmegaOne).IsRegular := he ▸ hr
  rcases dushnik_miller hregular c with ⟨H, hH, hh⟩ | h
  · have hn : ¬ H.Countable := by
      intro hcH
      have hle := hcH.le_aleph0
      rw [hH, he] at hle
      exact Cardinal.aleph0_lt_aleph_one.not_ge hle
    exact (hc H hn ⟨0, hh⟩).elim
  · exact h

end Lemmatheca.SetTheory.UncountablePartition
