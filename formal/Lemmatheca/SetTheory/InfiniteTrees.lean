import Lemmatheca.SetTheory.Cofinality
import Lemmatheca.SetTheory.ChoicePrinciples
import Lemmatheca.SetTheory.AlmostDisjoint
import Mathlib.Order.KonigLemma
import Mathlib.Order.Antichain
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Ordinal.FundamentalSequence
import Mathlib.Data.List.Infix
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Data.Finsupp.Encodable

/-! Transfinite trees, finite modifications, and the coherent-injection
construction of an Aronszajn tree. A branch is a downward-closed chain.
Function domains are initial segments of the small carrier `θ.ToType`; their
ordinal positions represent the ordinals below θ without changing universes.
-/

noncomputable section

namespace Lemmatheca.SetTheory.InfiniteTrees

open Set Filter Cardinal
open scoped Ordinal
universe u v

/-- A partially ordered carrier with well-ordered strict predecessor sets. -/
structure Tree where
  carrier : Type u
  [partialOrder : PartialOrder carrier]
  predecessors_wellOrdered : ∀ t : carrier, IsWellOrder (Set.Iio t) (· < ·)

attribute [instance] Tree.partialOrder
attribute [instance] Tree.predecessors_wellOrdered
instance : CoeSort Tree (Type u) := ⟨Tree.carrier⟩

noncomputable def nodeHeight (T : Tree.{u}) (t : T) : Ordinal.{u} :=
  letI := T.predecessors_wellOrdered t
  Ordinal.type ((· < ·) : Set.Iio t → Set.Iio t → Prop)

def level (T : Tree.{u}) (a : Ordinal.{u}) : Set T := {t | nodeHeight T t = a}

noncomputable def treeHeight (T : Tree.{u}) : Ordinal.{u} := ⨆ t : T, nodeHeight T t + 1

def IsBranch (T : Tree.{u}) (B : Set T) : Prop := IsChain (· ≤ ·) B ∧ IsLowerSet B

def IsCofinalBranch (T : Tree.{u}) (B : Set T) : Prop :=
  IsBranch T B ∧ ∀ a < treeHeight T, (B ∩ level T a).Nonempty

def IsKappaTree (T : Tree.{u}) (κ : Cardinal.{u}) : Prop :=
  ℵ₀ ≤ κ ∧ treeHeight T = κ.ord ∧ ∀ a < κ.ord, Cardinal.mk (level T a) < κ

def IsAronszajnTree (T : Tree.{u}) (κ : Cardinal.{u}) : Prop :=
  IsKappaTree T κ ∧ ¬ ∃ B, IsCofinalBranch T B

theorem height_empty (T : Tree.{u}) [IsEmpty T] : treeHeight T = 0 := by
  simp [treeHeight]

theorem level_zero_iff (T : Tree.{u}) (t : T) :
    t ∈ level T 0 ↔ ∀ s : T, ¬ s < t := by
  letI := T.predecessors_wellOrdered t
  change Ordinal.type ((· < ·) : Set.Iio t → Set.Iio t → Prop) = 0 ↔ _
  rw [Ordinal.type_eq_zero_iff_isEmpty]
  constructor
  · intro h s hs
    exact h.false ⟨s, hs⟩
  · intro h
    exact ⟨fun s => h s.1 s.2⟩

private def tree_predecessorRelIso (T : Tree.{u}) {s t : T} (hs : s < t) :
    ((· < ·) : Set.Iio s → Set.Iio s → Prop) ≃r
      ((· < ·) : Set.Iio (⟨s, hs⟩ : Set.Iio t) →
        Set.Iio (⟨s, hs⟩ : Set.Iio t) → Prop) where
  toFun x := ⟨⟨x.1, x.2.trans hs⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private theorem tree_height_typein (T : Tree.{u}) {s t : T} (hs : s < t) :
    nodeHeight T s = Ordinal.typein (α := Set.Iio t) (· < ·) ⟨s, hs⟩ := by
  letI := T.predecessors_wellOrdered t
  letI := T.predecessors_wellOrdered s
  letI := IsWellOrder.linearOrder ((· < ·) : Set.Iio t → Set.Iio t → Prop)
  rw [nodeHeight, ← Ordinal.type_Iio_lt]
  exact (tree_predecessorRelIso T hs).ordinal_type_eq

theorem unique_predecessor (T : Tree.{u}) (t : T) (a : Ordinal.{u})
    (ha : a < nodeHeight T t) : ∃! s : T, s < t ∧ nodeHeight T s = a := by
  letI := T.predecessors_wellOrdered t
  obtain ⟨s, hs⟩ := Ordinal.typein_surj (α := Set.Iio t) (· < ·) ha
  refine ⟨s.1, ⟨s.2, (tree_height_typein T s.2).trans hs⟩, ?_⟩
  intro r hr
  have he : (⟨r, hr.1⟩ : Set.Iio t) = s :=
    Ordinal.typein_injective (α := Set.Iio t) (· < ·)
      (((tree_height_typein T hr.1).symm.trans hr.2).trans hs.symm)
  exact congrArg Subtype.val he

theorem nodeHeight_strictMono (T : Tree.{u}) : StrictMono (nodeHeight T) := by
  intro s t hs
  letI := T.predecessors_wellOrdered t
  rw [tree_height_typein T hs]
  exact Ordinal.typein_lt_type (α := Set.Iio t) (· < ·) ⟨s, hs⟩

theorem lower_levels_nonempty (T : Tree.{u}) {a b : Ordinal.{u}}
    (hab : a < b) (hb : (level T b).Nonempty) : (level T a).Nonempty := by
  obtain ⟨t, ht⟩ := hb
  obtain ⟨s, hs, _⟩ := unique_predecessor T t a (ht ▸ hab)
  exact ⟨s, hs.2⟩

theorem levels_antichain (T : Tree.{u}) (a : Ordinal.{u}) :
    IsAntichain (· ≤ ·) (level T a) := by
  intro s hs t ht hne hst
  have := nodeHeight_strictMono T (lt_of_le_of_ne hst hne)
  change nodeHeight T s = a at hs
  change nodeHeight T t = a at ht
  rw [hs, ht] at this
  exact this.false

theorem branch_height_injective (T : Tree.{u}) {B : Set T} (hB : IsBranch T B) :
    Function.Injective (fun t : B => nodeHeight T t) := by
  intro s t he
  apply Subtype.ext
  rcases hB.1.total s.2 t.2 with hst | hts
  · by_contra hn
    exact (nodeHeight_strictMono T (lt_of_le_of_ne hst hn)).ne he
  · by_contra hn
    exact (nodeHeight_strictMono T (lt_of_le_of_ne hts (Ne.symm hn))).ne he.symm

theorem branch_wellOrdered (T : Tree.{u}) {B : Set T} (hB : IsBranch T B) :
    IsWellOrder B (· < ·) := by
  let e : ((· < ·) : B → B → Prop) ↪r ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop) :=
    { toFun := fun t => nodeHeight T t
      inj' := branch_height_injective T hB
      map_rel_iff' := by
        intro s t
        constructor
        · intro h
          change s.1 < t.1
          rcases hB.1.total s.2 t.2 with hst | hts
          · exact lt_of_le_of_ne hst (fun he => h.ne (congrArg (nodeHeight T) he))
          · exact (h.not_ge ((nodeHeight_strictMono T).monotone hts)).elim
        · exact fun h => nodeHeight_strictMono T h }
  exact e.isWellOrder

noncomputable def branchOrderType (T : Tree.{u}) (B : Set T) (hB : IsBranch T B) :
    Ordinal.{u} :=
  letI := branch_wellOrdered T hB
  Ordinal.type ((· < ·) : B → B → Prop)

private theorem tree_branch_typein (T : Tree.{u}) {B : Set T} (hB : IsBranch T B)
    [IsWellOrder B (· < ·)] (t : B) :
    nodeHeight T t = Ordinal.typein (α := B) (· < ·) t := by
  letI := IsWellOrder.linearOrder ((· < ·) : B → B → Prop)
  let e : ((· < ·) : Set.Iio t.1 → Set.Iio t.1 → Prop) ≃r
      ((· < ·) : Set.Iio t → Set.Iio t → Prop) :=
    { toFun := fun x => ⟨⟨x.1, hB.2 x.2.le t.2⟩, x.2⟩
      invFun := fun x => ⟨x.1.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  rw [nodeHeight, ← Ordinal.type_Iio_lt]
  exact e.ordinalType_congr

private theorem tree_nodeHeight_lt_height (T : Tree.{u}) (t : T) :
    nodeHeight T t < treeHeight T :=
  (lt_add_one _).trans_le (Ordinal.le_iSup (fun t : T => nodeHeight T t + 1) t)

theorem cofinal_branch_orderType (T : Tree.{u}) {B : Set T} (hB : IsCofinalBranch T B) :
    branchOrderType T B hB.1 = treeHeight T := by
  letI := branch_wellOrdered T hB.1
  apply le_antisymm
  · apply le_of_forall_lt
    intro a ha
    obtain ⟨t, ht⟩ := Ordinal.typein_surj (α := B) (· < ·) ha
    exact ht ▸ (tree_branch_typein T hB.1 t) ▸ tree_nodeHeight_lt_height T t
  · apply le_of_forall_lt
    intro a ha
    obtain ⟨t, ht, he⟩ := hB.2 a ha
    have := Ordinal.typein_lt_type (α := B) (· < ·) ⟨t, ht⟩
    rw [← tree_branch_typein T hB.1 ⟨t, ht⟩, he] at this
    exact this

theorem cofinal_iff_unbounded (T : Tree.{u}) {B : Set T} (hB : IsBranch T B)
    (hlim : Order.IsSuccLimit (treeHeight T)) :
    IsCofinalBranch T B ↔ ∀ a < treeHeight T, ∃ t ∈ B, a < nodeHeight T t := by
  constructor
  · intro h a ha
    obtain ⟨t, ht, he⟩ := h.2 (Order.succ a) (hlim.succ_lt ha)
    exact ⟨t, ht, he ▸ Order.lt_succ a⟩
  · intro h
    refine ⟨hB, fun a ha => ?_⟩
    obtain ⟨t, ht, hat⟩ := h a ha
    obtain ⟨s, hs, _⟩ := unique_predecessor T t a hat
    exact ⟨s, hB.2 hs.1.le ht, hs.2⟩

theorem maximal_chain_downward_closed (T : Tree.{u}) {B : Set T}
    (hB : IsMaxChain (· ≤ ·) B) : IsBranch T B := by
  refine ⟨hB.1, ?_⟩
  intro t s hst ht
  have hc : IsChain (· ≤ ·) (insert s B) := hB.1.insert fun r hr _ => by
    rcases hB.1.total ht hr with htr | hrt
    · exact Or.inl (hst.trans htr)
    · rcases hst.eq_or_lt with he | hs
      · exact Or.inr (he ▸ hrt)
      rcases hrt.eq_or_lt with he | hrlt
      · exact Or.inl (he ▸ hst)
      letI := T.predecessors_wellOrdered t
      rcases trichotomous_of ((· < ·) : Set.Iio t → Set.Iio t → Prop)
          ⟨s, hs⟩ ⟨r, hrlt⟩ with h | h | h
      · exact Or.inl h.le
      · exact Or.inl (congrArg Subtype.val h).le
      · exact Or.inr h.le
  exact (hB.2 hc (subset_insert _ _)).symm ▸ mem_insert s B

theorem cofinal_branch_maximal (T : Tree.{u}) {B : Set T} (hB : IsCofinalBranch T B) :
    IsMaxChain (· ≤ ·) B := by
  refine ⟨hB.1.1, ?_⟩
  intro C hC hBC
  apply Subset.antisymm hBC
  intro t ht
  obtain ⟨s, hs, he⟩ := hB.2 (nodeHeight T t) (tree_nodeHeight_lt_height T t)
  have hts : t = s := by
    rcases hC.total ht (hBC hs) with h | h
    · by_contra hn
      exact (nodeHeight_strictMono T (lt_of_le_of_ne h hn)).ne he.symm
    · by_contra hn
      exact (nodeHeight_strictMono T (lt_of_le_of_ne h (Ne.symm hn))).ne he
  exact hts ▸ hs

/-- The finite-level form of König's lemma, allowing several roots. -/
private theorem tree_lower_comparable (T : Tree.{u}) {s r t : T}
    (hs : s ≤ t) (hr : r ≤ t) : s ≤ r ∨ r ≤ s := by
  rcases hs.eq_or_lt with he | hs
  · exact Or.inr (he ▸ hr)
  rcases hr.eq_or_lt with he | hr
  · exact Or.inl (he ▸ hs.le)
  rcases trichotomous_of ((· < ·) : Set.Iio t → Set.Iio t → Prop)
      ⟨s, hs⟩ ⟨r, hr⟩ with h | h | h
  · exact Or.inl h.le
  · exact Or.inl (congrArg Subtype.val h).le
  · exact Or.inr h.le

private theorem tree_ancestor_unique (T : Tree.{u}) {s r t : T}
    (hs : s ≤ t) (hr : r ≤ t) (he : nodeHeight T s = nodeHeight T r) : s = r := by
  rcases tree_lower_comparable T hs hr with h | h
  · by_contra hn
    exact (nodeHeight_strictMono T (lt_of_le_of_ne h hn)).ne he
  · by_contra hn
    exact (nodeHeight_strictMono T (lt_of_le_of_ne h (Ne.symm hn))).ne he.symm

private theorem tree_ancestor_exists (T : Tree.{u}) (t : T) (a : Ordinal.{u})
    (ha : a ≤ nodeHeight T t) : ∃ s, s ≤ t ∧ nodeHeight T s = a := by
  rcases ha.eq_or_lt with he | ha
  · exact ⟨t, le_rfl, he.symm⟩
  obtain ⟨s, hs, _⟩ := unique_predecessor T t a ha
  exact ⟨s, hs.1.le, hs.2⟩

private theorem tree_level_nonempty (T : Tree.{u}) (a : Ordinal.{u})
    (ha : a < treeHeight T) : (level T a).Nonempty := by
  obtain ⟨t, ht⟩ := Ordinal.lt_iSup_add_one_iff.mp ha
  obtain ⟨s, _, he⟩ := tree_ancestor_exists T t a ht
  exact ⟨s, he⟩

theorem konig (T : Tree.{u}) (hheight : treeHeight T = Ordinal.omega 0)
    (hfinite : ∀ n : ℕ, (level T n).Finite) : ∃ B, IsCofinalBranch T B := by
  classical
  have hheight' : treeHeight T = Ordinal.omega0 := hheight.trans Ordinal.omega_zero
  let A (n : ℕ) := level T n
  haveI (n : ℕ) : Finite (A n) := (hfinite n).to_subtype
  haveI (n : ℕ) : Nonempty (A n) :=
    (tree_level_nonempty T n (hheight' ▸ Ordinal.natCast_lt_omega0 n)).to_subtype
  have ancestors (i j : ℕ) (hij : i ≤ j) (t : A j) :
      ∃ s : A i, s.1 ≤ t.1 := by
    obtain ⟨s, hs, he⟩ := tree_ancestor_exists T t i (t.2 ▸ by exact_mod_cast hij)
    exact ⟨⟨s, he⟩, hs⟩
  let π : {i j : ℕ} → (hij : i ≤ j) → A j → A i :=
    fun {i j} hij t => (ancestors i j hij t).choose
  have hπ {i j : ℕ} (hij : i ≤ j) (t : A j) : (π hij t).1 ≤ t.1 :=
    (ancestors i j hij t).choose_spec
  have hrefl (i : ℕ) (t : A i) : π le_rfl t = t := by
    apply Subtype.ext
    exact tree_ancestor_unique T (hπ le_rfl t) le_rfl ((π le_rfl t).2.trans t.2.symm)
  have htrans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (t : A k) :
      π hij (π hjk t) = π (hij.trans hjk) t := by
    apply Subtype.ext
    exact tree_ancestor_unique T ((hπ hij (π hjk t)).trans (hπ hjk t))
      (hπ (hij.trans hjk) t)
      ((π hij (π hjk t)).2.trans (π (hij.trans hjk) t).2.symm)
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite π
    (fun {_} t => hrefl _ t) (fun {i j k} hij hjk t => htrans hij hjk t)
    (fun i _ => Set.toFinite _)
  let B : Set T := range (fun n => (f n).1)
  have hle {i j : ℕ} (hij : i ≤ j) : (f i).1 ≤ (f j).1 := by
    rw [← hf hij]
    exact hπ hij (f j)
  refine ⟨B, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · rintro s ⟨i, rfl⟩ t ⟨j, rfl⟩ _
    exact (le_total i j).imp hle hle
  · intro t s hst ht
    obtain ⟨n, rfl⟩ := ht
    obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp (hheight' ▸ tree_nodeHeight_lt_height T s)
    have hkn : k ≤ n := by
      have := (nodeHeight_strictMono T).monotone hst
      rw [hk, (f n).2] at this
      exact_mod_cast this
    exact ⟨k, tree_ancestor_unique T (hle hkn) hst ((f k).2.trans hk.symm)⟩
  · intro a ha
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (hheight' ▸ ha)
    exact ⟨(f n).1, ⟨n, rfl⟩, (f n).2⟩

theorem no_omega_aronszajn (T : Tree.{u}) : ¬ IsAronszajnTree T ℵ₀ := by
  rintro ⟨hT, hn⟩
  apply hn
  apply konig T (by simpa using hT.2.1)
  intro n
  exact Cardinal.lt_aleph0_iff_set_finite.mp
    (hT.2.2 n (by simpa using Ordinal.natCast_lt_omega0 n))

/-- A function together with its initial-segment domain. -/
def FunctionNode (θ : Ordinal.{u}) (X : Type u) := Σ a : θ.ToType, Set.Iio a → X

def initialSegmentEmbedding {θ : Ordinal.{u}} {a b : θ.ToType} (h : a ≤ b) :
    Set.Iio a ↪ Set.Iio b where
  toFun i := ⟨i.1, lt_of_lt_of_le i.2 h⟩
  inj' := by
    intro i j he
    apply Subtype.ext
    exact congrArg (fun x : Set.Iio b => x.1) he

def Extends {θ : Ordinal.{u}} {X : Type u} (s t : FunctionNode θ X) : Prop :=
  ∃ h : s.1 ≤ t.1, s.2 = t.2 ∘ initialSegmentEmbedding h

instance functionNodePartialOrder {θ : Ordinal.{u}} {X : Type u} :
    PartialOrder (FunctionNode θ X) where
  le := Extends
  le_refl := by
    intro s
    exact ⟨le_rfl, by funext i; rfl⟩
  le_trans := by
    rintro s t r ⟨hst, he⟩ ⟨htr, hf⟩
    refine ⟨hst.trans htr, ?_⟩
    funext i
    exact (congrFun he i).trans (congrFun hf (initialSegmentEmbedding hst i))
  le_antisymm := by
    rintro ⟨a, s⟩ ⟨b, t⟩ ⟨hab, he⟩ ⟨hba, _⟩
    obtain rfl := hab.antisymm hba
    exact congrArg (Sigma.mk a) (show s = t from he)

def restrictNode {θ : Ordinal.{u}} {X : Type u} (s : FunctionNode θ X)
    (b : θ.ToType) (h : b ≤ s.1) : FunctionNode θ X :=
  ⟨b, s.2 ∘ initialSegmentEmbedding h⟩

private theorem tree_function_lt_iff {θ : Ordinal.{u}} {X : Type u}
    (s t : FunctionNode θ X) : s < t ↔ s ≤ t ∧ s.1 < t.1 := by
  conv_lhs => rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨⟨h, he⟩, hn⟩
    refine ⟨⟨h, he⟩, lt_of_le_of_ne h ?_⟩
    intro heq
    apply hn
    apply Sigma.ext heq
    rcases s with ⟨a, f⟩
    rcases t with ⟨b, g⟩
    dsimp at heq
    subst b
    exact heq_of_eq he
  · rintro ⟨h, hab⟩
    exact ⟨h, fun he => hab.ne (congrArg Sigma.fst he)⟩

private theorem tree_restrict_le {θ : Ordinal.{u}} {X : Type u}
    (t : FunctionNode θ X) (b c : θ.ToType) (hb : b ≤ t.1) (hc : c ≤ t.1) :
    restrictNode t b hb ≤ restrictNode t c hc ↔ b ≤ c := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, by funext i; rfl⟩

private theorem tree_eq_restrict {θ : Ordinal.{u}} {X : Type u}
    (s t : FunctionNode θ X) (h : s ≤ t) :
    s = restrictNode t s.1 h.1 := by
  rcases s with ⟨a, f⟩
  rcases t with ⟨b, g⟩
  exact congrArg (Sigma.mk a) h.2

def RestrictionClosed {θ : Ordinal.{u}} {X : Type u}
    (S : Set (FunctionNode θ X)) : Prop :=
  ∀ s ∈ S, ∀ b (h : b ≤ s.1), restrictNode s b h ∈ S

private def tree_function_predIso {θ : Ordinal.{u}} {X : Type u}
    (S : Set (FunctionNode θ X)) (hS : RestrictionClosed S) (t : S) :
    Set.Iio t ≃o Set.Iio t.1.1 where
  toFun p := ⟨p.1.1.1, ((tree_function_lt_iff p.1.1 t.1).mp p.2).2⟩
  invFun b := ⟨⟨restrictNode t.1 b.1 b.2.le, hS t.1 t.2 b.1 b.2.le⟩,
    (tree_function_lt_iff _ _).mpr
      ⟨(tree_restrict_le t.1 b.1 t.1.1 b.2.le le_rfl).mpr b.2.le, b.2⟩⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact (tree_eq_restrict p.1.1 t.1 p.2.le).symm
  right_inv _ := rfl
  map_rel_iff' := by
    intro p q
    constructor
    · intro hpq
      change p.1.1 ≤ q.1.1
      rw [tree_eq_restrict p.1.1 t.1 p.2.le, tree_eq_restrict q.1.1 t.1 q.2.le]
      exact (tree_restrict_le t.1 _ _ _ _).mpr hpq
    · exact fun h => h.1

def functionTree {θ : Ordinal.{u}} {X : Type u}
    (S : Set (FunctionNode θ X)) (hS : RestrictionClosed S) : Tree.{u} where
  carrier := S
  predecessors_wellOrdered := by
    intro t
    exact (tree_function_predIso S hS t).toOrderEmbedding.isWellOrder

def fullFunctionTree (θ : Ordinal.{u}) (X : Type u) : Tree.{u} :=
  functionTree (Set.univ : Set (FunctionNode θ X)) (by intro s hs b hb; trivial)

private def tree_positionIso {θ : Ordinal.{u}} (a : θ.ToType) :
    Set.Iio a ≃o Set.Iio a.toOrd.1 where
  toFun x := ⟨x.1.toOrd.1, ((Ordinal.ToType.mk (o := θ)).symm.strictMono x.2)⟩
  invFun x := ⟨(Ordinal.ToType.mk (o := θ))
      ⟨x.1, by exact (lt_trans (show x.1 < a.toOrd.1 from x.2)
        (show a.toOrd.1 < θ from a.toOrd.2))⟩, by
    have h : (⟨x.1, (lt_trans (show x.1 < a.toOrd.1 from x.2)
      (show a.toOrd.1 < θ from a.toOrd.2))⟩ : Set.Iio θ) < a.toOrd := x.2
    simpa using (Ordinal.ToType.mk (o := θ)).strictMono h⟩
  left_inv x := by
    apply Subtype.ext
    change (Ordinal.ToType.mk (o := θ)) ((Ordinal.ToType.mk (o := θ)).symm x.1) = x.1
    exact (Ordinal.ToType.mk (o := θ)).apply_symm_apply x.1
  right_inv _ := by simp
  map_rel_iff' := by
    intro x y
    exact (Ordinal.ToType.mk (o := θ)).symm.le_iff_le

private theorem tree_position_type {θ : Ordinal.{u}} (a : θ.ToType) :
    typeLT (Set.Iio a) = a.toOrd.1 := by
  apply (Ordinal.lift_inj.{u + 1, u}).mp
  rw [(tree_positionIso a).toRelIsoLT.ordinal_lift_type_eq,
    Ordinal.lift_id'.{u, u + 1}, Ordinal.type_lt_Iio]

theorem functionTree_nodeHeight {θ : Ordinal.{u}} {X : Type u}
    (S : Set (FunctionNode θ X)) (hS : RestrictionClosed S) (t : functionTree S hS) :
    nodeHeight (functionTree S hS) t = t.1.1.toOrd.1 := by
  letI := (tree_function_predIso S hS t).toOrderEmbedding.isWellOrder
  exact ((tree_function_predIso S hS t).toRelIsoLT.ordinalType_congr).trans
    (tree_position_type t.1.1)

theorem functionTree_predecessors {θ : Ordinal.{u}} {X : Type u}
    (S : Set (FunctionNode θ X)) (hS : RestrictionClosed S) (s t : functionTree S hS) :
    s < t ↔ ∃ (b : θ.ToType) (h : b < t.1.1), s.1 = restrictNode t.1 b h.le := by
  constructor
  · intro h
    have hc := (tree_function_lt_iff s.1 t.1).mp h
    exact ⟨s.1.1, hc.2, tree_eq_restrict s.1 t.1 hc.1⟩
  · rintro ⟨b, hb, he⟩
    change s.1 < t.1
    rw [he]
    apply (tree_function_lt_iff _ _).mpr
    exact ⟨⟨hb.le, rfl⟩, hb⟩

theorem fullFunctionTree_height (θ : Ordinal.{u}) (X : Type u) [Nonempty X] :
    treeHeight (fullFunctionTree θ X) = θ := by
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro t
    have he : nodeHeight (fullFunctionTree θ X) t = t.1.1.toOrd.1 :=
      functionTree_nodeHeight (Set.univ : Set (FunctionNode θ X))
        (by intro s hs b hb; trivial) t
    rw [he]
    exact Order.add_one_le_of_lt t.1.1.toOrd.2
  · apply le_of_forall_lt
    intro a ha
    let t : fullFunctionTree θ X :=
      ⟨⟨Ordinal.ToType.mk ⟨a, ha⟩, fun _ => Classical.arbitrary X⟩, mem_univ _⟩
    have he : nodeHeight (fullFunctionTree θ X) t = a := by
      exact (functionTree_nodeHeight (Set.univ : Set (FunctionNode θ X))
        (by intro s hs b hb; trivial) t).trans (by simp [t])
    exact he ▸ tree_nodeHeight_lt_height (fullFunctionTree θ X) t

/-- Finite words equipped specifically with the prefix partial order. -/
def WordNode (X : Type u) := List X

instance wordNodePartialOrder {X : Type u} : PartialOrder (WordNode X) where
  le s t := List.IsPrefix s t
  le_refl := fun _ => List.prefix_rfl
  le_trans := fun _ _ _ => List.IsPrefix.trans
  le_antisymm := fun _ _ hst hts => hst.eq_of_length (hst.length_le.antisymm hts.length_le)

private theorem word_lt_iff {X : Type u} (s t : WordNode X) :
    s < t ↔ s.IsPrefix t ∧ s.length < t.length := by
  rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨h, lt_of_le_of_ne h.length_le (fun he => hn (h.eq_of_length he))⟩
  · rintro ⟨h, hl⟩
    exact ⟨h, fun he => hl.ne (congrArg List.length he)⟩

def PrefixClosed {X : Type u} (S : Set (WordNode X)) : Prop :=
  ∀ t ∈ S, ∀ s, List.IsPrefix s t → s ∈ S

private def word_predIso {X : Type u} (S : Set (WordNode X))
    (hS : PrefixClosed S) (t : S) : Set.Iio t ≃o Fin t.1.length where
  toFun p := ⟨p.1.1.length, ((word_lt_iff p.1.1 t.1).mp p.2).2⟩
  invFun n := ⟨⟨t.1.take n, hS t.1 t.2 _ (List.take_prefix _ _)⟩,
    (word_lt_iff _ _).mpr ⟨List.take_prefix _ _, by
      dsimp only [WordNode] at *
      rw [List.length_take, Nat.min_eq_left n.2.le]
      exact n.2⟩⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact (List.prefix_iff_eq_take.mp ((word_lt_iff p.1.1 t.1).mp p.2).1).symm
  right_inv n := by
    apply Fin.ext
    dsimp only [WordNode] at *
    rw [List.length_take, Nat.min_eq_left n.2.le]
  map_rel_iff' := by
    intro p q
    constructor
    · intro h
      change p.1.1.IsPrefix q.1.1
      rw [List.prefix_iff_eq_take.mp ((word_lt_iff p.1.1 t.1).mp p.2).1,
        List.prefix_iff_eq_take.mp ((word_lt_iff q.1.1 t.1).mp q.2).1]
      exact List.take_isPrefix_take.mpr (Or.inl h)
    · exact fun h => h.length_le

def wordTree {X : Type u} (S : Set (WordNode X)) (hS : PrefixClosed S) : Tree.{u} where
  carrier := S
  predecessors_wellOrdered := by
    intro t
    exact (word_predIso S hS t).toOrderEmbedding.isWellOrder

def fullWordTree (X : Type u) : Tree.{u} :=
  wordTree (Set.univ : Set (WordNode X)) (by intro t ht s hs; trivial)

theorem wordTree_nodeHeight {X : Type u} (S : Set (WordNode X)) (hS : PrefixClosed S)
    (t : wordTree S hS) : nodeHeight (wordTree S hS) t = t.1.length := by
  let := (word_predIso S hS t).toOrderEmbedding.isWellOrder
  change typeLT (Set.Iio (show S from t)) = _
  let : Fintype (Set.Iio (show S from t)) :=
    Fintype.ofEquiv (Fin t.1.length) (word_predIso S hS t).symm.toEquiv
  rw [Ordinal.type_fintype, Fintype.card_congr (word_predIso S hS t).toEquiv,
    Fintype.card_fin]

theorem fullWordTree_height (X : Type u) [Nonempty X] :
    treeHeight (fullWordTree X) = Ordinal.omega 0 := by
  rw [Ordinal.omega_zero]
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro t
    have he : nodeHeight (fullWordTree X) t = t.1.length := wordTree_nodeHeight _ _ t
    rw [he]
    have h : (t.1.length : Ordinal) + 1 < Ordinal.omega0 := by
      simpa using Ordinal.natCast_lt_omega0 (t.1.length + 1)
    exact h.le
  · apply Ordinal.omega0_le.mpr
    intro n
    let t : fullWordTree X := ⟨List.replicate n (Classical.choice ‹Nonempty X›), Set.mem_univ _⟩
    have h := Ordinal.le_iSup (fun t : fullWordTree X => nodeHeight (fullWordTree X) t + 1) t
    have he : nodeHeight (fullWordTree X) t = t.1.length := wordTree_nodeHeight _ _ t
    rw [he] at h
    have ht : t.1.length = n := List.length_replicate ..
    rw [ht] at h
    exact (show (n : Ordinal) ≤ (n : Ordinal) + 1 from le_self_add).trans h

def binaryBranches (x : ℕ → Bool) : Set (fullWordTree Bool) :=
  {w | ∃ n, w.1 = AlmostDisjoint.binaryPrefix x n}

theorem word_level_iff {X : Type u} (S : Set (WordNode X)) (hS : PrefixClosed S)
    (t : wordTree S hS) (n : ℕ) : t ∈ level (wordTree S hS) n ↔ t.1.length = n := by
  change nodeHeight (wordTree S hS) t = (n : Ordinal) ↔ _
  rw [wordTree_nodeHeight, Nat.cast_inj]

private def word_levelTuple {X : Type u} (n : ℕ) :
    level (fullWordTree X) n ≃ (Fin n → X) where
  toFun w i := (show List X from w.1.1)[i.1]'(by
    have h := (word_level_iff _ _ w.1 n).mp w.2
    change (i : ℕ) < w.1.1.length
    rw [h]
    exact i.2)
  invFun f := ⟨⟨List.ofFn f, Set.mem_univ _⟩,
    (word_level_iff _ _ _ n).mpr (List.length_ofFn (f := f))⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    have h := (word_level_iff _ _ w.1 n).mp w.2
    dsimp only [WordNode] at *
    apply List.ext_getElem
    · simpa using h.symm
    · intro i hi hj
      simp
  right_inv f := by
    funext i
    simp

theorem binaryTree_levels :
    Countable (fullWordTree Bool) ∧ ∀ n : ℕ,
      (level (fullWordTree Bool) n).Finite ∧ (level (fullWordTree Bool) n).ncard = 2 ^ n := by
  classical
  refine ⟨?_, fun n => ?_⟩
  · change Countable {l : List Bool // l ∈ (Set.univ : Set (List Bool))}
    exact Subtype.val_injective.countable
  let e := word_levelTuple (X := Bool) n
  let := Fintype.ofEquiv (Fin n → Bool) e.symm
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Set.fintypeCard_eq_ncard, Fintype.card_congr e]
  simp

private theorem word_binaryPrefix_prefix (x : ℕ → Bool) {n m : ℕ} (h : n ≤ m) :
    (AlmostDisjoint.binaryPrefix x n).IsPrefix (AlmostDisjoint.binaryPrefix x m) := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp [AlmostDisjoint.binaryPrefix, Nat.min_eq_left h]
  · intro i hi hj
    simp [AlmostDisjoint.binaryPrefix]

theorem word_binaryBranch_cofinal (x : ℕ → Bool) :
    IsCofinalBranch (fullWordTree Bool) (binaryBranches x) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro s ⟨n, hn⟩ t ⟨m, hm⟩ hne
    change s.1.IsPrefix t.1 ∨ t.1.IsPrefix s.1
    rw [hn, hm]
    exact (le_total n m).imp (word_binaryPrefix_prefix x) (word_binaryPrefix_prefix x)
  · rintro t s hst ⟨n, hn⟩
    refine ⟨s.1.length, ?_⟩
    have he := List.prefix_iff_eq_take.mp (show s.1.IsPrefix t.1 from hst)
    have hl : s.1.length ≤ n := by
      have := (show s.1.IsPrefix t.1 from hst).length_le
      simpa [hn, AlmostDisjoint.binaryPrefix] using this
    refine he.trans ?_
    rw [hn]
    simpa [AlmostDisjoint.binaryPrefix] using
      (List.prefix_iff_eq_take.mp (word_binaryPrefix_prefix x hl)).symm
  · intro a ha
    rw [fullWordTree_height, Ordinal.omega_zero] at ha
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp ha
    refine ⟨⟨AlmostDisjoint.binaryPrefix x n, Set.mem_univ _⟩, ⟨n, rfl⟩, ?_⟩
    exact (word_level_iff _ _ _ n).mpr (List.length_ofFn (f := fun i : Fin n => x i))

private theorem word_binaryBranches_injective : Function.Injective binaryBranches := by
  intro x y he
  funext i
  let w : fullWordTree Bool := ⟨AlmostDisjoint.binaryPrefix x (i + 1), Set.mem_univ _⟩
  have hw : w ∈ binaryBranches y := he ▸ (show w ∈ binaryBranches x from ⟨i + 1, rfl⟩)
  obtain ⟨m, hm⟩ := hw
  have hl : m = i + 1 := by
    have hh := congrArg List.length hm
    simpa [w, AlmostDisjoint.binaryPrefix] using hh.symm
  subst m
  have hh : (fun j : Fin (i + 1) => x j) = (fun j : Fin (i + 1) => y j) :=
    List.ofFn_inj.mp hm
  exact congrFun hh ⟨i, Nat.lt_succ_self i⟩

theorem binaryBranches_spec :
    (∀ x, IsCofinalBranch (fullWordTree Bool) (binaryBranches x)) ∧
      ∀ B, IsCofinalBranch (fullWordTree Bool) B → ∃! x, binaryBranches x = B := by
  classical
  refine ⟨word_binaryBranch_cofinal, ?_⟩
  intro B hB
  have hex (n : ℕ) : ∃ w : fullWordTree Bool, w ∈ B ∧ w ∈ level (fullWordTree Bool) n :=
    hB.2 n (by rw [fullWordTree_height, Ordinal.omega_zero]; exact Ordinal.natCast_lt_omega0 n)
  choose w hwB hwL using hex
  have hlen (n : ℕ) : (w n).1.length = n := (word_level_iff _ _ (w n) n).mp (hwL n)
  have hpref {n m : ℕ} (hnm : n ≤ m) : (w n).1.IsPrefix (w m).1 := by
    rcases hB.1.1.total (hwB n) (hwB m) with h | h
    · exact h
    · have hmn : m ≤ n := by simpa [hlen] using h.length_le
      have he : n = m := hnm.antisymm hmn
      subst m
      exact List.prefix_rfl
  let x : ℕ → Bool := fun i => (show List Bool from (w (i + 1)).1)[i]'(by
    have hh := hlen (i + 1)
    change i < (w (i + 1)).1.length
    rw [hh]
    exact Nat.lt_succ_self i)
  have hew (n : ℕ) : (w n).1 = AlmostDisjoint.binaryPrefix x n := by
    dsimp only [WordNode] at *
    apply List.ext_getElem
    · simp [hlen, AlmostDisjoint.binaryPrefix]
    · intro i hi hj
      have hp := hpref (show i + 1 ≤ n by rw [hlen n] at hi; omega)
      have hh := hp.getElem (i := i) (by rw [hlen]; omega)
      simpa [AlmostDisjoint.binaryPrefix, x] using hh.symm
  have he : binaryBranches x = B := by
    ext t
    constructor
    · rintro ⟨n, hn⟩
      have ht : t = w n := Subtype.ext (hn.trans (hew n).symm)
      exact ht ▸ hwB n
    · intro ht
      refine ⟨t.1.length, ?_⟩
      have heq : t.1 = (w t.1.length).1 := by
        rcases hB.1.1.total ht (hwB t.1.length) with h | h
        · exact h.eq_of_length (hlen _).symm
        · exact (h.eq_of_length (hlen _)).symm
      exact heq.trans (hew _)
  exact ⟨x, he, fun y hy => word_binaryBranches_injective (hy.trans he.symm)⟩

theorem binaryTree_branch_cardinality :
    Cardinal.mk {B : Set (fullWordTree Bool) | IsCofinalBranch (fullWordTree Bool) B} =
      Cardinal.continuum := by
  let e : (ℕ → Bool) ≃ {B : Set (fullWordTree Bool) | IsCofinalBranch (fullWordTree Bool) B} :=
    Equiv.ofBijective (fun x => ⟨binaryBranches x, binaryBranches_spec.1 x⟩) ⟨
      fun x y h => word_binaryBranches_injective (congrArg Subtype.val h), by
        intro B
        obtain ⟨x, hx, _⟩ := binaryBranches_spec.2 B.1 B.2
        exact ⟨x, Subtype.ext hx⟩⟩
  rw [← Cardinal.mk_congr e, Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat,
    Cardinal.lift_id, Cardinal.lift_aleph0, Cardinal.two_power_aleph0]

def CoinfiniteRange {A : Type u} (f : A → ℕ) : Prop := (Set.range f)ᶜ.Infinite

theorem finite_modification_class_countable {A : Type u} [Countable A] (f : A → ℕ) :
    {g : A → ℕ | g =ᶠ[Filter.cofinite] f}.Countable := by
  classical
  let C := {g : A → ℕ | g =ᶠ[Filter.cofinite] f}
  let code : C → A →₀ ℕ := fun g => Finsupp.ofSupportFinite
    (fun a => if g.val a = f a then 0 else g.val a + 1) (by
      apply (Filter.eventually_cofinite.mp g.prop).subset
      intro a ha
      change (if g.val a = f a then 0 else g.val a + 1) ≠ 0 at ha
      by_contra h
      have he : g.val a = f a := by simpa using h
      exact ha (by simp [he]))
  have hi : Function.Injective code := by
    intro g h he
    apply Subtype.ext
    funext a
    have he' := congrArg (fun q : A →₀ ℕ => q a) he
    change (if g.val a = f a then 0 else g.val a + 1) =
      (if h.val a = f a then 0 else h.val a + 1) at he'
    split_ifs at he' with hg hh <;> omega
  exact Set.countable_coe_iff.mp hi.countable

theorem finite_modification_ranges {A : Type u} {f g : A → ℕ}
    (h : f =ᶠ[Filter.cofinite] g) :
    ((Set.range f \ Set.range g) ∪ (Set.range g \ Set.range f)).Finite ∧
      (CoinfiniteRange f ↔ CoinfiniteRange g) := by
  have hE : {a | f a ≠ g a}.Finite := Filter.eventually_cofinite.mp h
  have hfg : (range f \ range g).Finite := (hE.image f).subset (by
    rintro n ⟨⟨a, rfl⟩, ha⟩
    exact ⟨a, fun he => ha ⟨a, he.symm⟩, rfl⟩)
  have hgf : (range g \ range f).Finite := (hE.image g).subset (by
    rintro n ⟨⟨a, rfl⟩, ha⟩
    exact ⟨a, fun he => ha ⟨a, he⟩, rfl⟩)
  refine ⟨hfg.union hgf, ?_⟩
  constructor
  · intro hf
    exact (hf.sdiff hgf).mono (by
      intro n hn hg
      exact hn.2 ⟨hg, hn.1⟩)
  · intro hg
    exact (hg.sdiff hfg).mono (by
      intro n hn hf
      exact hn.2 ⟨hf, hn.1⟩)

private theorem fm_fill_finite {B : Type v} (p : B → ℕ) (N : Set B) (hN : N.Finite)
    (hinj : Set.InjOn p Nᶜ) (hpc : CoinfiniteRange p) (R : Set ℕ) (hR : R.Finite)
    (havoid : ∀ b, b ∉ N → p b ∉ R) :
    ∃ h : B → ℕ, Function.Injective h ∧ (∀ b, b ∉ N → h b = p b) ∧
      h =ᶠ[Filter.cofinite] p ∧ CoinfiniteRange h ∧ Disjoint (Set.range h) R := by
  classical
  let Q : Set ℕ := (range p)ᶜ \ R
  have hQ : Q.Infinite := hpc.sdiff hR
  have : Infinite Q := hQ.to_subtype
  have : Finite N := hN.to_subtype
  obtain ⟨c, hc⟩ := _root_.Countable.exists_injective_nat N
  let q : ℕ ↪ Q := Infinite.natEmbedding Q
  let fresh : N → ℕ := fun b => (q (c b)).val
  have hfresh : Function.Injective fresh :=
    Subtype.val_injective.comp (q.injective.comp hc)
  have hpFresh (b : N) : fresh b ∉ range p := (q (c b)).prop.1
  have hRFresh (b : N) : fresh b ∉ R := (q (c b)).prop.2
  let h : B → ℕ := fun b => if hb : b ∈ N then fresh ⟨b, hb⟩ else p b
  have hout (b : B) (hb : b ∉ N) : h b = p b := by simp [h, hb]
  have heq : h =ᶠ[Filter.cofinite] p := by
    apply Filter.eventually_cofinite.mpr
    apply hN.subset
    intro b hb
    by_contra hn
    exact hb (hout b hn)
  refine ⟨h, ?_, hout, heq, (finite_modification_ranges heq).2.mpr hpc, ?_⟩
  · intro b d he
    by_cases hb : b ∈ N <;> by_cases hd : d ∈ N
    · have he' : fresh ⟨b, hb⟩ = fresh ⟨d, hd⟩ := by simpa [h, hb, hd] using he
      exact congrArg Subtype.val (hfresh he')
    · have he' : fresh ⟨b, hb⟩ = p d := by simpa [h, hb, hd] using he
      exact (hpFresh ⟨b, hb⟩ ⟨d, he'.symm⟩).elim
    · have he' : p b = fresh ⟨d, hd⟩ := by simpa [h, hb, hd] using he
      exact (hpFresh ⟨d, hd⟩ ⟨b, he'⟩).elim
    · exact hinj hb hd (by simpa [h, hb, hd] using he)
  · apply Set.disjoint_left.mpr
    rintro n ⟨b, rfl⟩ hn
    by_cases hb : b ∈ N
    · exact hRFresh ⟨b, hb⟩ (by simpa [h, hb] using hn)
    · exact havoid b hb (by simpa [h, hb] using hn)

/-- Generalization from a subset inclusion to any specified inclusion embedding. -/
theorem finite_repair {A : Type u} {B : Type v} (ι : A ↪ B) (f : B → ℕ) (g : A → ℕ)
    (hf : Function.Injective f) (hfc : CoinfiniteRange f) (hg : Function.Injective g)
    (heq : g =ᶠ[Filter.cofinite] f ∘ ι) (R : Set ℕ) (hR : R.Finite)
    (hdisj : Disjoint (Set.range g) R) :
    ∃ h : B → ℕ, Function.Injective h ∧ h ∘ ι = g ∧
      h =ᶠ[Filter.cofinite] f ∧ CoinfiniteRange h ∧ Disjoint (Set.range h) R := by
  classical
  let D : Set A := {a | g a ≠ f (ι a)}
  have hD : D.Finite := Filter.eventually_cofinite.mp heq
  let p : B → ℕ := fun b => if hb : b ∈ range ι then g (Classical.choose hb) else f b
  have hpOld (a : A) : p (ι a) = g a := by
    have hb : ι a ∈ range ι := mem_range_self a
    have he : Classical.choose hb = a := ι.injective (Classical.choose_spec hb)
    dsimp only [p]
    rw [dite_eq_left hb, he]
  have hpNew (b : B) (hb : b ∉ range ι) : p b = f b := by
    dsimp only [p]
    exact dite_eq_right hb
  have hpEq : p =ᶠ[Filter.cofinite] f := by
    apply Filter.eventually_cofinite.mpr
    apply (hD.image ι).subset
    intro b hb
    by_cases hi : b ∈ range ι
    · obtain ⟨a, rfl⟩ := hi
      exact ⟨a, by simpa [D, hpOld] using hb, rfl⟩
    · exact (hb (hpNew b hi)).elim
  let N : Set B := {b | b ∉ range ι ∧ f b ∈ g '' D ∪ R}
  have hN : N.Finite := ((hD.image g).union hR).preimage hf.injOn |>.subset (by
    intro b hb; exact hb.2)
  have hcross (a : A) (b : B) (hb : b ∉ range ι) (hbN : b ∉ N) : g a ≠ f b := by
    intro he
    by_cases ha : a ∈ D
    · exact hbN ⟨hb, Or.inl ⟨a, ha, he⟩⟩
    · have hga : g a = f (ι a) := by simpa [D] using ha
      exact hb ⟨a, hf (hga.symm.trans he)⟩
  have hpInj : Set.InjOn p Nᶜ := by
    intro b hb c hc he
    by_cases hbOld : b ∈ range ι <;> by_cases hcOld : c ∈ range ι
    · obtain ⟨a, rfl⟩ := hbOld
      obtain ⟨d, rfl⟩ := hcOld
      exact congrArg ι (hg (by simpa [hpOld] using he))
    · obtain ⟨a, rfl⟩ := hbOld
      exact (hcross a c hcOld hc (by simpa [hpOld, hpNew c hcOld] using he)).elim
    · obtain ⟨a, rfl⟩ := hcOld
      exact (hcross a b hbOld hb (by simpa [hpOld, hpNew b hbOld] using he.symm)).elim
    · exact hf (by simpa [hpNew b hbOld, hpNew c hcOld] using he)
  have hpAvoid (b : B) (hb : b ∉ N) : p b ∉ R := by
    by_cases hi : b ∈ range ι
    · obtain ⟨a, rfl⟩ := hi
      rw [hpOld]
      exact Set.disjoint_left.mp hdisj (mem_range_self a)
    · rw [hpNew b hi]
      exact fun hn => hb ⟨hi, Or.inr hn⟩
  have hpCoinfinite : CoinfiniteRange p := (finite_modification_ranges hpEq).2.mpr hfc
  obtain ⟨h, hinj, hout, hEq, hcoinfinite, hAvoid⟩ :=
    fm_fill_finite p N hN hpInj hpCoinfinite R hR hpAvoid
  refine ⟨h, hinj, ?_, hEq.trans hpEq, hcoinfinite, hAvoid⟩
  funext a
  exact (hout (ι a) (fun hn => hn.1 (mem_range_self a))).trans (hpOld a)

abbrev OmegaOne := (Ordinal.omega 1).ToType

def IsCoherentFamily (s : (a : OmegaOne) → Set.Iio a → ℕ) : Prop :=
  (∀ a, Function.Injective (s a) ∧ CoinfiniteRange (s a)) ∧
    ∀ a b (h : b < a), s a ∘ initialSegmentEmbedding h.le =ᶠ[Filter.cofinite] s b

private theorem tree_initial_countable (a : OmegaOne) : Countable (Set.Iio a) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  have hc : Cardinal.mk (Set.Iio a) = a.toOrd.1.card := by
    rw [← tree_position_type a, Ordinal.card_type]
  rw [hc, Cardinal.card_le_iff, Cardinal.succ_aleph0, Cardinal.ord_aleph]
  exact a.toOrd.2

private structure tree_DiagonalState {a : OmegaOne} (β : ℕ → Set.Iio a)
    (s : (b : Set.Iio a) → Set.Iio b.1 → ℕ) (n : ℕ) where
  fn : Set.Iio (β n).1 → ℕ
  reserve : Finset ℕ
  injective : Function.Injective fn
  almostEq : fn =ᶠ[cofinite] s (β n)
  coinfinite : CoinfiniteRange fn
  disjoint : Disjoint (range fn) (reserve : Set ℕ)
  card : reserve.card = n

/-- Extension from an entire compatible history, the recursion's central step. -/
theorem coherent_history_extension (a : OmegaOne)
    (s : (b : Set.Iio a) → Set.Iio b.1 → ℕ)
    (hinj : ∀ b, Function.Injective (s b) ∧ CoinfiniteRange (s b))
    (hcoh : ∀ b c (h : c.1 < b.1),
      s b ∘ initialSegmentEmbedding h.le =ᶠ[Filter.cofinite] s c) :
    ∃ f : Set.Iio a → ℕ, Function.Injective f ∧ CoinfiniteRange f ∧
      ∀ b : Set.Iio a, f ∘ initialSegmentEmbedding b.2.le =ᶠ[Filter.cofinite] s b := by
  classical
  have hweak (b c : Set.Iio a) (hcb : c.1 ≤ b.1) :
      s b ∘ initialSegmentEmbedding hcb =ᶠ[cofinite] s c := by
    rcases hcb.eq_or_lt with he | hc
    · have he' : c = b := Subtype.ext he
      subst c
      exact Filter.EventuallyEq.rfl
    · exact hcoh b c hc
  by_cases he : IsEmpty (Set.Iio a)
  · letI := he
    refine ⟨fun _ => 0, Function.injective_of_subsingleton _, ?_, ?_⟩
    · have hr : range (fun _ : Set.Iio a => (0 : ℕ)) = ∅ := by
        ext v
        constructor
        · rintro ⟨x, _⟩
          exact isEmptyElim x
        · intro h
          exact h.elim
      rw [CoinfiniteRange, hr, compl_empty]
      exact infinite_univ
    · exact fun b => isEmptyElim b
  haveI : Nonempty (Set.Iio a) := not_isEmpty_iff.mp he
  by_cases hm : ∃ b : Set.Iio a, ∀ c : Set.Iio a, c ≤ b
  · obtain ⟨b, hb⟩ := hm
    obtain ⟨k, hk⟩ := (hinj b).2.nonempty
    let f : Set.Iio a → ℕ := fun x => if h : x.1 < b.1 then s b ⟨x.1, h⟩ else k
    have hxeq (x : Set.Iio a) (hx : ¬ x.1 < b.1) : x = b :=
      le_antisymm (hb x) (not_lt.mp hx)
    have hf : Function.Injective f := by
      intro x y hxy
      by_cases hx : x.1 < b.1 <;> by_cases hy : y.1 < b.1
      · have h : (⟨x.1, hx⟩ : Set.Iio b.1) = ⟨y.1, hy⟩ :=
          (hinj b).1 (by simpa only [f, dif_pos hx, dif_pos hy] using hxy)
        apply Subtype.ext
        exact congrArg (fun i : Set.Iio b.1 => i.1) h
      · have h : s b ⟨x.1, hx⟩ = k := by simpa only [f, dif_pos hx, dif_neg hy] using hxy
        exact (hk ⟨⟨x.1, hx⟩, h⟩).elim
      · have h : s b ⟨y.1, hy⟩ = k := by
          simpa only [f, dif_pos hy, dif_neg hx] using hxy.symm
        exact (hk ⟨⟨y.1, hy⟩, h⟩).elim
      · exact (hxeq x hx).trans (hxeq y hy).symm
    refine ⟨f, hf, ?_, ?_⟩
    · apply ((hinj b).2.sdiff (Set.finite_singleton k)).mono
      intro v hv
      rintro ⟨x, rfl⟩
      by_cases hx : x.1 < b.1
      · apply hv.1
        exact ⟨⟨x.1, hx⟩, by simp only [f, dif_pos hx]⟩
      · exact hv.2 (by simp only [f, dif_neg hx, mem_singleton_iff])
    · intro c
      have hcb : c.1 ≤ b.1 := hb c
      have hr : f ∘ initialSegmentEmbedding c.2.le =
          s b ∘ initialSegmentEmbedding hcb := by
        funext x
        change (if h : x.1 < b.1 then s b ⟨x.1, h⟩ else k) =
          s b (initialSegmentEmbedding hcb x)
        rw [dif_pos (lt_of_lt_of_le x.2 hcb)]
        rfl
      rw [hr]
      exact hweak b c hcb
  haveI : Countable (Set.Iio a) := tree_initial_countable a
  haveI : NoMaxOrder (Set.Iio a) := by
    constructor
    intro b
    have h : ∃ c : Set.Iio a, ¬ c ≤ b := by
      by_contra hn
      push_neg at hn
      exact hm ⟨b, hn⟩
    obtain ⟨c, hc⟩ := h
    exact ⟨c, lt_of_not_ge hc⟩
  obtain ⟨β, hβ, hβtop⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop (Set.Iio a)
  have hcover (x : Set.Iio a) : ∃ n, x.1 < (β n).1 := by
    obtain ⟨y, hy⟩ := exists_gt x
    obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.mp hβtop y).exists
    exact ⟨n, hy.trans_le hn⟩
  let z0 : tree_DiagonalState β s 0 :=
    { fn := s (β 0)
      reserve := ∅
      injective := (hinj _).1
      almostEq := Filter.EventuallyEq.rfl
      coinfinite := (hinj _).2
      disjoint := by simp
      card := by simp }
  have step (n : ℕ) (z : tree_DiagonalState β s n) :
      ∃ w : tree_DiagonalState β s (n + 1),
        w.fn ∘ initialSegmentEmbedding (hβ (Nat.le_succ n)) = z.fn ∧
          z.reserve ⊆ w.reserve := by
    have heq : z.fn =ᶠ[cofinite]
        s (β (n + 1)) ∘ initialSegmentEmbedding (hβ (Nat.le_succ n)) :=
      z.almostEq.trans (hweak (β (n + 1)) (β n) (hβ (Nat.le_succ n))).symm
    obtain ⟨h, hi, hext, heq', hc, hd⟩ := finite_repair
      (initialSegmentEmbedding (hβ (Nat.le_succ n))) (s (β (n + 1))) z.fn
      (hinj _).1 (hinj _).2 z.injective heq z.reserve z.reserve.finite_toSet z.disjoint
    obtain ⟨k, hk, hkR⟩ := hc.exists_notMem_finset z.reserve
    let w : tree_DiagonalState β s (n + 1) :=
      { fn := h
        reserve := insert k z.reserve
        injective := hi
        almostEq := heq'
        coinfinite := hc
        disjoint := by
          apply Set.disjoint_left.mpr
          intro v hv hvr
          rcases Finset.mem_insert.mp hvr with he | hvR
          · exact hk (he ▸ hv)
          · exact Set.disjoint_left.mp hd hv hvR
        card := by simp [hkR, z.card] }
    exact ⟨w, hext, Finset.subset_insert _ _⟩
  let z : (n : ℕ) → tree_DiagonalState β s n :=
    Nat.rec z0 (fun n w => (step n w).choose)
  have hz (n : ℕ) :
      (z (n + 1)).fn ∘ initialSegmentEmbedding (hβ (Nat.le_succ n)) = (z n).fn ∧
        (z n).reserve ⊆ (z (n + 1)).reserve := (step n (z n)).choose_spec
  have hext {n m : ℕ} (hnm : n ≤ m) :
      (z m).fn ∘ initialSegmentEmbedding (hβ hnm) = (z n).fn := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih =>
      funext x
      exact (congrFun (hz m).1 (initialSegmentEmbedding (hβ hnm) x)).trans
        (congrFun ih x)
  have hreserve {n m : ℕ} (hnm : n ≤ m) : (z n).reserve ⊆ (z m).reserve := by
    induction m, hnm using Nat.le_induction with
    | base => exact Subset.rfl
    | succ m hnm ih => exact ih.trans (hz m).2
  let N (x : Set.Iio a) := Nat.find (hcover x)
  have hN (x : Set.Iio a) : x.1 < (β (N x)).1 := Nat.find_spec (hcover x)
  let f : Set.Iio a → ℕ := fun x => (z (N x)).fn ⟨x.1, hN x⟩
  have hf_at (n : ℕ) (x : Set.Iio (β n).1) :
      f (initialSegmentEmbedding (β n).2.le x) = (z n).fn x := by
    let y : Set.Iio a := initialSegmentEmbedding (β n).2.le x
    rcases le_total (N y) n with h | h
    · exact (congrFun (hext h) ⟨y.1, hN y⟩).symm
    · exact congrFun (hext h) x
  have hf : Function.Injective f := by
    intro x y hxy
    let m := max (N x) (N y)
    have hx : x.1 < (β m).1 := (hN x).trans_le (hβ (le_max_left _ _))
    have hy : y.1 < (β m).1 := (hN y).trans_le (hβ (le_max_right _ _))
    have he : (⟨x.1, hx⟩ : Set.Iio (β m).1) = ⟨y.1, hy⟩ := (z m).injective (by
      rw [← hf_at m ⟨x.1, hx⟩, ← hf_at m ⟨y.1, hy⟩]
      exact hxy)
    apply Subtype.ext
    exact congrArg (fun i : Set.Iio (β m).1 => i.1) he
  let R : Set ℕ := ⋃ n, ((z n).reserve : Set ℕ)
  have hR : R.Infinite := by
    intro hfinite
    let n := hfinite.toFinset.card + 1
    have hsub : (z n).reserve ⊆ hfinite.toFinset := by
      intro v hv
      apply hfinite.mem_toFinset.mpr
      exact Set.mem_iUnion.mpr ⟨n, hv⟩
    have hh := Finset.card_le_card hsub
    rw [(z n).card] at hh
    dsimp [n] at hh
    omega
  have hc : CoinfiniteRange f := by
    apply hR.mono
    intro v hv
    obtain ⟨n, hv⟩ := Set.mem_iUnion.mp hv
    rintro ⟨x, hfx⟩
    let m := max n (N x)
    have hx : x.1 < (β m).1 := (hN x).trans_le (hβ (le_max_right _ _))
    have hv' : v ∈ (z m).reserve := hreserve (le_max_left _ _) hv
    apply Set.disjoint_left.mp (z m).disjoint _ hv'
    exact ⟨⟨x.1, hx⟩, (hf_at m ⟨x.1, hx⟩).symm.trans hfx⟩
  refine ⟨f, hf, hc, ?_⟩
  intro b
  obtain ⟨n, hbn⟩ := hcover b
  have hr : f ∘ initialSegmentEmbedding b.2.le =
      (z n).fn ∘ initialSegmentEmbedding hbn.le := by
    funext x
    exact hf_at n (initialSegmentEmbedding hbn.le x)
  rw [hr]
  exact ((z n).almostEq.comp_tendsto (initialSegmentEmbedding hbn.le).injective.tendsto_cofinite)
    |>.trans (hcoh (β n) b hbn)

theorem coherent_family_exists :
    ∃ s : (a : OmegaOne) → Set.Iio a → ℕ, IsCoherentFamily s := by
  classical
  let Valid (a : OmegaOne) (r : (b : Set.Iio a) → Set.Iio b.1 → ℕ) : Prop :=
    (∀ b, Function.Injective (r b) ∧ CoinfiniteRange (r b)) ∧
      ∀ b c (h : c.1 < b.1),
        r b ∘ initialSegmentEmbedding h.le =ᶠ[cofinite] r c
  let H (a : OmegaOne) (r : (b : OmegaOne) → b < a → Set.Iio b → ℕ) :
      Set.Iio a → ℕ :=
    if h : Valid a (fun b => r b.1 b.2) then
      (coherent_history_extension a (fun b => r b.1 b.2) h.1 h.2).choose
    else fun _ => 0
  let s : (a : OmegaOne) → Set.Iio a → ℕ := (wellFounded_lt (α := OmegaOne)).fix H
  have hs (a : OmegaOne) :
      (Function.Injective (s a) ∧ CoinfiniteRange (s a)) ∧
        ∀ b (h : b < a), s a ∘ initialSegmentEmbedding h.le =ᶠ[cofinite] s b := by
    induction a using (wellFounded_lt (α := OmegaOne)).induction with
    | h a ih =>
      have hv : Valid a (fun b => s b.1) := by
        refine ⟨fun b => (ih b.1 b.2).1, ?_⟩
        intro b c hcb
        exact (ih b.1 b.2).2 c.1 hcb
      have he : s a = H a (fun b _ => s b) := (wellFounded_lt (α := OmegaOne)).fix_eq H a
      rw [he]
      dsimp only [H]
      rw [dif_pos hv]
      have hp := (coherent_history_extension a (fun b => s b.1) hv.1 hv.2).choose_spec
      exact ⟨⟨hp.1, hp.2.1⟩, fun b hb => hp.2.2 ⟨b, hb⟩⟩
  exact ⟨s, ⟨fun a => (hs a).1, fun a b h => (hs a).2 b h⟩⟩

def injectionNodes : Set (FunctionNode (Ordinal.omega 1) ℕ) :=
  {t | Function.Injective t.2}

theorem injectionNodes_restrictionClosed : RestrictionClosed injectionNodes := by
  intro t ht b hb
  exact ht.comp (initialSegmentEmbedding hb).injective

def injectionTree : Tree := functionTree injectionNodes injectionNodes_restrictionClosed

def binaryInjection (x : ℕ → Bool) (n : ℕ) : ℕ := 2 * n + if x n then 1 else 0

theorem binaryInjection_spec :
    (∀ x : ℕ → Bool, Function.Injective (binaryInjection x)) ∧
      Function.Injective binaryInjection := by
  constructor
  · intro x n m h
    dsimp [binaryInjection] at h
    split_ifs at h <;> omega
  · intro x y h
    funext n
    have hn := congrFun h n
    dsimp [binaryInjection] at hn
    cases hx : x n <;> cases hy : y n <;> simp [hx, hy] at hn ⊢

private theorem injection_domain_countable (a : OmegaOne) : Countable (Set.Iio a) := by
  let : Countable (Set.Iio a.toOrd.1) :=
    Cardinal.countable_Iio_of_lt_omega_one a.toOrd.2
  exact (tree_positionIso a).injective.countable

private theorem injection_branch_countable
    (S : Set (FunctionNode (Ordinal.omega 1) ℕ)) (hS : RestrictionClosed S)
    (hinj : ∀ t ∈ S, Function.Injective t.2)
    {B : Set (functionTree S hS)} (hB : IsBranch (functionTree S hS) B) : B.Countable := by
  classical
  let idx (t : functionTree S hS) : OmegaOne := t.1.1
  let U : Set OmegaOne := {a | ∃ t ∈ B, a < idx t}
  have hcomp (t : functionTree S hS) (ht : t ∈ B)
      (r : functionTree S hS) (hr : r ∈ B) (a : OmegaOne)
      (hat : a < idx t) (har : a < idx r) :
      t.1.2 ⟨a, hat⟩ = r.1.2 ⟨a, har⟩ := by
    rcases hB.1.total ht hr with htr | hrt
    · obtain ⟨_, he⟩ := htr
      exact congrFun he ⟨a, hat⟩
    · obtain ⟨_, he⟩ := hrt
      exact (congrFun he ⟨a, har⟩).symm
  let witness (a : U) : functionTree S hS := Classical.choose a.2
  have hw (a : U) : witness a ∈ B ∧ a.1 < idx (witness a) := Classical.choose_spec a.2
  let val (a : U) : ℕ := (witness a).1.2 ⟨a.1, (hw a).2⟩
  have hv (a : U) (t : functionTree S hS) (ht : t ∈ B) (ha : a.1 < idx t) :
      val a = t.1.2 ⟨a.1, ha⟩ := hcomp _ (hw a).1 _ ht _ (hw a).2 ha
  have hval : Function.Injective val := by
    intro a b hab
    rcases hB.1.total (hw a).1 (hw b).1 with h | h
    · have ha : a.1 < idx (witness b) := lt_of_lt_of_le (hw a).2 h.1
      have he := (hv a _ (hw b).1 ha).symm.trans (hab.trans (hv b _ (hw b).1 (hw b).2))
      exact Subtype.ext (congrArg (fun x : Set.Iio (idx (witness b)) => x.1) (hinj _ (witness b).2 he))
    · have hb : b.1 < idx (witness a) := lt_of_lt_of_le (hw b).2 h.1
      have he := (hv a _ (hw a).1 (hw a).2).symm.trans (hab.trans (hv b _ (hw a).1 hb))
      exact Subtype.ext (congrArg (fun x : Set.Iio (idx (witness a)) => x.1) (hinj _ (witness a).2 he))
  have hU : U.Countable := hval.countable
  let D : Set OmegaOne := idx '' B
  have hlast : (D \ U).Subsingleton := by
    rintro a ⟨⟨t, ht, rfl⟩, ha⟩ b ⟨⟨r, hr, rfl⟩, hb⟩
    rcases lt_trichotomy (idx t) (idx r) with h | h | h
    · exact False.elim (ha ⟨r, hr, h⟩)
    · exact h
    · exact False.elim (hb ⟨t, ht, h⟩)
  have hD : D.Countable := (hU.union hlast.countable).mono (by
    intro a ha
    by_cases hu : a ∈ U
    · exact Or.inl hu
    · exact Or.inr ⟨ha, hu⟩)
  apply Set.countable_of_injective_of_countable_image _ hD
  intro t ht r hr he
  have he' : nodeHeight (functionTree S hS) t = nodeHeight (functionTree S hS) r := by
    rw [functionTree_nodeHeight, functionTree_nodeHeight]
    exact congrArg (fun a : OmegaOne => a.toOrd.1) he
  exact congrArg Subtype.val (branch_height_injective _ hB (a₁ := ⟨t, ht⟩) (a₂ := ⟨r, hr⟩) he')

private theorem injection_height (S : Set (FunctionNode (Ordinal.omega 1) ℕ))
    (hS : RestrictionClosed S) (hex : ∀ a : OmegaOne, ∃ f, (⟨a, f⟩ : FunctionNode _ ℕ) ∈ S) :
    treeHeight (functionTree S hS) = Ordinal.omega 1 := by
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro t
    rw [functionTree_nodeHeight]
    exact Order.add_one_le_of_lt t.1.1.toOrd.2
  · apply le_of_forall_lt
    intro a ha
    let b : OmegaOne := Ordinal.ToType.mk ⟨a, ha⟩
    obtain ⟨f, hf⟩ := hex b
    let t : functionTree S hS := ⟨⟨b, f⟩, hf⟩
    have he : nodeHeight (functionTree S hS) t = a := by
      simpa [t, b] using functionTree_nodeHeight S hS t
    have h := Ordinal.le_iSup (fun t : functionTree S hS => nodeHeight _ t + 1) t
    rw [he] at h
    exact (lt_add_one a).trans_le h

private theorem injection_no_cofinal
    (S : Set (FunctionNode (Ordinal.omega 1) ℕ)) (hS : RestrictionClosed S)
    (hinj : ∀ t ∈ S, Function.Injective t.2)
    (hheight : treeHeight (functionTree S hS) = Ordinal.omega 1) :
    ¬ ∃ B, IsCofinalBranch (functionTree S hS) B := by
  rintro ⟨B, hB⟩
  let : Countable B := injection_branch_countable S hS hinj hB.1
  let f (t : B) : OmegaOne := t.1.1.1
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨t, ⟨ht, he⟩⟩ := hB.2 a.toOrd.1 (by rw [hheight]; exact a.toOrd.2)
    refine ⟨⟨t, ht⟩, ?_⟩
    apply (Ordinal.ToType.mk (o := Ordinal.omega 1)).symm.injective
    apply Subtype.ext
    exact (functionTree_nodeHeight S hS t).symm.trans he
  have : Countable OmegaOne := hf.countable
  have hc : #OmegaOne ≤ ℵ₀ := Cardinal.mk_le_aleph0
  simpa [OmegaOne, Cardinal.mk_toType] using hc

theorem injectionTree_spec :
    treeHeight injectionTree = Ordinal.omega 1 ∧
      (¬ ∃ B, IsCofinalBranch injectionTree B) ∧
      ¬ (level injectionTree (Ordinal.omega 0)).Countable ∧
      ¬ IsKappaTree injectionTree ℵ₁ := by
  classical
  have hheight : treeHeight injectionTree = Ordinal.omega 1 := by
    apply injection_height
    intro a
    let : Countable (Set.Iio a) := injection_domain_countable a
    obtain ⟨f, hf⟩ := exists_injective_nat (Set.Iio a)
    exact ⟨f, hf⟩
  have hnobranch := injection_no_cofinal injectionNodes injectionNodes_restrictionClosed
    (fun _ h => h) hheight
  let b : OmegaOne := Ordinal.ToType.mk ⟨Ordinal.omega 0, by simpa using Ordinal.omega0_lt_omega_one⟩
  have hcard : #(Set.Iio b) = #ℕ := by
    rw [← Ordinal.card_type ((· < ·) : Set.Iio b → Set.Iio b → Prop)]
    change (typeLT (Set.Iio b)).card = #ℕ
    rw [tree_position_type]
    simp [b]
  obtain ⟨e⟩ := Cardinal.eq.mp hcard
  let j (x : ℕ → Bool) : injectionTree :=
    ⟨⟨b, binaryInjection x ∘ e⟩, (binaryInjection_spec.1 x).comp e.injective⟩
  have hjheight (x : ℕ → Bool) : nodeHeight injectionTree (j x) = Ordinal.omega 0 := by
    change nodeHeight (functionTree injectionNodes injectionNodes_restrictionClosed) (j x) = Ordinal.omega 0
    simpa [j, b] using functionTree_nodeHeight injectionNodes injectionNodes_restrictionClosed (j x)
  let J (x : ℕ → Bool) : level injectionTree (Ordinal.omega 0) := ⟨j x, hjheight x⟩
  have hJ : Function.Injective J := by
    intro x y h
    apply binaryInjection_spec.2
    have he : (⟨b, binaryInjection x ∘ e⟩ : FunctionNode _ ℕ) = ⟨b, binaryInjection y ∘ e⟩ :=
      congrArg (fun t : level injectionTree (Ordinal.omega 0) => t.1.1) h
    have hf : binaryInjection x ∘ e = binaryInjection y ∘ e := eq_of_heq (Sigma.mk.inj he).2
    funext n
    obtain ⟨a, rfl⟩ := e.surjective n
    exact congrFun hf a
  have hunc : ¬ (level injectionTree (Ordinal.omega 0)).Countable := by
    intro hc
    let : Countable (level injectionTree (Ordinal.omega 0)) := hc.to_subtype
    have : Countable (ℕ → Bool) := hJ.countable
    have hle : #(ℕ → Bool) ≤ ℵ₀ := Cardinal.mk_le_aleph0
    have hcont : #(ℕ → Bool) = Cardinal.continuum := by
      rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat]
      simpa only [Cardinal.lift_id] using Cardinal.two_power_aleph0
    exact Cardinal.aleph0_lt_continuum.not_ge (hcont ▸ hle)
  refine ⟨hheight, hnobranch, hunc, ?_⟩
  intro hκ
  have hc := hκ.2.2 (Ordinal.omega 0) (by simpa using Ordinal.omega0_lt_omega_one)
  exact hunc (Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.lt_aleph_one_iff.mp hc))

def aronszajnNodes (s : (a : OmegaOne) → Set.Iio a → ℕ) :
    Set (FunctionNode (Ordinal.omega 1) ℕ) :=
  {t | Function.Injective t.2 ∧ t.2 =ᶠ[Filter.cofinite] s t.1}

theorem aronszajnNodes_restrictionClosed (s : (a : OmegaOne) → Set.Iio a → ℕ)
    (hs : IsCoherentFamily s) : RestrictionClosed (aronszajnNodes s) := by
  intro t ht b hb
  refine ⟨ht.1.comp (initialSegmentEmbedding hb).injective, ?_⟩
  have he := ht.2.comp_tendsto (initialSegmentEmbedding hb).injective.tendsto_cofinite
  rcases hb.eq_or_lt with h | h
  · subst b
    have hei : t.2 ∘ initialSegmentEmbedding hb = t.2 := by
      funext i
      congr 1
    exact hei ▸ ht.2
  · exact he.trans (hs.2 t.1 b h)

def aronszajnTree (s : (a : OmegaOne) → Set.Iio a → ℕ) (hs : IsCoherentFamily s) : Tree :=
  functionTree (aronszajnNodes s) (aronszajnNodes_restrictionClosed s hs)

private theorem injection_aronszajn_level_countable
    (s : (a : OmegaOne) → Set.Iio a → ℕ) (hs : IsCoherentFamily s)
    (a : Ordinal) (ha : a < Ordinal.omega 1) :
    (level (aronszajnTree s hs) a).Countable := by
  classical
  let b : OmegaOne := Ordinal.ToType.mk ⟨a, ha⟩
  let : Countable (Set.Iio b) := injection_domain_countable b
  let F : Set (Set.Iio b → ℕ) := {f | f =ᶠ[Filter.cofinite] s b}
  have hF : F.Countable := finite_modification_class_countable (s b)
  have himage : ((fun f : Set.Iio b → ℕ => (⟨b, f⟩ : FunctionNode _ ℕ)) '' F).Countable :=
    hF.image _
  apply Set.MapsTo.countable_of_injOn (t := (fun f : Set.Iio b → ℕ => (⟨b, f⟩ : FunctionNode _ ℕ)) '' F)
      (f := Subtype.val) _ Subtype.val_injective.injOn himage
  rintro ⟨⟨c, f⟩, ht⟩ he
  have hc : c = b := by
    apply (Ordinal.ToType.mk (o := Ordinal.omega 1)).symm.injective
    apply Subtype.ext
    have he' := (functionTree_nodeHeight (aronszajnNodes s)
      (aronszajnNodes_restrictionClosed s hs) ⟨⟨c, f⟩, ht⟩).symm.trans he
    simpa [b] using he'
  subst c
  exact ⟨f, ht.2, rfl⟩

theorem aronszajnTree_spec (s : (a : OmegaOne) → Set.Iio a → ℕ) (hs : IsCoherentFamily s) :
    IsAronszajnTree (aronszajnTree s hs) ℵ₁ ∧
      (∀ a < Ordinal.omega 1, (level (aronszajnTree s hs) a).Countable) ∧
      ∀ B, IsBranch (aronszajnTree s hs) B → B.Countable := by
  have hheight : treeHeight (aronszajnTree s hs) = Ordinal.omega 1 :=
    injection_height _ _ (fun a => ⟨s a, (hs.1 a).1, Filter.EventuallyEq.rfl⟩)
  have hlevels := injection_aronszajn_level_countable s hs
  refine ⟨⟨⟨aleph0_le_aleph 1, ?_, ?_⟩, ?_⟩, hlevels, ?_⟩
  · simpa using hheight
  · intro a ha
    have ha' : a < Ordinal.omega 1 := by simpa using ha
    exact (Cardinal.le_aleph0_iff_set_countable.mpr (hlevels a ha')).trans_lt aleph0_lt_aleph_one
  · exact injection_no_cofinal _ _ (fun _ h => h.1) hheight
  · intro B hB
    exact injection_branch_countable _ _ (fun _ h => h.1) hB

/-- Unconditional existence; coherent-family existence is part of the construction. -/
theorem aronszajn_exists :
    ∃ T : Tree.{0}, IsAronszajnTree T ℵ₁ ∧
      (∀ a < Ordinal.omega 1, (level T a).Countable) ∧
      ∀ B, IsBranch T B → B.Countable := by
  obtain ⟨s, hs⟩ := coherent_family_exists
  exact ⟨aronszajnTree s hs, aronszajnTree_spec s hs⟩

theorem aronszajnTree_root_and_extensions
    (s : (a : OmegaOne) → Set.Iio a → ℕ) (hs : IsCoherentFamily s) :
    (∃! r : aronszajnTree s hs, nodeHeight (aronszajnTree s hs) r = 0) ∧
      ∀ t : aronszajnTree s hs, ∀ b : OmegaOne, t.1.1 < b →
        ∃ u : aronszajnTree s hs, t ≤ u ∧ u.1.1 = b := by
  classical
  let a₀ : OmegaOne := Ordinal.ToType.mk ⟨0, by simpa using Ordinal.omega_pos 1⟩
  let r : aronszajnTree s hs := ⟨⟨a₀, s a₀⟩, (hs.1 a₀).1, Filter.EventuallyEq.rfl⟩
  have hr : nodeHeight (aronszajnTree s hs) r = 0 := by
    change nodeHeight (functionTree (aronszajnNodes s) (aronszajnNodes_restrictionClosed s hs)) r = 0
    simpa [r, a₀] using functionTree_nodeHeight (aronszajnNodes s)
      (aronszajnNodes_restrictionClosed s hs) r
  refine ⟨⟨r, hr, ?_⟩, ?_⟩
  · rintro ⟨⟨a, f⟩, ht⟩ ha
    have haa : a = a₀ := by
      apply (Ordinal.ToType.mk (o := Ordinal.omega 1)).symm.injective
      apply Subtype.ext
      simpa [a₀] using (functionTree_nodeHeight (aronszajnNodes s)
        (aronszajnNodes_restrictionClosed s hs) ⟨⟨a, f⟩, ht⟩).symm.trans ha
    subst a
    apply Subtype.ext
    apply congrArg (Sigma.mk a₀)
    funext i
    have hi := (Ordinal.ToType.mk (o := Ordinal.omega 1)).symm.strictMono i.2
    change i.1.toOrd.1 < a₀.toOrd.1 at hi
    have hi' : i.1.toOrd.1 < (0 : Ordinal) := by simpa [a₀] using hi
    exact False.elim (not_lt_zero hi')
  · intro t b hab
    have he : t.1.2 =ᶠ[Filter.cofinite] s b ∘ initialSegmentEmbedding hab.le :=
      t.2.2.trans (hs.2 b t.1.1 hab).symm
    obtain ⟨f, hf, hold, hmod, _, _⟩ := finite_repair
      (initialSegmentEmbedding hab.le) (s b) t.1.2 (hs.1 b).1 (hs.1 b).2
      t.2.1 he ∅ Set.finite_empty (by simp)
    refine ⟨⟨⟨b, f⟩, hf, hmod⟩, ?_, rfl⟩
    exact ⟨hab.le, hold.symm⟩

end Lemmatheca.SetTheory.InfiniteTrees
