import Lemmatheca.SetTheory.InfiniteTrees
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Order.OrderIsoNat

/-! Finite-colour partition relations and length-tagged colouring trees.

An n-element subset is a finset with its cardinality certificate. Homogeneity
includes an actual colour witness even when the collection of tested subsets is
empty. Finite carrier names are `Fin r`, corresponding to the initial segment
{0,...,r-1}. Partition notation is represented by carrier types and an
equivalence to the target carrier, rather than by chosen cardinal representatives.
-/

noncomputable section

namespace Lemmatheca.SetTheory.PartitionRelations

open Set Cardinal
universe u v w

abbrev Subsets (α : Type u) (n : ℕ) := {s : Finset α // s.card = n}

abbrev Coloring (α : Type u) (n : ℕ) (K : Type v) := Subsets α n → K

def IsHomogeneousIn {α : Type u} {K : Type v} {n : ℕ}
    (c : Coloring α n K) (H : Set α) (i : K) : Prop :=
  ∀ s : Subsets α n, (↑s.val : Set α) ⊆ H → c s = i

def IsHomogeneous {α : Type u} {K : Type v} {n : ℕ}
    (c : Coloring α n K) (H : Set α) : Prop :=
  ∃ i : K, IsHomogeneousIn c H i

def PartitionRelation (α : Type u) (β : Type v) (n k : ℕ) : Prop :=
  ∀ c : Coloring α n (Fin k),
    ∃ H : Set α, Nonempty (H ≃ β) ∧ IsHomogeneous c H

theorem homogeneous_of_card_lt {α : Type u} {K : Type v} {n : ℕ}
    (c : Coloring α n K) (H : Finset α) (hH : H.card < n) :
    ∀ i : K, IsHomogeneousIn c (↑H : Set α) i := by
  intro i s hs
  have h := Finset.card_le_card hs
  rw [s.property] at h
  omega

theorem homogeneous_of_card_eq {α : Type u} {K : Type v} {n : ℕ}
    (c : Coloring α n K) (H : Finset α) (hH : H.card = n) :
    IsHomogeneous c (↑H : Set α) := by
  refine ⟨c ⟨H, hH⟩, ?_⟩
  intro s hs
  have he : s.val = H := Finset.eq_of_subset_of_card_le hs (by rw [s.property, hH])
  have he' : s = ⟨H, hH⟩ := Subtype.ext he
  rw [he']

def pullback {α : Type u} {β : Type v} {K : Type w} {n : ℕ}
    (e : α ↪ β) (c : Coloring β n K) : Coloring α n K :=
  fun s => c ⟨s.val.map e, (Finset.card_map e).trans s.property⟩

private theorem pullback_refl {α : Type u} {K : Type v} {n : ℕ}
    (c : Coloring α n K) : pullback (Function.Embedding.refl α) c = c := by
  funext s
  apply congrArg c
  apply Subtype.ext
  exact Finset.map_refl

theorem pullback_homogeneousIn {α : Type u} {β : Type v} {K : Type w} {n : ℕ}
    (e : α ↪ β) (c : Coloring β n K) (H : Set α) (i : K) :
    IsHomogeneousIn (pullback e c) H i ↔ IsHomogeneousIn c (e '' H) i := by
  classical
  constructor
  · intro h t ht
    let s := t.val.preimage e e.injective.injOn
    have hrange : ∀ x ∈ t.val, x ∈ Set.range e := by
      intro x hx
      obtain ⟨a, _, ha⟩ := ht hx
      exact ⟨a, ha⟩
    have hmap : s.map e = t.val := by
      rw [Finset.map_eq_image, Finset.image_preimage]
      exact Finset.filter_eq_self.mpr hrange
    have hcard : s.card = n := by
      rw [← Finset.card_map e, hmap]
      exact t.property
    have hs : (↑s : Set α) ⊆ H := by
      intro a ha
      obtain ⟨b, hb, he⟩ := ht (Finset.mem_preimage.mp ha)
      exact e.injective he ▸ hb
    have he : (⟨s.map e, (Finset.card_map e).trans hcard⟩ : Subsets β n) = t :=
      Subtype.ext hmap
    simpa only [pullback, he] using h ⟨s, hcard⟩ hs
  · intro h s hs
    apply h
    rw [Finset.coe_map]
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, hs ha, rfl⟩

theorem tails_intersection_empty (a : ℕ → ℕ) (ha : StrictMono a)
    (A : ℕ → Set ℕ) (hA : ∀ i, ∀ x ∈ A i, a i < x) :
    (⋂ i, A i) = ∅ := by
  ext x
  constructor
  · intro hx
    have h := hA x x (Set.mem_iInter.mp hx x)
    have hle := ha.id_le x
    change x ≤ a x at hle
    omega
  · simp

private theorem infinite_inside {n k : ℕ}
    (ih : ∀ c : Coloring ℕ n (Fin k), ∃ H : Set ℕ, H.Infinite ∧ IsHomogeneous c H)
    (c : Coloring ℕ n (Fin k)) (S : Set ℕ) (hS : S.Infinite) :
    ∃ H : Set ℕ, H ⊆ S ∧ H.Infinite ∧ IsHomogeneous c H := by
  classical
  let : Infinite S := hS.to_subtype
  let b : ℕ ≃ S := (Nat.Subtype.orderIsoOfNat S).toEquiv
  let e : ℕ ↪ ℕ := ⟨fun a => (b a).val, fun _ _ h => b.injective (Subtype.ext h)⟩
  obtain ⟨H, hH, i, hi⟩ := ih (pullback e c)
  refine ⟨e '' H, ?_, hH.image e.injective.injOn, i,
    (pullback_homogeneousIn e c H i).mp hi⟩
  rintro _ ⟨a, _, rfl⟩
  exact (b a).property

private def pointColoring {n k : ℕ} (c : Coloring ℕ (n + 1) (Fin k))
    (a : ℕ) (z : Fin k) : Coloring ℕ n (Fin k) := by
  classical
  exact fun s => if h : a ∉ s.val then
    c ⟨insert a s.val, by rw [Finset.card_insert_of_notMem h, s.property]⟩ else z

private structure RamseyState {n k : ℕ} (c : Coloring ℕ (n + 1) (Fin k)) (z : Fin k) where
  point : ℕ
  tail : Set ℕ
  color : Fin k
  infinite : tail.Infinite
  above : ∀ x ∈ tail, point < x
  homogeneous : IsHomogeneousIn (pointColoring c point z) tail color

private theorem infinite_ramsey_all (n k : ℕ) (hk : 0 < k)
    (c : Coloring ℕ n (Fin k)) :
    ∃ H : Set ℕ, H.Infinite ∧ IsHomogeneous c H := by
  classical
  induction n with
  | zero =>
      refine ⟨Set.univ, Set.infinite_univ, c ⟨∅, Finset.card_empty⟩, ?_⟩
      intro s _
      have he : s = ⟨∅, Finset.card_empty⟩ := Subtype.ext (Finset.card_eq_zero.mp s.property)
      rw [he]
  | succ n ih =>
      let z : Fin k := ⟨0, hk⟩
      let State := RamseyState c z
      have tailInfinite (a : ℕ) : (Set.Ioi a).Infinite := by
        have h := Set.infinite_univ.sdiff (Set.finite_Iic a)
        exact h.mono (fun _ hx => Nat.lt_of_not_ge hx.2)
      obtain ⟨A₀, hA₀, hA₀inf, d₀, hd₀⟩ :=
        infinite_inside ih (pointColoring c 0 z) (Set.Ioi 0) (tailInfinite 0)
      let initial : State := ⟨0, A₀, d₀, hA₀inf, fun x hx => hA₀ hx, hd₀⟩
      have next (s : State) : ∃ t : State, t.point ∈ s.tail ∧ t.tail ⊆ s.tail := by
        let a := Nat.find s.infinite.nonempty
        have ha : a ∈ s.tail := Nat.find_spec s.infinite.nonempty
        let B := s.tail \ Set.Iic a
        have hB : B.Infinite := s.infinite.sdiff (Set.finite_Iic a)
        obtain ⟨A, hAB, hAinf, d, hd⟩ :=
          infinite_inside ih (pointColoring c a z) B hB
        let t : State := ⟨a, A, d, hAinf,
          fun x hx => Nat.lt_of_not_ge (hAB hx).2, hd⟩
        exact ⟨t, ha, fun x hx => (hAB hx).1⟩
      let f : ℕ → State := fun i => Nat.rec initial (fun _ s => (next s).choose) i
      have hf (i : ℕ) : (f (i + 1)).point ∈ (f i).tail ∧
          (f (i + 1)).tail ⊆ (f i).tail := (next (f i)).choose_spec
      have hm : StrictMono (fun i => (f i).point) :=
        strictMono_nat_of_lt_succ fun i => (f i).above _ (hf i).1
      have nested {i j : ℕ} (hij : i ≤ j) : (f j).tail ⊆ (f i).tail := by
        induction j, hij using Nat.le_induction with
        | base => exact Set.Subset.rfl
        | succ j hij h => exact (hf j).2.trans h
      have later {i j : ℕ} (hij : i < j) : (f j).point ∈ (f i).tail := by
        cases j with
        | zero => omega
        | succ j => exact nested (Nat.le_of_lt_succ hij) (hf j).1
      obtain ⟨d, hd⟩ := Finite.exists_infinite_fiber (fun i => (f i).color)
      let I : Set ℕ := {i | (f i).color = d}
      have hI : I.Infinite := Set.infinite_coe_iff.mp hd
      let e : ℕ ↪ ℕ := ⟨fun i => (f i).point, hm.injective⟩
      refine ⟨e '' I, hI.image e.injective.injOn, d,
        (pullback_homogeneousIn e c I d).mp ?_⟩
      intro s hs
      have hnon : s.val.Nonempty := Finset.card_pos.mp (by rw [s.property]; omega)
      let i := s.val.min' hnon
      have hi : i ∈ s.val := Finset.min'_mem _ _
      let rest := s.val.erase i
      have hrest : rest.card = n := by
        dsimp only [rest]
        rw [Finset.card_erase_of_mem hi, s.property]
        omega
      let t : Subsets ℕ n := ⟨rest.map e, (Finset.card_map e).trans hrest⟩
      have ht : (↑t.val : Set ℕ) ⊆ (f i).tail := by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
        have hj' := Finset.mem_erase.mp hj
        have hij : i < j := lt_of_le_of_ne (Finset.min'_le _ _ hj'.2) hj'.1.symm
        exact later hij
      have hai : (f i).point ∉ t.val := by
        intro h
        exact (lt_irrefl _) ((f i).above _ (ht h))
      have hc := (f i).homogeneous t ht
      simp only [pointColoring, dite_eq_left hai] at hc
      have he : (⟨insert (f i).point t.val, by
          rw [Finset.card_insert_of_notMem hai, t.property]⟩ : Subsets ℕ (n + 1)) =
          ⟨s.val.map e, (Finset.card_map e).trans s.property⟩ := by
        apply Subtype.ext
        change insert (e i) (rest.map e) = s.val.map e
        rw [← Finset.map_insert, Finset.insert_erase hi]
      rw [he] at hc
      exact hc.trans (hs hi)

theorem infinite_ramsey {n k : ℕ} (_hn : 0 < n) (hk : 0 < k)
    (c : Coloring ℕ n (Fin k)) :
    ∃ H : Set ℕ, H.Infinite ∧ IsHomogeneous c H :=
  infinite_ramsey_all n k hk c

/-- The first component is retained even for an empty colouring domain. -/
structure FiniteColoringNode (n k : ℕ) where
  length : ℕ
  coloring : Coloring (Fin length) n (Fin k)

def Extends {n k : ℕ} (s t : FiniteColoringNode n k) : Prop :=
  ∃ h : s.length ≤ t.length,
    s.coloring = pullback (Fin.castLEEmb h) t.coloring

instance coloringNodePartialOrder (n k : ℕ) : PartialOrder (FiniteColoringNode n k) where
  le := Extends
  le_refl := by
    intro s
    refine ⟨le_rfl, ?_⟩
    funext a
    apply congrArg s.coloring
    apply Subtype.ext
    simp [Fin.castLEEmb]
  le_trans := by
    rintro s t r ⟨hst, he⟩ ⟨htr, hf⟩
    refine ⟨hst.trans htr, ?_⟩
    rw [he, hf]
    funext a
    apply congrArg r.coloring
    apply Subtype.ext
    change (a.val.map (Fin.castLEEmb hst)).map (Fin.castLEEmb htr) =
      a.val.map (Fin.castLEEmb (hst.trans htr))
    rw [Finset.map_map]
    congr 1
  le_antisymm := by
    rintro ⟨r, c⟩ ⟨s, d⟩ ⟨hrs, he⟩ ⟨hsr, _⟩
    dsimp only at hrs hsr he
    obtain rfl := hrs.antisymm hsr
    have hc : c = d := by simpa [Fin.castLEEmb, pullback_refl] using he
    cases hc
    rfl

def restrictNode {n k : ℕ} (t : FiniteColoringNode n k)
    (r : ℕ) (hr : r ≤ t.length) : FiniteColoringNode n k :=
  ⟨r, pullback (Fin.castLEEmb hr) t.coloring⟩

private theorem node_eq_restrict {n k : ℕ} (s t : FiniteColoringNode n k)
    (h : s ≤ t) : s = restrictNode t s.length h.choose := by
  rcases s with ⟨r, c⟩
  rcases t with ⟨q, d⟩
  have he := h.choose_spec
  change c = pullback (Fin.castLEEmb h.choose) d at he
  exact congrArg (FiniteColoringNode.mk r) he

private theorem node_lt_iff {n k : ℕ} (s t : FiniteColoringNode n k) :
    s < t ↔ s ≤ t ∧ s.length < t.length := by
  rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨h, hn⟩
    refine ⟨h, lt_of_le_of_ne h.choose ?_⟩
    intro he
    apply hn
    rcases s with ⟨q, d⟩
    rcases t with ⟨r, c⟩
    dsimp only at he
    subst r
    have hdc : d = c := by
      have hh := h.choose_spec
      simpa [Fin.castLEEmb, pullback_refl] using hh
    cases hdc
    rfl
  · rintro ⟨h, hl⟩
    exact ⟨h, fun he => hl.ne (congrArg FiniteColoringNode.length he)⟩

private theorem restrict_le_iff {n k : ℕ} (t : FiniteColoringNode n k)
    (r s : ℕ) (hr : r ≤ t.length) (hs : s ≤ t.length) :
    restrictNode t r hr ≤ restrictNode t s hs ↔ r ≤ s := by
  constructor
  · exact fun h => h.choose
  · intro h
    refine ⟨h, ?_⟩
    change pullback (Fin.castLEEmb hr) t.coloring =
      pullback (Fin.castLEEmb h) (pullback (Fin.castLEEmb hs) t.coloring)
    funext (a : Subsets (Fin r) n)
    apply congrArg t.coloring
    apply Subtype.ext
    change a.val.map (Fin.castLEEmb hr) =
      (a.val.map (Fin.castLEEmb h)).map (Fin.castLEEmb hs)
    rw [Finset.map_map]
    congr 1

private def predecessorLengthIso {n k : ℕ} (t : FiniteColoringNode n k) :
    Set.Iio t ≃o Fin t.length where
  toFun p := ⟨p.val.length, ((node_lt_iff p.val t).mp p.property).2⟩
  invFun r := ⟨restrictNode t r.val r.isLt.le,
    (node_lt_iff _ _).mpr ⟨⟨r.isLt.le, rfl⟩, r.isLt⟩⟩
  left_inv p := by
    apply Subtype.ext
    exact (node_eq_restrict p.val t p.property.le).symm
  right_inv _ := rfl
  map_rel_iff' := by
    intro p q
    constructor
    · intro h
      change p.val ≤ q.val
      rw [node_eq_restrict p.val t p.property.le,
        node_eq_restrict q.val t q.property.le]
      exact (restrict_le_iff t _ _ _ _).mpr h
    · exact fun h => h.choose

theorem coloringNode_predecessors_wellOrdered (n k : ℕ)
    (t : FiniteColoringNode n k) : IsWellOrder (Set.Iio t) (· < ·) :=
  (predecessorLengthIso t).toOrderEmbedding.isWellOrder

def coloringTree (n k : ℕ) : InfiniteTrees.Tree where
  carrier := FiniteColoringNode n k
  predecessors_wellOrdered := coloringNode_predecessors_wellOrdered n k

theorem coloringTree_nodeHeight (n k : ℕ) (t : coloringTree n k) :
    InfiniteTrees.nodeHeight (coloringTree n k) t = (t.length : Ordinal) := by
  let := coloringNode_predecessors_wellOrdered n k t
  change Ordinal.type ((· < ·) : Set.Iio t → Set.Iio t → Prop) = _
  exact (predecessorLengthIso t).toRelIsoLT.ordinalType_congr.trans (Ordinal.type_fin _)

theorem coloringTree_levels_finite (n k r : ℕ) :
    (InfiniteTrees.level (coloringTree n k) r).Finite := by
  classical
  let L := InfiniteTrees.level (coloringTree n k) r
  have hl (t : L) : t.val.length = r := by
    have ht := t.property
    change InfiniteTrees.nodeHeight (coloringTree n k) t.val = (r : Ordinal) at ht
    rw [coloringTree_nodeHeight] at ht
    exact_mod_cast ht
  let f (t : L) : Coloring (Fin r) n (Fin k) := hl t ▸ t.val.coloring
  have hf : Function.Injective f := by
    rintro ⟨⟨s, c⟩, hs⟩ ⟨⟨t, d⟩, ht⟩ he
    have hsr := hl ⟨⟨s, c⟩, hs⟩
    have htr := hl ⟨⟨t, d⟩, ht⟩
    dsimp only at hsr htr
    subst s
    subst t
    apply Subtype.ext
    have hcd : c = d := he
    cases hcd
    rfl
  let : Finite (Coloring (Fin r) n (Fin k)) := inferInstance
  let : Finite L := Finite.of_injective f hf
  exact Set.toFinite L

theorem coloringTree_height (n k : ℕ) (hk : 0 < k) :
    InfiniteTrees.treeHeight (coloringTree n k) = Ordinal.omega0 := by
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro t
    rw [coloringTree_nodeHeight]
    have hh : (t.length : Ordinal) + 1 < Ordinal.omega0 := by
      simpa using Ordinal.natCast_lt_omega0 (t.length + 1)
    exact hh.le
  · apply Ordinal.omega0_le.mpr
    intro r
    let t : coloringTree n k := ⟨r, fun _ => ⟨0, hk⟩⟩
    have h := Ordinal.le_iSup (fun t : coloringTree n k =>
      InfiniteTrees.nodeHeight (coloringTree n k) t + 1) t
    rw [coloringTree_nodeHeight] at h
    exact (show (r : Ordinal) ≤ (r : Ordinal) + 1 from le_self_add).trans h

def FiniteRamseyProperty (N n k m : ℕ) : Prop :=
  ∀ c : Coloring (Fin N) n (Fin k),
    ∃ H : Finset (Fin N), H.card = m ∧ IsHomogeneous c (↑H : Set (Fin N))

private theorem finite_carrier (s : Finset ℕ) :
    ∃ r : ℕ, ∃ t : Finset (Fin r), t.card = s.card ∧ t.map Fin.valEmbedding = s := by
  classical
  let r := s.sup id + 1
  let t := s.preimage (Fin.valEmbedding : Fin r ↪ ℕ)
    (Fin.valEmbedding : Fin r ↪ ℕ).injective.injOn
  have hbound : ∀ a ∈ s, a < r := fun a ha => Nat.lt_succ_of_le (Finset.le_sup (f := id) ha)
  have hm : t.map Fin.valEmbedding = s := by
    ext a
    constructor
    · intro ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
      exact Finset.mem_preimage.mp hb
    · intro ha
      exact Finset.mem_map.mpr ⟨⟨a, hbound a ha⟩, Finset.mem_preimage.mpr ha, rfl⟩
  refine ⟨r, t, ?_, hm⟩
  rw [← Finset.card_map Fin.valEmbedding, hm]

private theorem glue_colorings {n k : ℕ} (f : ∀ r, Coloring (Fin r) n (Fin k))
    (hf : ∀ {r s} (h : r ≤ s), f r = pullback (Fin.castLEEmb h) (f s)) :
    ∃ c : Coloring ℕ n (Fin k), ∀ r (t : Subsets (Fin r) n),
      c ⟨t.val.map Fin.valEmbedding, (Finset.card_map _).trans t.property⟩ = f r t := by
  classical
  have lift (s : Subsets ℕ n) :
      ∃ r, ∃ t : Subsets (Fin r) n, t.val.map Fin.valEmbedding = s.val := by
    obtain ⟨r, t, ht, hm⟩ := finite_carrier s.val
    exact ⟨r, ⟨t, ht.trans s.property⟩, hm⟩
  have compare {r q} (t : Subsets (Fin r) n) (u : Subsets (Fin q) n)
      (h : t.val.map Fin.valEmbedding = u.val.map Fin.valEmbedding) : f r t = f q u := by
    let m := max r q
    let er := Fin.castLEEmb (le_max_left r q)
    let eq := Fin.castLEEmb (le_max_right r q)
    have he : t.val.map er = u.val.map eq := by
      apply Finset.map_injective (Fin.valEmbedding : Fin m ↪ ℕ)
      simp only [Finset.map_map]
      exact h
    calc
      f r t = f m ⟨t.val.map er, (Finset.card_map _).trans t.property⟩ :=
        congrFun (hf (le_max_left r q)) t
      _ = f m ⟨u.val.map eq, (Finset.card_map _).trans u.property⟩ :=
        congrArg (f m) (Subtype.ext he)
      _ = f q u := (congrFun (hf (le_max_right r q)) u).symm
  let c : Coloring ℕ n (Fin k) := fun s =>
    f (lift s).choose (lift s).choose_spec.choose
  refine ⟨c, ?_⟩
  intro r t
  exact compare _ t (lift _).choose_spec.choose_spec

private theorem bad_restrict {r s n k m : ℕ} (h : r ≤ s)
    (c : Coloring (Fin s) n (Fin k))
    (hc : ¬ ∃ H : Finset (Fin s), H.card = m ∧ IsHomogeneous c (↑H : Set (Fin s))) :
    ¬ ∃ H : Finset (Fin r), H.card = m ∧
      IsHomogeneous (pullback (Fin.castLEEmb h) c) (↑H : Set (Fin r)) := by
  classical
  rintro ⟨H, hH, i, hi⟩
  apply hc
  refine ⟨H.map (Fin.castLEEmb h), (Finset.card_map _).trans hH, i, ?_⟩
  rw [Finset.coe_map]
  exact (pullback_homogeneousIn _ c (↑H : Set (Fin r)) i).mp hi

theorem finite_ramsey {n k m : ℕ} (hn : 0 < n) (hk : 0 < k) (_hm : 0 < m) :
    ∃ N : ℕ, m ≤ N ∧ FiniteRamseyProperty N n k m := by
  classical
  by_contra h
  have counter (N : ℕ) (hN : m ≤ N) :
      ∃ c : Coloring (Fin N) n (Fin k),
        ¬ ∃ H : Finset (Fin N), H.card = m ∧ IsHomogeneous c (↑H : Set (Fin N)) := by
    have hp : ¬ FiniteRamseyProperty N n k m := fun hp => h ⟨N, hN, hp⟩
    exact not_forall.mp hp
  let A (r : ℕ) := {c : Coloring (Fin r) n (Fin k) //
    ¬ ∃ H : Finset (Fin r), H.card = m ∧ IsHomogeneous c (↑H : Set (Fin r))}
  let (r : ℕ) : Finite (A r) := inferInstance
  let (r : ℕ) : Nonempty (A r) := by
    obtain ⟨c, hc⟩ := counter (max r m) (le_max_right _ _)
    exact ⟨⟨pullback (Fin.castLEEmb (le_max_left _ _)) c,
      bad_restrict (le_max_left _ _) c hc⟩⟩
  let π : {r s : ℕ} → (h : r ≤ s) → A s → A r :=
    fun {_ _} h c => ⟨pullback (Fin.castLEEmb h) c.val, bad_restrict h c.val c.property⟩
  have hrefl (r : ℕ) (c : A r) : π le_rfl c = c := by
    apply Subtype.ext
    simp [π, Fin.castLEEmb, pullback_refl]
  have htrans {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) (c : A t) :
      π hrs (π hst c) = π (hrs.trans hst) c := by
    apply Subtype.ext
    funext a
    apply congrArg c.val
    apply Subtype.ext
    change (a.val.map (Fin.castLEEmb hrs)).map (Fin.castLEEmb hst) =
      a.val.map (Fin.castLEEmb (hrs.trans hst))
    rw [Finset.map_map]
    congr 1
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite π
    (fun {_} c => hrefl _ c) (fun {_ _ _} hrs hst c => htrans hrs hst c)
    (fun _ _ => Set.toFinite _)
  have hcompat {r s : ℕ} (hrs : r ≤ s) :
      (f r).val = pullback (Fin.castLEEmb hrs) (f s).val :=
    (congrArg Subtype.val (hf hrs)).symm
  obtain ⟨c, hc⟩ := glue_colorings (fun r => (f r).val) (fun {_ _} hrs => hcompat hrs)
  obtain ⟨H, hH, i, hi⟩ := infinite_ramsey hn hk c
  obtain ⟨F, hFH, hF⟩ := hH.exists_subset_card_eq m
  obtain ⟨r, G, hG, hmap⟩ := finite_carrier F
  apply (f r).property
  refine ⟨G, hG.trans hF, i, ?_⟩
  intro s hs
  rw [← hc r s]
  apply hi
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
  apply hFH
  rw [← hmap]
  exact Finset.mem_map.mpr ⟨a, hs ha, rfl⟩

def ramseyNumber (n k m : ℕ) (hn : 0 < n) (hk : 0 < k) (hm : 0 < m) : ℕ := by
  classical
  exact Nat.find (finite_ramsey hn hk hm)

theorem ramseyNumber_spec (n k m : ℕ) (hn : 0 < n) (hk : 0 < k) (hm : 0 < m) :
    m ≤ ramseyNumber n k m hn hk hm ∧
      FiniteRamseyProperty (ramseyNumber n k m hn hk hm) n k m ∧
      ∀ N : ℕ, m ≤ N → FiniteRamseyProperty N n k m →
        ramseyNumber n k m hn hk hm ≤ N := by
  classical
  dsimp only [ramseyNumber]
  have h := Nat.find_spec (finite_ramsey hn hk hm)
  exact ⟨h.1, h.2, fun N hN hp => Nat.find_min' _ ⟨hN, hp⟩⟩

theorem simultaneous_infinite_ramsey (r : ℕ) (n k : Fin r → ℕ)
    (hn : ∀ j, 0 < n j) (hk : ∀ j, 0 < k j)
    (c : ∀ j, Coloring ℕ (n j) (Fin (k j))) :
    ∃ H : Set ℕ, H.Infinite ∧ ∀ j, IsHomogeneous (c j) H := by
  classical
  induction r with
  | zero => exact ⟨Set.univ, Set.infinite_univ, fun j => j.elim0⟩
  | succ r ih =>
      obtain ⟨H₀, hH₀, hprev⟩ := ih
        (fun j => n j.castSucc) (fun j => k j.castSucc)
        (fun j => hn j.castSucc) (fun j => hk j.castSucc) (fun j => c j.castSucc)
      obtain ⟨H, hHH₀, hH, hlast⟩ := infinite_inside
        (fun d => infinite_ramsey (hn (Fin.last r)) (hk (Fin.last r)) d)
        (c (Fin.last r)) H₀ hH₀
      refine ⟨H, hH, ?_⟩
      intro j
      refine Fin.lastCases hlast (fun j => ?_) j
      obtain ⟨i, hi⟩ := hprev j
      exact ⟨i, fun s hs => hi s (hs.trans hHH₀)⟩

def minimumColoring (n : ℕ) (hn : 0 < n) : Coloring ℕ n ℕ :=
  fun s => s.val.min' (Finset.card_pos.mp (s.property.symm ▸ hn))

theorem minimumColoring_no_large_homogeneous (n : ℕ) (hn : 0 < n)
    (H : Finset ℕ) (hH : n < H.card) :
    ¬ IsHomogeneous (minimumColoring n hn) (↑H : Set ℕ) := by
  classical
  rintro ⟨i, hi⟩
  have hHnon : H.Nonempty := Finset.card_pos.mp (by omega)
  let a := H.min' hHnon
  have ha : a ∈ H := Finset.min'_mem _ _
  have hcard : n ≤ (H.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcard
  have hTnon : T.Nonempty := Finset.card_pos.mp (hTcard.symm ▸ hn)
  let b := T.min' hTnon
  have hb : b ∈ T := Finset.min'_mem _ _
  have hba : b ≠ a := (Finset.mem_erase.mp (hTsub hb)).1
  have haT : a ∉ T := fun h => (Finset.mem_erase.mp (hTsub h)).1 rfl
  let U := insert a (T.erase b)
  have hUcard : U.card = n := by
    rw [Finset.card_insert_of_notMem (fun h => haT (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hb, hTcard]
    omega
  have hUsub : (↑U : Set ℕ) ⊆ H := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    · exact Finset.mem_of_mem_erase (hTsub (Finset.mem_of_mem_erase hx))
  have hUnon : U.Nonempty := Finset.card_pos.mp (hUcard.symm ▸ hn)
  have hUmin : U.min' hUnon = a := by
    apply le_antisymm
    · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    · exact Finset.le_min' U hUnon a (fun x hx => Finset.min'_le H x (hUsub hx))
  have hT := hi ⟨T, hTcard⟩ (fun x hx => Finset.mem_of_mem_erase (hTsub hx))
  have hU := hi ⟨U, hUcard⟩ hUsub
  change b = i at hT
  change U.min' hUnon = i at hU
  exact hba ((hT.trans hU.symm).trans hUmin)

theorem minimumColoring_no_infinite_homogeneous (n : ℕ) (hn : 0 < n)
    (H : Set ℕ) (hH : H.Infinite) :
    ¬ IsHomogeneous (minimumColoring n hn) H := by
  rintro ⟨i, hi⟩
  obtain ⟨F, hFH, hF⟩ := hH.exists_subset_card_eq (n + 1)
  apply minimumColoring_no_large_homogeneous n hn F (by rw [hF]; omega)
  exact ⟨i, fun s hs => hi s (hs.trans hFH)⟩

theorem zero_arity_homogeneous {α : Type u} {K : Type v}
    (c : Coloring α 0 K) (H : Set α) :
    IsHomogeneousIn c H (c ⟨∅, Finset.card_empty⟩) := by
  intro s _
  have he : s = ⟨∅, Finset.card_empty⟩ := Subtype.ext (Finset.card_eq_zero.mp s.property)
  rw [he]

theorem empty_color_domain_iff (α : Type u) (n : ℕ) :
    Nonempty (Coloring α n (Fin 0)) ↔ IsEmpty (Subsets α n) := by
  constructor
  · rintro ⟨c⟩
    exact ⟨fun s => (c s).elim0⟩
  · intro h
    let := h
    exact ⟨isEmptyElim⟩

theorem empty_color_not_homogeneous {α : Type u} {n : ℕ}
    (c : Coloring α n (Fin 0)) (H : Set α) : ¬ IsHomogeneous c H := by
  rintro ⟨i, _⟩
  exact i.elim0

end Lemmatheca.SetTheory.PartitionRelations
