import Mathlib.Tactic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Order.Extension.Linear
import Mathlib.SetTheory.Cardinal.Regular

/-! Reusable WeakerChoice definitions and results. -/

set_option autoImplicit false
universe u
namespace Lemmatheca.SetTheory.WeakerChoice
open Order
open scoped Ordinal Cardinal

/-! Universe-relative principles. Their implications in classical Lean do not
certify their strength over first-order ZF; that requires a logical encoding. -/

/-- Choice functions for sequences of nonempty subsets of a common carrier. -/
def CountableChoice : Prop := ∀ (α : Type u) (A : ℕ → Set α),
  (∀ n, (A n).Nonempty) → ∃ c : ℕ → α, ∀ n, c n ∈ A n

/-- Every point has a successor under the relation. -/
def Serial {α : Type u} (R : α → α → Prop) : Prop := ∀ x, ∃ y, R x y

/-- Dependent choice with a prescribed starting point. -/
def DependentChoice : Prop := ∀ (α : Type u) (R : α → α → Prop),
  Serial R → ∀ x₀, ∃ f : ℕ → α, f 0 = x₀ ∧ ∀ n, R (f n) (f (n + 1))

/-- Dependent choice without a prescribed starting point. -/
def UnstartedDependentChoice : Prop := ∀ (α : Type u) (R : α → α → Prop),
  Nonempty α → Serial R → ∃ f : ℕ → α, ∀ n, R (f n) (f (n + 1))

/-- Every finite initial family admits a choice function. -/
theorem finite_prefix {α : Type u} (A : ℕ → Set α) (hA : ∀ n, (A n).Nonempty) (m : ℕ) :
    ∃ c : Fin m → α, ∀ i, c i ∈ A i.val := by
  classical
  exact ⟨fun i => (hA i.val).choose, fun i => (hA i.val).choose_spec⟩

/-- Dedekind infinity means an injective self-map that is not surjective. -/
def DedekindInfinite (α : Type u) : Prop :=
  ∃ f : α → α, Function.Injective f ∧ ¬ Function.Surjective f

private theorem dedekind_of_embedding {α : Type u} (j : ℕ ↪ α) : DedekindInfinite α := by
  classical
  let f : α → α := fun a => if ha : a ∈ Set.range j then j ((ha.choose) + 1) else a
  have hf (n : ℕ) : f (j n) = j (n + 1) := by
    have ha : j n ∈ Set.range j := ⟨n, rfl⟩
    have hn : ha.choose = n := j.injective ha.choose_spec
    simp only [f, ha, dite_true, hn]
  have hout (a : α) (ha : a ∉ Set.range j) : f a = a := by simp only [f, ha, dite_false]
  refine ⟨f, ?_, ?_⟩
  · intro a b hab
    by_cases ha : a ∈ Set.range j <;> by_cases hb : b ∈ Set.range j
    · obtain ⟨n, rfl⟩ := ha
      obtain ⟨m, rfl⟩ := hb
      rw [hf, hf] at hab
      exact congrArg j (Nat.add_right_cancel (j.injective hab))
    · obtain ⟨n, rfl⟩ := ha
      rw [hf, hout b hb] at hab
      exact False.elim (hb ⟨n + 1, hab⟩)
    · obtain ⟨m, rfl⟩ := hb
      rw [hout a ha, hf] at hab
      exact False.elim (ha ⟨m + 1, hab.symm⟩)
    · simpa only [hout a ha, hout b hb] using hab
  · intro hs
    obtain ⟨a, ha⟩ := hs (j 0)
    by_cases hr : a ∈ Set.range j
    · obtain ⟨n, rfl⟩ := hr
      rw [hf] at ha
      have := j.injective ha
      omega
    · rw [hout a hr] at ha
      exact hr ⟨0, ha.symm⟩

/-- Dedekind infinity is equivalent to a proper-subset bijection and to an injection of naturals. -/
theorem dedekind_characterizations (α : Type u) :
    (DedekindInfinite α ↔ ∃ S : Set α, S ≠ Set.univ ∧ Nonempty (α ≃ S)) ∧
    (DedekindInfinite α ↔ Nonempty (ℕ ↪ α)) ∧
    (DedekindInfinite α ↔ ∃ S : Set α, Nonempty (ℕ ≃ S)) := by
  have hj : DedekindInfinite α ↔ Nonempty (ℕ ↪ α) := by
    constructor
    · rintro ⟨f, hf, hn⟩
      have hi : Infinite α := by
        by_contra h
        let : Finite α := not_infinite_iff_finite.mp h
        exact hn (Finite.surjective_of_injective hf)
      let := hi
      exact ⟨Infinite.natEmbedding α⟩
    · rintro ⟨j⟩
      exact dedekind_of_embedding j
  refine ⟨?_, hj, ?_⟩
  · constructor
    · rintro ⟨f, hf, hn⟩
      refine ⟨Set.range f, ?_, ⟨Equiv.ofInjective f hf⟩⟩
      intro hr
      apply hn
      intro a
      apply Set.mem_range.mp
      rw [hr]
      exact Set.mem_univ a
    · rintro ⟨S, hS, ⟨e⟩⟩
      refine ⟨fun a => (e a).val, Subtype.val_injective.comp e.injective, ?_⟩
      intro hs
      apply hS
      apply Set.eq_univ_of_forall
      intro a
      obtain ⟨b, rfl⟩ := hs a
      exact (e b).property
  · rw [hj]
    constructor
    · rintro ⟨j⟩
      exact ⟨Set.range j, ⟨Equiv.ofInjective j j.injective⟩⟩
    · rintro ⟨S, ⟨e⟩⟩
      exact ⟨e.toEmbedding.trans (Function.Embedding.subtype S)⟩

/-- Finite carriers are Dedekind finite. -/
theorem finite_not_dedekind (α : Type u) [Finite α] : ¬ DedekindInfinite α := by
  rintro ⟨f, hf, hn⟩
  exact hn (Finite.surjective_of_injective hf)

/-- A supplied family of natural-number encodings gives an encoding of its union. -/
theorem encoded_union {α : Type u} (A : ℕ → Set α) (j : ∀ n, A n ↪ ℕ) :
    Nonempty ((⋃ n, A n) ↪ ℕ) := by
  let : ∀ n, Countable (A n) := fun n => Function.Injective.countable (j n).injective
  have hA : ∀ n, (A n).Countable := fun n => Set.countable_coe_iff.mp inferInstance
  have hu := Set.countable_iUnion hA
  let : Countable (⋃ n, A n) := Set.countable_coe_iff.mpr hu
  exact countable_iff_nonempty_embedding.mp inferInstance

/-- Minima select from arbitrary nonempty families of subsets of naturals. -/
theorem select_minima {ι : Type u} (A : ι → Set ℕ) (h : ∀ i, (A i).Nonempty) :
    ∃ c : ι → ℕ, ∀ i, IsLeast (A i) (c i) := by
  classical
  exact ⟨fun i => sInf (A i), fun i => ⟨csInf_mem (h i),
    fun _ hx => csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ hx⟩⟩

/-- A history extends another by adding exactly one new term. -/
def OneTermExtension {α : Type u} (s t : List α) : Prop := ∃ a, t = s ++ [a]

/-- A finite selection history selects a valid value at every position. -/
def SelectionHistory {α : Type u} (A : ℕ → Set α) (s : List α) : Prop :=
  ∀ i : Fin s.length, s[i] ∈ A i.val

/-- Nonempty candidate sets make one-term extension serial on finite selection histories. -/
theorem selection_histories_serial {α : Type u} (A : ℕ → Set α)
    (hA : ∀ n, (A n).Nonempty) : SelectionHistory A [] ∧
    ∀ s, SelectionHistory A s → ∃ t, SelectionHistory A t ∧ OneTermExtension s t := by
  constructor
  · intro i; exact Fin.elim0 i
  · intro s hs
    obtain ⟨a, ha⟩ := hA s.length
    refine ⟨s ++ [a], ?_, a, rfl⟩
    intro i
    change (s ++ [a])[i.val] ∈ A i.val
    by_cases hi : i.val < s.length
    · simpa only [List.getElem_append_left hi] using (show s[i.val] ∈ A i.val from hs ⟨i.val, hi⟩)
    · have hlt := i.isLt
      simp only [List.length_append, List.length_singleton] at hlt
      have hieq : i.val = s.length := by omega
      rw [List.getElem_append]
      simp only [hieq, lt_self_iff_false, dite_false, Nat.sub_self, List.getElem_singleton]
      exact ha

/-- A supplied chain of one-term extensions has a unique infinite sequence of compatible values. -/
theorem history_path_extraction {α : Type u} (p : ℕ → List α)
    (hstep : ∀ n, OneTermExtension (p n) (p (n + 1))) :
    ∃! f : ℕ → α, ∀ n, List.ofFn (fun i : Fin ((p 0).length + n) => f i.val) = p n := by
  have hlen : ∀ n, (p n).length = (p 0).length + n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨a, ha⟩ := hstep n
      simp [ha, ih, Nat.add_assoc]
  have hpref : ∀ n m, n ≤ m → p n <+: p m := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact ⟨[], by simp⟩
    | succ m hm ih =>
      obtain ⟨a, ha⟩ := hstep m
      exact ih.trans ⟨[a], ha.symm⟩
  have hbound : ∀ n, n < (p (n + 1)).length := by
    intro n; rw [hlen]; omega
  let f : ℕ → α := fun n => (p (n + 1))[n]'(hbound n)
  have hvalue : ∀ k i (hi : i < (p k).length), f i = (p k)[i] := by
    intro k i hi
    dsimp only [f]
    rcases le_total (i + 1) k with h | h
    · exact (hpref (i + 1) k h).getElem (hbound i)
    · exact ((hpref k (i + 1) h).getElem hi).symm
  have hf : ∀ n, List.ofFn (fun i : Fin ((p 0).length + n) => f i.val) = p n := by
    intro n
    apply List.ext_getElem
    · rw [List.length_ofFn]
      exact (hlen n).symm
    · intro i hi hj
      rw [List.getElem_ofFn]
      exact hvalue n i hj
  refine ⟨f, hf, ?_⟩
  intro g hg
  funext i
  have hi : i < (p 0).length + (i + 1) := by omega
  have he := congrArg (fun s : List α => s[i]?) ((hg (i + 1)).trans (hf (i + 1)).symm)
  simpa only [List.getElem?_ofFn, hi, dite_true, Option.some.injEq] using he

/-- A supplied extension path of valid selection histories starting empty gives a choice function. -/
theorem selections_of_history_path {α : Type u} (A : ℕ → Set α) (p : ℕ → List α)
    (hzero : p 0 = []) (hvalid : ∀ n, SelectionHistory A (p n))
    (hstep : ∀ n, OneTermExtension (p n) (p (n + 1))) :
    ∃ c : ℕ → α, (∀ n, c n ∈ A n) ∧
      ∀ n, List.ofFn (fun i : Fin n => c i.val) = p n := by
  obtain ⟨c, hc, _⟩ := history_path_extraction p hstep
  have hp : ∀ n, List.ofFn (fun i : Fin n => c i.val) = p n := by
    intro n
    have h := hc n
    have hz : (p 0).length = 0 := by simp [hzero]
    simpa only [hz, Nat.zero_add, Fin.val_cast] using h
  refine ⟨c, ?_, hp⟩
  intro n
  have hv := hvalid (n + 1)
  rw [← hp (n + 1)] at hv
  have hlen : n < (List.ofFn (fun i : Fin (n + 1) => c i.val)).length := by simp
  have hvn : (List.ofFn (fun i : Fin (n + 1) => c i.val))[n] ∈ A n := hv ⟨n, hlen⟩
  simpa only [List.getElem_ofFn, Fin.val_mk] using hvn

/-- Supplied choices along an enumeration transfer to the indexed family. -/
theorem reindex_selections {ι α : Type u} (A : ι → Set α) (e : ℕ → ι)
    (he : Function.Surjective e) (c : ℕ → α) (hc : ∀ n, c n ∈ A (e n)) :
    ∃ s : ι → α, ∀ i, s i ∈ A i := by
  classical
  exact ⟨fun i => c (he i).choose, fun i => by
    simpa only [(he i).choose_spec] using hc (he i).choose⟩

/-- The union of supplied finite injections has a countably infinite range. -/
theorem finite_injection_union {α : Type u} (e : ∀ n : ℕ, Fin (n + 1) ↪ α) :
    let B := ⋃ n, Set.range (e n)
    B.Countable ∧ Infinite B ∧ Nonempty (ℕ ≃ B) := by
  dsimp only
  let B := ⋃ n, Set.range (e n)
  have hcount : B.Countable := Set.countable_iUnion (fun n => Set.countable_range (e n))
  let : Countable B := Set.countable_coe_iff.mpr hcount
  have hinf : Infinite B := by
    by_contra hn
    let : Finite B := not_infinite_iff_finite.mp hn
    let : Fintype B := Fintype.ofFinite B
    let n := Fintype.card B
    let f : Fin (n + 1) → B := fun i => ⟨e n i, Set.mem_iUnion.mpr ⟨n, i, rfl⟩⟩
    have hi : Function.Injective f := fun a b hab => (e n).injective
      (congrArg Subtype.val hab)
    have hle := Fintype.card_le_of_injective f hi
    simp only [Fintype.card_fin] at hle
    omega
  let := hinf
  exact ⟨hcount, hinf, nonempty_equiv_of_countable⟩

/-- With the encodings supplied, successors of countable ordinals have a countable supremum. -/
theorem encoded_ordinals_bound {ι : Type u} [Countable ι] (a : ι → Ordinal.{u})
    (j : ∀ i, (a i + 1).ToType ↪ ℕ) :
    (⨆ i, a i + 1) < Ordinal.omega 1 ∧ ∀ i, a i < ⨆ j, a j + 1 := by
  have hcount : ∀ i, Countable (a i + 1).ToType :=
    fun i => Function.Injective.countable (j i).injective
  have hlt : ∀ i, a i + 1 < Ordinal.omega 1 := by
    intro i
    have := Cardinal.mk_le_aleph0_iff.mpr (hcount i)
    rwa [Cardinal.mk_toType, Cardinal.card_le_iff, Cardinal.succ_aleph0,
      Cardinal.ord_aleph] at this
  have hindex : Cardinal.mk ι < (Ordinal.omega 1 : Ordinal.{u}).cof := by
    rw [Cardinal.cof_omega_one]
    exact (Cardinal.mk_le_aleph0 (α := ι)).trans_lt (Cardinal.aleph0_lt_aleph_one)
  refine ⟨Ordinal.iSup_lt_of_lt_cof hindex hlt, ?_⟩
  intro i
  exact (lt_add_one (a i)).trans_le (le_ciSup Ordinal.bddAbove_of_small i)

/-- A nonempty finite relation path starts at the prescribed point. -/
def RelationHistory {α : Type u} (R : α → α → Prop) (x₀ : α) (s : List α) : Prop :=
  s.head? = some x₀ ∧ s.IsChain R

/-- A serial relation gives one-term extensions of all finite paths with a prescribed start. -/
theorem relation_histories_serial {α : Type u} (R : α → α → Prop) (hR : Serial R) (x₀ : α) :
    RelationHistory R x₀ [x₀] ∧ ∀ s, RelationHistory R x₀ s →
      ∃ t, RelationHistory R x₀ t ∧ OneTermExtension s t := by
  classical
  refine ⟨by simp [RelationHistory], ?_⟩
  intro s hs
  have hne : s ≠ [] := by
    intro he
    have hh := hs.1
    simp [he] at hh
  obtain ⟨a, ha⟩ := hR (s.getLast hne)
  refine ⟨s ++ [a], ⟨?_, ?_⟩, a, rfl⟩
  · cases s with
    | nil => exact False.elim (hne rfl)
    | cons b t => exact hs.1
  · apply hs.2.append (by simp)
    intro x hx y hy
    have hx' : s.getLast hne = x := by simpa only [List.getLast?_eq_some_getLast hne,
      Option.mem_def, Option.some.injEq] using hx
    have hy' : a = y := by simpa using hy
    simpa only [hx', hy'] using ha

/-- A supplied extension chain of finite relation paths gives a sequence with the same starting point. -/
theorem relation_sequence_of_history_path {α : Type u} (R : α → α → Prop) (x₀ : α)
    (p : ℕ → List α) (hvalid : ∀ n, RelationHistory R x₀ (p n))
    (hstep : ∀ n, OneTermExtension (p n) (p (n + 1))) :
    ∃ f : ℕ → α, f 0 = x₀ ∧ ∀ n, R (f n) (f (n + 1)) := by
  obtain ⟨f, hf, _⟩ := history_path_extraction p hstep
  have hpos : 0 < (p 0).length := by
    by_contra hn
    have he : p 0 = [] := List.length_eq_zero_iff.mp (by omega)
    have hh := (hvalid 0).1
    simp [he] at hh
  refine ⟨f, ?_, ?_⟩
  · have hz := (hvalid 0).1
    rw [← hf 0] at hz
    rw [List.head?_eq_getElem?, List.getElem?_ofFn] at hz
    simpa only [Nat.add_zero, hpos, dite_true, Option.some.injEq] using hz
  · intro n
    have hc := (hvalid (n + 2)).2
    rw [← hf (n + 2)] at hc
    have hn : n + 1 < (List.ofFn (fun i : Fin ((p 0).length + (n + 2)) => f i.val)).length := by
      rw [List.length_ofFn]; omega
    simpa only [List.getElem_ofFn, Fin.val_mk] using hc.getElem n hn

end Lemmatheca.SetTheory.WeakerChoice
