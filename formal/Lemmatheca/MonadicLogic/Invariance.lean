import Lemmatheca.MonadicLogic.Syntax

namespace Lemmatheca.MathematicalLogic.MonadicLogic
open FirstOrder FirstOrder.Language Structure

section Generic
variable {M N P : Type*} {π : M → P} {ρ : N → P}

/-- The specified map between used values sends each old coordinate to its partner. -/
theorem assignment_bijection {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hmatch : Matching π ρ a b) :
    ∃ e : Set.range a ≃ Set.range b,
      (∀ i, e ⟨a i, Set.mem_range_self i⟩ = ⟨b i, Set.mem_range_self i⟩) ∧
        ∀ x : Set.range a, π x.val = ρ (e x).val := by
  classical
  let f : Set.range a → Set.range b := fun x =>
    ⟨b (Classical.choose x.property), Set.mem_range_self _⟩
  have hf : ∀ i, f ⟨a i, Set.mem_range_self i⟩ = ⟨b i, Set.mem_range_self i⟩ := by
    intro i
    apply Subtype.ext
    exact (hmatch.2 _ i).mp (Classical.choose_spec (Set.mem_range_self i))
  have hfi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have h := (hmatch.2 (Classical.choose x.property) (Classical.choose y.property)).mpr
      (congrArg Subtype.val hxy)
    simpa only [Classical.choose_spec x.property, Classical.choose_spec y.property] using h
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨i,hi⟩ := y.property
    refine ⟨⟨a i, Set.mem_range_self i⟩, ?_⟩
    rw [hf]
    exact Subtype.ext hi
  refine ⟨Equiv.ofBijective f ⟨hfi,hfs⟩, hf, ?_⟩
  intro x
  change π x.val = ρ (b (Classical.choose x.property))
  exact (congrArg π (Classical.choose_spec x.property)).symm.trans (hmatch.1 _)

private theorem matching_symm {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : Matching π ρ a b) : Matching ρ π b a :=
  ⟨fun i => (h.1 i).symm, fun i j => (h.2 i j).symm⟩

private theorem capacities_symm {r : ℕ} (h : Capacities r π ρ) : Capacities r ρ π := by
  intro p
  rcases h p with ⟨A,B,hA,hB,hcard,hlt⟩ | hlarge
  · exact Or.inl ⟨B,A,hB,hA,hcard.symm,by omega⟩
  · exact Or.inr hlarge.symm

private noncomputable def used {n : ℕ} (π : M → P) (p : P) (a : Fin n → M) : Finset M := by
  classical
  exact (Finset.univ.image a).filter (fun x => π x = p)

private theorem mem_used {n : ℕ} (p : P) (a : Fin n → M) (x : M) :
    x ∈ used π p a ↔ (∃ i, a i = x) ∧ π x = p := by
  classical
  simp [used]

private theorem used_card_le {n : ℕ} (p : P) (a : Fin n → M) :
    (used π p a).card ≤ n := by
  classical
  exact (Finset.card_filter_le _ _).trans (by simpa using Finset.card_image_le (s := Finset.univ) (f := a))

private theorem used_card_eq {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hmatch : Matching π ρ a b) (p : P) : (used π p a).card = (used ρ p b).card := by
  classical
  obtain ⟨e,_,he⟩ := assignment_bijection hmatch
  let f : (x : M) → x ∈ used π p a → N := fun x hx =>
    (e ⟨x, ((mem_used p a x).mp hx).1⟩).val
  apply Finset.card_bij f
  · intro x hx
    let x' : Set.range a := ⟨x, ((mem_used p a x).mp hx).1⟩
    apply (mem_used p b _).mpr
    exact ⟨(e x').property, (he x').symm.trans ((mem_used p a x).mp hx).2⟩
  · intro x hx y hy hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext hxy))
  · intro y hy
    let y' : Set.range b := ⟨y, ((mem_used p b y).mp hy).1⟩
    let x' := e.symm y'
    have hx : x'.val ∈ used π p a := by
      apply (mem_used p a _).mpr
      refine ⟨x'.property, ?_⟩
      have hp := he x'
      rw [e.apply_symm_apply] at hp
      exact hp.trans ((mem_used p b y).mp hy).2
    refine ⟨x'.val,hx,?_⟩
    change (e x').val = y
    rw [e.apply_symm_apply]

private theorem matching_snoc {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : Matching π ρ a b) {x : M} {y : N} (hp : π x = ρ y)
    (he : ∀ i, x = a i ↔ y = b i) : Matching π ρ (Fin.snoc a x) (Fin.snoc b y) := by
  constructor
  · intro i
    exact Fin.lastCases (by simpa using hp) (fun j => by simpa using h.1 j) i
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simpa using he j
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [Fin.snoc_castSucc, Fin.snoc_last, eq_comm] using he i
      · simpa using h.2 i j

private theorem extension_forward {r n : ℕ} (hcap : Capacities r π ρ)
    {a : Fin n → M} {b : Fin n → N} (hmatch : Matching π ρ a b) (hn : n < r) (x : M) :
    ∃ y : N, Matching π ρ (Fin.snoc a x) (Fin.snoc b y) := by
  classical
  by_cases hx : ∃ i, a i = x
  · obtain ⟨i,rfl⟩ := hx
    exact ⟨b i, matching_snoc hmatch (hmatch.1 i) (fun j => hmatch.2 i j)⟩
  have hxfresh : ∀ i, x ≠ a i := by simpa only [not_exists, ne_eq, eq_comm] using hx
  obtain ⟨y,hy,hyp⟩ : ∃ y, (∀ i, y ≠ b i) ∧ ρ y = π x := by
    rcases hcap (π x) with ⟨A,B,hA,hB,hcard,hlt⟩ | ⟨_,B,hBc,hBp⟩
    · have hsub : used π (π x) a ⊆ A := by
        intro z hz
        exact (hA z).mp ((mem_used _ _ _).mp hz).2
      have hxA : x ∈ A := (hA x).mp rfl
      have hxnot : x ∉ used π (π x) a := by simp [mem_used, hx]
      have hstrict : used π (π x) a ⊂ A := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩
        intro he
        exact hxnot (he.symm ▸ hxA)
      have hless : (used ρ (π x) b).card < B.card := by
        rw [← used_card_eq hmatch, ← hcard]
        exact Finset.card_lt_card hstrict
      obtain ⟨y,hyB,hyused⟩ := Finset.exists_mem_notMem_of_card_lt_card hless
      have hyp : ρ y = π x := (hB y).mpr hyB
      refine ⟨y,?_,hyp⟩
      intro i he
      exact hyused ((mem_used _ _ _).mpr ⟨⟨i,he.symm⟩,hyp⟩)
    · have hless : (used ρ (π x) b).card < B.card := by
        rw [hBc]
        exact (used_card_le _ _).trans_lt hn
      obtain ⟨y,hyB,hyused⟩ := Finset.exists_mem_notMem_of_card_lt_card hless
      have hyp := hBp y hyB
      refine ⟨y,?_,hyp⟩
      intro i he
      exact hyused ((mem_used _ _ _).mpr ⟨⟨i,he.symm⟩,hyp⟩)
  exact ⟨y,matching_snoc hmatch hyp.symm (fun i => by simp [hxfresh i,hy i])⟩

/-- A matching finite assignment extends in either direction, preserving all old comparisons. -/
theorem witness_extension {r n : ℕ} (hcap : Capacities r π ρ)
    {a : Fin n → M} {b : Fin n → N} (hmatch : Matching π ρ a b) (hn : n < r) :
    (∀ x : M, ∃ y : N, Matching π ρ (Fin.snoc a x) (Fin.snoc b y)) ∧
      (∀ y : N, ∃ x : M, Matching π ρ (Fin.snoc a x) (Fin.snoc b y)) := by
  refine ⟨extension_forward hcap hmatch hn, ?_⟩
  intro y
  obtain ⟨x,hx⟩ := extension_forward (capacities_symm hcap) (matching_symm hmatch) hn y
  exact ⟨x,matching_symm hx⟩

end Generic

private def termSlot {k n : ℕ} : (lang k).Term (Empty ⊕ Fin n) → Fin n
  | .var (.inl e) => e.elim
  | .var (.inr i) => i
  | .func (.constant i) _ => i.elim0

private theorem realize_termSlot {k n : ℕ} {M : Type*} [(lang k).Structure M]
    (t : (lang k).Term (Empty ⊕ Fin n)) (a : Fin n → M) :
    t.realize (Sum.elim Empty.elim a) = a (termSlot t) := by
  cases t with
  | var i => cases i with | inl e => exact e.elim | inr i => rfl
  | func f ts => cases f with | constant i => exact i.elim0

private theorem atom_relation_invariance {k n : ℕ} {M N : Type*}
    [(lang k).Structure M] [(lang k).Structure N]
    (a : Fin n → M) (b : Fin n → N)
    (hmatch : Matching (profile (k := k)) (profile (k := k)) a b)
    {l : ℕ} (r : (lang k).Relations l) (ts : Fin l → (lang k).Term (Empty ⊕ Fin n)) :
    (BoundedFormula.rel r ts).Realize Empty.elim a ↔
      (BoundedFormula.rel r ts).Realize Empty.elim b := by
  rcases r with ⟨i,hi⟩
  have hl : l = 1 := by simpa [arities] using hi.symm
  cases hl
  let j : Fin k := ⟨i.val,by simpa [arities] using i.isLt⟩
  have hr : (⟨i,hi⟩ : (lang k).Relations 1) = predicate k j := Subtype.ext (Fin.ext rfl)
  rw [hr]
  change RelMap (predicate k j) (fun z => (ts z).realize (Sum.elim Empty.elim a)) ↔
    RelMap (predicate k j) (fun z => (ts z).realize (Sum.elim Empty.elim b))
  have ha : (fun z => (ts z).realize (Sum.elim Empty.elim a)) =
      (fun _ => a (termSlot (ts 0))) := by
    funext z
    have hz : z = 0 := Subsingleton.elim _ _
    subst z
    exact realize_termSlot _ _
  have hb : (fun z => (ts z).realize (Sum.elim Empty.elim b)) =
      (fun _ => b (termSlot (ts 0))) := by
    funext z
    have hz : z = 0 := Subsingleton.elim _ _
    subst z
    exact realize_termSlot _ _
  rw [ha,hb]
  have hbits := congrFun (hmatch.1 (termSlot (ts 0))) j
  have htrue := congrArg (fun z : Bool => z = true) hbits
  simpa only [profile, decide_eq_true_eq] using Iff.of_eq htrue

theorem truth_invariance {k : ℕ} {M N : Type*} [(lang k).Structure M] [(lang k).Structure N]
    {r n : ℕ} (hcap : Capacities r (profile (k := k) (M := M)) (profile (k := k) (M := N)))
    (φ : (lang k).BoundedFormula Empty n) (a : Fin n → M) (b : Fin n → N)
    (hmatch : Matching (profile (k := k)) (profile (k := k)) a b) (hbudget : n + quantifiers φ ≤ r) :
    φ.Realize Empty.elim a ↔ φ.Realize Empty.elim b := by
  revert a b
  induction φ with
  | falsum => intro a b _; simp [BoundedFormula.Realize]
  | equal t u =>
    intro a b hmatch
    simpa only [BoundedFormula.Realize, realize_termSlot] using hmatch.2 (termSlot t) (termSlot u)
  | rel r ts =>
    intro a b hmatch
    exact atom_relation_invariance a b hmatch r ts
  | imp φ ψ ihφ ihψ =>
    intro a b hmatch
    have hp := ihφ (by simp only [quantifiers] at hbudget; omega) a b hmatch
    have hq := ihψ (by simp only [quantifiers] at hbudget; omega) a b hmatch
    exact imp_congr hp hq
  | @all n φ ih =>
    intro a b hmatch
    have hn : n < r := by simp only [quantifiers] at hbudget; omega
    have hbudget' : n + 1 + quantifiers φ ≤ r := by simp only [quantifiers] at hbudget; omega
    change (∀ x : M, φ.Realize Empty.elim (Fin.snoc a x)) ↔
      ∀ y : N, φ.Realize Empty.elim (Fin.snoc b y)
    constructor
    · intro h y
      obtain ⟨x,hxy⟩ := (witness_extension hcap hmatch hn).2 y
      exact (ih hbudget' _ _ hxy).mp (h x)
    · intro h x
      obtain ⟨y,hxy⟩ := (witness_extension hcap hmatch hn).1 x
      exact (ih hbudget' _ _ hxy).mpr (h y)

end Lemmatheca.MathematicalLogic.MonadicLogic
