import Mathlib.Tactic
import Mathlib.SetTheory.ZFC.Class

/-! Reusable AxiomaticSetTheory definitions and results. -/

set_option autoImplicit false

/-! Semantic instances of the set-construction axioms in mathlib's universe-relative
`ZFSet` realization. Predicates stand for formula instances with fixed parameters;
they do not encode first-order syntax or prove consistency, independence, or
derivability over ZF without Choice. The general Russell statement only assumes
the membership condition supplied by Separation. -/
namespace Lemmatheca.SetTheory.AxiomaticSetTheory
open scoped ZFSet
universe u

def IsInductive (I : ZFSet.{u}) : Prop :=
  ∅ ∈ I ∧ ∀ x ∈ I, insert x x ∈ I

def IsProperClass (P : ZFSet.{u} → Prop) : Prop :=
  ¬ ∃ A : ZFSet.{u}, ∀ x, x ∈ A ↔ P x

def russellPart (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => x ∉ x) A

theorem russell_not_mem {α : Type u} (M : α → α → Prop) (A R : α)
    (hR : ∀ x, M x R ↔ M x A ∧ ¬ M x x) : ¬ M R A := by
  intro h
  have hn : ¬ M R R := fun hr => (hR R).mp hr |>.2 hr
  exact hn ((hR R).mpr ⟨h, hn⟩)

theorem russellPart_not_mem (A : ZFSet.{u}) : russellPart A ∉ A := by
  apply russell_not_mem (fun x y : ZFSet.{u} => x ∈ y) A (russellPart A)
  intro x
  exact ZFSet.mem_sep

theorem universal_class_proper : IsProperClass (fun _ : ZFSet.{u} => True) := by
  rintro ⟨A, hA⟩
  exact russellPart_not_mem A ((hA _).mpr trivial)

theorem proper_class_not_represented (P : ZFSet.{u} → Prop) (hP : IsProperClass P)
    (A : ZFSet.{u}) : ¬ ∃ x ∈ A, ∀ y, y ∈ x ↔ P y := by
  rintro ⟨x, _, hx⟩
  exact hP ⟨x, hx⟩

theorem relative_intersection_empty (U : ZFSet.{u}) :
    ZFSet.sep (fun x => ∀ C ∈ (∅ : ZFSet.{u}), x ∈ C) U = U := by
  apply ZFSet.ext
  simp

theorem product_empty_cases (A : ZFSet.{u}) :
    ZFSet.prod ∅ A = ∅ ∧ ZFSet.prod A ∅ = ∅ := by
  constructor
  · apply ZFSet.ext
    intro z
    constructor
    · intro hz
      unfold ZFSet.prod ZFSet.pairSep at hz
      obtain ⟨a, ha, _, _, _, _⟩ := (ZFSet.mem_sep.mp hz).2
      exact (ZFSet.notMem_empty a ha).elim
    · intro hz
      exact (ZFSet.notMem_empty z hz).elim
  · apply ZFSet.ext
    intro z
    constructor
    · intro hz
      unfold ZFSet.prod ZFSet.pairSep at hz
      obtain ⟨_, _, b, hb, _, _⟩ := (ZFSet.mem_sep.mp hz).2
      exact (ZFSet.notMem_empty b hb).elim
    · intro hz
      exact (ZFSet.notMem_empty z hz).elim

theorem function_set_empty_cases (A B : ZFSet.{u}) :
    ZFSet.funs ∅ B = {∅} ∧ (A ≠ ∅ → ZFSet.funs A ∅ = ∅) := by
  have prod0 (X : ZFSet.{u}) : ZFSet.prod ∅ X = ∅ := (product_empty_cases X).1
  have prod0' (X : ZFSet.{u}) : ZFSet.prod X ∅ = ∅ := (product_empty_cases X).2
  constructor
  · apply ZFSet.ext
    intro f
    simp only [ZFSet.mem_funs, ZFSet.mem_singleton, ZFSet.IsFunc, prod0]
    constructor
    · rintro ⟨hf, _⟩
      exact le_antisymm hf (ZFSet.empty_subset _)
    · rintro rfl
      exact ⟨le_refl _, fun z hz => (ZFSet.notMem_empty z hz).elim⟩
  · intro hA
    apply ZFSet.ext
    intro f
    simp only [ZFSet.mem_funs, ZFSet.notMem_empty, iff_false, ZFSet.IsFunc, prod0']
    rintro ⟨hf, hg⟩
    have he : f = ∅ := le_antisymm hf (ZFSet.empty_subset _)
    apply hA
    apply (ZFSet.eq_empty A).mpr
    intro x hx
    obtain ⟨y, hy, _⟩ := hg x hx
    exact ZFSet.notMem_empty _ (he ▸ hy)

theorem replacement_unique_outputs (A : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (hR : ∀ x ∈ A, ∃! y, R x y) :
    ∃ B : ZFSet.{u}, ∀ y, y ∈ B ↔ ∃ x ∈ A, R x y := by
  classical
  let f (x : A) : ZFSet.{u} := (hR x.val x.property).choose
  have hf (x : A) : R x.val (f x) := (hR x.val x.property).choose_spec.1
  refine ⟨ZFSet.range f, fun y => ?_⟩
  simp only [ZFSet.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, x.property, hf x⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨⟨x, hx⟩, ((hR x hx).choose_spec.2 y hy).symm⟩

theorem replacement_restricted_graph (A : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) (hR : ∀ x ∈ A, ∃! y, R x y) :
    ∃ G : ZFSet.{u}, ∀ z, z ∈ G ↔ ∃ x ∈ A, ∃ y, R x y ∧ z = ZFSet.pair x y := by
  classical
  let f (x : A) : ZFSet.{u} := (hR x.val x.property).choose
  have hf (x : A) : R x.val (f x) := (hR x.val x.property).choose_spec.1
  refine ⟨ZFSet.range (fun x : A => ZFSet.pair x.val (f x)), fun z => ?_⟩
  simp only [ZFSet.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, x.property, f x, hf x, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [(hR x hx).choose_spec.2 y hy]

theorem family_choice_graph (A : ZFSet.{u}) (hA : ∀ x ∈ A, x.Nonempty) :
    ∃ G : ZFSet.{u}, ZFSet.IsFunc A (ZFSet.sUnion A) G ∧
      ∀ x ∈ A, ∃ y ∈ x, ZFSet.pair x y ∈ G := by
  classical
  let f (x : A) : ZFSet.{u} := (hA x.val x.property).choose
  have hf (x : A) : f x ∈ x.val := (hA x.val x.property).choose_spec
  let G := ZFSet.range (fun x : A => ZFSet.pair x.val (f x))
  refine ⟨G, ⟨?_, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨x, rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.pair_mem_prod.mpr ⟨x.property, ZFSet.mem_sUnion_of_mem (hf x) x.property⟩
  · intro x hx
    refine ⟨f ⟨x,hx⟩, ZFSet.mem_range_self (f := fun w : A => ZFSet.pair w.val (f w)) ⟨x,hx⟩, ?_⟩
    intro y hy
    obtain ⟨w, hw⟩ := ZFSet.mem_range.mp hy
    obtain ⟨hwy, hxy⟩ := ZFSet.pair_inj.mp hw
    have he : w = ⟨x,hx⟩ := Subtype.ext hwy
    simpa [he] using hxy.symm
  · intro x hx
    exact ⟨f ⟨x,hx⟩, hf ⟨x,hx⟩, ZFSet.mem_range_self (f := fun w : A => ZFSet.pair w.val (f w)) ⟨x,hx⟩⟩

theorem family_powersets_bounded (A : ZFSet.{u}) :
    let B := ZFSet.range (fun x : A => ZFSet.powerset x.val)
    (∀ y, y ∈ B ↔ ∃ x ∈ A, ZFSet.powerset x = y) ∧
      B ⊆ ZFSet.powerset (ZFSet.powerset (ZFSet.sUnion A)) ∧
      (A = ∅ → B = ∅) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro y
    simp only [ZFSet.mem_range]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.val, x.property, hx⟩
    · rintro ⟨x,hx,he⟩
      exact ⟨⟨x,hx⟩,he⟩
  · intro y hy
    obtain ⟨x,rfl⟩ := ZFSet.mem_range.mp hy
    rw [ZFSet.mem_powerset]
    intro z hz
    rw [ZFSet.mem_powerset] at hz ⊢
    exact fun a ha => ZFSet.mem_sUnion_of_mem (hz ha) x.property
  · intro h
    apply ZFSet.ext
    intro y
    simp only [ZFSet.mem_range, ZFSet.notMem_empty, iff_false, not_exists]
    intro x
    exact (ZFSet.notMem_empty x.val (h ▸ x.property)).elim

end Lemmatheca.SetTheory.AxiomaticSetTheory
