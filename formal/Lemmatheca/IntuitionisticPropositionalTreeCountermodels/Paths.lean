import Lemmatheca.IntuitionisticPropositionalKripkeMorphisms.Morphisms
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Fintype.List
import Mathlib.Data.Fintype.Card

namespace Lemmatheca.ProofTheory.Intuitionistic.Kripke

universe v

/-- Finiteness, a specified least root, and comparable predecessor histories. -/
def IsFiniteRootedTree {T : Type v} [PartialOrder T] (o : T) : Prop :=
  Finite T ∧ (∀ p : T, o ≤ p) ∧
    ∀ p q s : T, p ≤ s → q ≤ s → p ≤ q ∨ q ≤ p

namespace StrictPaths

variable {W : Type v} [PartialOrder W]

/-- The actual list starts at the supplied root and is pairwise strictly increasing. -/
def IsPath (r : W) (p : List W) : Prop :=
  p.head? = some r ∧ p.Pairwise (· < ·)

/-- A proof record prevents the ambient list's lexicographic order from being inherited. -/
structure Path (r : W) where
  val : List W
  property : IsPath r val

/-- Prefix is the actual relation on the underlying lists. -/
instance pathPartialOrder (r : W) : PartialOrder (Path r) where
  le p q := p.val.IsPrefix q.val
  lt p q := p.val.IsPrefix q.val ∧ ¬ q.val.IsPrefix p.val
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl _ := List.prefix_rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm p q h₁ h₂ := by
    have h : p.val = q.val := h₁.eq_of_length (h₁.length_le.antisymm h₂.length_le)
    cases p
    cases q
    cases h
    rfl

def root (r : W) : Path r := ⟨[r], by simp [IsPath]⟩

instance pathNonempty (r : W) : Nonempty (Path r) := ⟨root r⟩

private theorem path_ne_nil {r : W} (p : Path r) : p.val ≠ [] := by
  intro h
  have hs := p.property.1
  simp [h] at hs

/-- The endpoint is the last entry of the same nonempty list. -/
def last {r : W} (p : Path r) : W := p.val.getLast (path_ne_nil p)

theorem last_root (r : W) : last (root r) = r := by rfl

theorem path_nodup {r : W} (p : Path r) : p.val.Nodup := by
  exact p.property.2.nodup

theorem Path.ext_val {r : W} {p q : Path r} (h : p.val = q.val) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem finite_paths [Finite W] (r : W) : Finite (Path r) := by
  classical
  let : Fintype W := Fintype.ofFinite W
  apply Finite.of_injective (fun p : Path r => (⟨p.val, path_nodup p⟩ : {l : List W // l.Nodup}))
  intro p q h
  exact Path.ext_val (congrArg Subtype.val h)

instance pathFinite [Finite W] (r : W) : Finite (Path r) := finite_paths r

noncomputable instance pathFintype [Finite W] (r : W) : Fintype (Path r) :=
  Fintype.ofFinite _

theorem root_le {r : W} (p : Path r) : root r ≤ p := by
  change [r].IsPrefix p.val
  cases hp : p.val with
  | nil => exact (path_ne_nil p hp).elim
  | cons a t =>
      have ha : a = r := by simpa only [hp, List.head?_cons, Option.some.injEq] using p.property.1
      exact ⟨t, by simp only [List.singleton_append, ha]⟩

theorem predecessors_compare {r : W} (p q s : Path r)
    (hp : p ≤ s) (hq : q ≤ s) : p ≤ q ∨ q ≤ p := by
  rcases le_total p.val.length q.val.length with h | h
  · exact Or.inl (List.prefix_of_prefix_length_le hp hq h)
  · exact Or.inr (List.prefix_of_prefix_length_le hq hp h)

private theorem mem_le_last {r : W} (p : Path r) {x : W} (hx : x ∈ p.val) : x ≤ last p := by
  have hweak : p.val.Pairwise (· ≤ ·) :=
    List.Pairwise.imp (fun h => le_of_lt h) p.property.2
  exact hweak.rel_getLast hx

theorem first_le_last {r : W} (p : Path r) : r ≤ last p := by
  exact mem_le_last p (List.mem_of_mem_head? (by simp only [p.property.1, Option.mem_some_iff]))

theorem last_monotone (r : W) : Monotone (last : Path r → W) := by
  intro p q hpq
  exact mem_le_last q (hpq.sublist.subset (List.getLast_mem (path_ne_nil p)))

/-- Appending this strictly later endpoint retains the exact path predicate. -/
private theorem append_path {r : W} (p : Path r) (x : W) (hx : last p < x) :
    IsPath r (p.val ++ [x]) := by
  constructor
  · cases hp : p.val with
    | nil => exact (path_ne_nil p hp).elim
    | cons a t => simpa only [hp, List.cons_append, List.head?_cons] using p.property.1
  · apply List.pairwise_append.mpr
    refine ⟨p.property.2, by simp, ?_⟩
    intro y hy z hz
    have hzx : z = x := by simpa only [List.mem_singleton] using hz
    subst z
    exact lt_of_le_of_lt (mem_le_last p hy) hx

/-- Equality uses the supplied path; otherwise the requested world is appended. -/
noncomputable def lift {r : W} (p : Path r) (x : W) (hx : last p ≤ x) : Path r := by
  classical
  exact if heq : last p = x then p
    else ⟨p.val ++ [x], append_path p x (lt_of_le_of_ne hx heq)⟩

theorem lift_spec {r : W} (p : Path r) (x : W) (hx : last p ≤ x) :
    p ≤ lift p x hx ∧ last (lift p x hx) = x := by
  classical
  by_cases heq : last p = x
  · simp only [lift, dite_eq_left heq]
    exact ⟨le_rfl, heq⟩
  · constructor
    · change p.val.IsPrefix (lift p x hx).val
      simp only [lift, dite_eq_right heq]
      exact List.prefix_append _ _
    · change (lift p x hx).val.getLast (path_ne_nil (lift p x hx)) = x
      simp only [lift, dite_eq_right heq]
      exact List.getLast_append_singleton _

theorem last_bounded (r : W) : IsBoundedFrameMap (last : Path r → W) := by
  refine ⟨last_monotone r, ?_⟩
  intro p x hx
  exact ⟨lift p x hx, (lift_spec p x hx).1, (lift_spec p x hx).2⟩

theorem last_range (r : W) : Set.range (last : Path r → W) = {x : W | r ≤ x} := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact first_le_last p
  · intro hx
    change r ≤ x at hx
    obtain ⟨p, _, hp⟩ := (last_bounded r).back (root r) x (by simpa only [last_root] using hx)
    exact ⟨p, hp⟩

theorem last_surjective_iff (r : W) :
    Function.Surjective (last : Path r → W) ↔ ∀ x : W, r ≤ x := by
  constructor
  · intro h x
    obtain ⟨p, rfl⟩ := h x
    exact first_le_last p
  · intro h x
    have hx : x ∈ Set.range (last : Path r → W) := by
      rw [last_range]
      exact h x
    exact hx

end StrictPaths
end Lemmatheca.ProofTheory.Intuitionistic.Kripke
