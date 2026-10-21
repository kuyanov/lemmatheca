import Lemmatheca.PartialRecursiveFunctions.PartialRecursiveFunctions

namespace Lemmatheca.Entry.PartialRecursiveFunctions

open Lemmatheca.ComputabilityTheory.PartialRecursiveFunctions

def inverseDouble : PFunction 1 :=
  minimize (lift (fun x : Args 2 => (2 * x.get 1 - x.get 0) + (x.get 0 - 2 * x.get 1)))

theorem inverseDouble_recursive : Recursive inverseDouble := by
  have hx : @Nat.Primrec' 2 (fun v => v.get 0) := Nat.Primrec'.get 0
  have hy : @Nat.Primrec' 2 (fun v => v.get 1) := Nat.Primrec'.get 1
  have hd := Nat.Primrec'.mul.comp₂ _ (Nat.Primrec'.const 2) hy
  exact Recursive.search (primitive_recursive_inclusion
    (Nat.Primrec'.add.comp₂ _ (Nat.Primrec'.sub.comp₂ _ hd hx)
      (Nat.Primrec'.sub.comp₂ _ hx hd))).1

theorem inverseDouble_spec (x y : ℕ) :
    y ∈ inverseDouble (List.Vector.ofFn (fun _ => x)) ↔ x = 2 * y := by
  rw [inverseDouble, minimize_spec]
  simp only [lift, Part.mem_some_iff]
  change (0 = (2 * y - x) + (x - 2 * y) ∧
    ∀ i < y, ∃ a, 0 < a ∧ a = (2 * i - x) + (x - 2 * i)) ↔ x = 2 * y
  constructor
  · intro h
    omega
  · intro h
    refine ⟨by omega, ?_⟩
    intro i hi
    refine ⟨(2 * i - x) + (x - 2 * i), ?_, rfl⟩
    omega

theorem inverseDouble_examples :
    0 ∈ inverseDouble (List.Vector.ofFn (fun _ => 0)) ∧
    3 ∈ inverseDouble (List.Vector.ofFn (fun _ => 6)) ∧
    ¬ (inverseDouble (List.Vector.ofFn (fun _ => 3))).Dom := by
  refine ⟨(inverseDouble_spec 0 0).mpr rfl, (inverseDouble_spec 6 3).mpr rfl, ?_⟩
  intro hd
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
  have h := (inverseDouble_spec 3 y).mp hy
  omega

noncomputable def blockedQ : PFunction 1 :=
  predicateSearch (fun x : Args 2 => x.get 0 = 1)

theorem blockedQ_recursive : Recursive blockedQ := by
  classical
  apply predicateSearch_recursive
  apply Nat.Primrec'.prim_iff.mpr
  have hp : PrimrecPred (fun x : Args 2 => x.get 0 = 1) :=
    Primrec.eq.comp (Primrec.vector_get.comp Primrec.id (Primrec.const 0)) (Primrec.const 1)
  apply (Primrec.ite hp (Primrec.const 1) (Primrec.const 0)).of_eq
  intro v
  by_cases hv : v.get 0 = 1 <;> simp [characteristic, hv]

theorem blockedQ_spec (x y : ℕ) :
    y ∈ blockedQ (List.Vector.ofFn (fun _ => x)) ↔ x = 1 ∧ y = 0 := by
  rw [blockedQ, predicateSearch_spec]
  change (x = 1 ∧ ∀ i < y, ¬ x = 1) ↔ x = 1 ∧ y = 0
  constructor
  · rintro ⟨hx, hi⟩
    refine ⟨hx, ?_⟩
    by_contra hy
    exact hi 0 (Nat.pos_of_ne_zero hy) hx
  · rintro ⟨hx, rfl⟩
    simp [hx]

theorem blockedQ_search :
    minimize blockedQ List.Vector.nil = Part.none := by
  apply blocked_zero_search
  intro hd
  obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp hd
  have he : snoc (List.Vector.nil : Args 0) 0 = List.Vector.ofFn (fun _ : Fin 1 => 0) := by
    apply List.Vector.ext
    intro i
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    simp [snoc, Fin.snoc]
  rw [he] at ha
  have h := (blockedQ_spec 0 a).mp ha
  omega

theorem bound_can_miss_later_witness (b c : ℕ) (hbc : b ≤ c) :
    let P : Args 1 → Prop := fun x => x.get 0 = c
    boundedPredicateSearch P List.Vector.nil b = b ∧
      c ∈ predicateSearch P List.Vector.nil := by
  dsimp only
  refine ⟨bounded_failure _ _ _ ?_, (predicateSearch_spec _ _ _).mpr ?_⟩
  · intro i hi
    change ¬ i = c
    omega
  · change c = c ∧ ∀ i < c, ¬ i = c
    exact ⟨rfl, fun i hi he => by omega⟩

theorem always_false_search (b : ℕ) :
    boundedPredicateSearch (fun _ : Args 1 => False) List.Vector.nil b = b ∧
      predicateSearch (fun _ : Args 1 => False) List.Vector.nil = Part.none := by
  refine ⟨bounded_failure _ _ _ (by simp), Part.eq_none_iff'.mpr ?_⟩
  rw [predicateSearch_domain]
  simp

theorem least_input_example :
    minimize (lift (fun x : Args 1 => 3 - x.get 0)) List.Vector.nil = Part.some 3 := by
  apply Part.eq_some_iff.mpr
  rw [minimize_spec]
  simp only [lift, Part.mem_some_iff]
  change 0 = 3 - 3 ∧ ∀ i < 3, ∃ a, 0 < a ∧ a = 3 - i
  exact ⟨rfl, fun i hi => ⟨3 - i, by omega, rfl⟩⟩

end Lemmatheca.Entry.PartialRecursiveFunctions
