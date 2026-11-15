import Lemmatheca.ClassicalPropositionalUniformInterpolation.Syntax

namespace Lemmatheca.ProofTheory.ClassicalPropositional.UniformInterpolation

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u
variable {α : Type u} [DecidableEq α]

private theorem update_agrees (p : α) (v : Valuation α) (b : Bool) :
    AgreeOutside {p} (Function.update v p b) v := by
  intro q hq
  exact Function.update_of_ne (by simpa using hq) _ _

private theorem update_eq_of_agree (p : α) (v w : Valuation α)
    (h : AgreeOutside {p} w v) : Function.update v p (w p) = w := by
  funext q
  by_cases hq : q = p
  · subst q
    simp
  · rw [Function.update_of_ne hq]
    exact (h q (by simpa using hq)).symm

omit [DecidableEq α] in
private theorem agree_refl (F : Finset α) (v : Valuation α) : AgreeOutside F v v :=
  fun _ _ => rfl

/-- Single-atom projection preserves the values of all other atoms, not just source atoms. -/
theorem existsAtom_projection (p : α) (A : PropFormula α) (v : Valuation α) :
    eval v (existsAtom p A) = true ↔
      ∃ w : Valuation α, eval w A = true ∧ AgreeOutside {p} w v := by
  simp only [existsAtom, eval, Bool.or_eq_true_iff, constantInstance_eval]
  constructor
  · rintro (h | h)
    · exact ⟨Function.update v p false, h, update_agrees p v false⟩
    · exact ⟨Function.update v p true, h, update_agrees p v true⟩
  · rintro ⟨w, hw, hagree⟩
    have hu := update_eq_of_agree p v w hagree
    cases hb : w p
    · have hu' : Function.update v p false = w := by simpa only [hb] using hu
      exact Or.inl (by simpa only [hu'] using hw)
    · have hu' : Function.update v p true = w := by simpa only [hb] using hu
      exact Or.inr (by simpa only [hu'] using hw)

/-- The universal formula tests every extension of precisely the retained assignment. -/
theorem forallAtom_projection (p : α) (A : PropFormula α) (v : Valuation α) :
    eval v (forallAtom p A) = true ↔
      ∀ w : Valuation α, AgreeOutside {p} w v → eval w A = true := by
  simp only [forallAtom, eval, Bool.and_eq_true_iff, constantInstance_eval]
  constructor
  · intro h w hagree
    have hu := update_eq_of_agree p v w hagree
    cases hb : w p
    · have hu' : Function.update v p false = w := by simpa only [hb] using hu
      simpa only [hu'] using h.1
    · have hu' : Function.update v p true = w := by simpa only [hb] using hu
      simpa only [hu'] using h.2
  · intro h
    exact ⟨h _ (update_agrees p v false), h _ (update_agrees p v true)⟩

/-- The finite recursion has the full extension semantics, including repetitions. -/
theorem existsList_projection (L : List α) (A : PropFormula α) (v : Valuation α) :
    eval v (existsList L A) = true ↔
      ∃ w : Valuation α, eval w A = true ∧ AgreeOutside L.toFinset w v := by
  induction L generalizing v with
  | nil =>
    constructor
    · intro h
      exact ⟨v, h, agree_refl _ _⟩
    · rintro ⟨w, hw, hagree⟩
      have he : w = v := funext (fun q => hagree q (by simp))
      simpa only [he, existsList] using hw
  | cons p L ih =>
    rw [existsList, existsAtom_projection]
    constructor
    · rintro ⟨u, hu, huv⟩
      obtain ⟨w, hw, hwu⟩ := (ih u).mp hu
      refine ⟨w, hw, ?_⟩
      intro q hq
      have hL : q ∉ L.toFinset := by
        intro hm
        exact hq (by simp [hm])
      have hp : q ≠ p := by simpa using (fun hqp => hq (by simp [hqp]))
      exact (hwu q hL).trans (huv q (by simpa using hp))
    · rintro ⟨w, hw, hwv⟩
      refine ⟨Function.update v p (w p), (ih _).mpr ⟨w, hw, ?_⟩, update_agrees p v (w p)⟩
      intro q hq
      by_cases hqp : q = p
      · subst q
        simp
      · rw [Function.update_of_ne hqp]
        exact hwv q (by simp [hqp, hq])

/-- The universal recursion ranges over exactly the same retained assignments. -/
theorem forallList_projection (L : List α) (A : PropFormula α) (v : Valuation α) :
    eval v (forallList L A) = true ↔
      ∀ w : Valuation α, AgreeOutside L.toFinset w v → eval w A = true := by
  induction L generalizing v with
  | nil =>
    constructor
    · intro h w hagree
      have he : w = v := funext (fun q => hagree q (by simp))
      simpa only [he, forallList] using h
    · intro h
      exact h v (agree_refl _ _)
  | cons p L ih =>
    rw [forallList, forallAtom_projection]
    constructor
    · intro h w hwv
      apply (ih (Function.update v p (w p))).mp
        (h _ (update_agrees p v (w p))) w
      intro q hq
      by_cases hqp : q = p
      · subst q
        simp
      · rw [Function.update_of_ne hqp]
        exact hwv q (by simp [hqp, hq])
    · intro h u huv
      apply (ih u).mpr
      intro w hwu
      apply h w
      intro q hq
      have hL : q ∉ L.toFinset := by
        intro hm
        exact hq (by simp [hm])
      have hp : q ≠ p := by
        intro he
        exact hq (by simp [he])
      exact (hwu q hL).trans (huv q (by simpa using hp))

/-- Neither finite recursive construction introduces or retains a forgotten atom. -/
theorem list_support (L : List α) (A : PropFormula α) :
    atoms (existsList L A) ⊆ atoms A \ L.toFinset ∧
      atoms (forallList L A) ⊆ atoms A \ L.toFinset := by
  induction L with
  | nil => simp [existsList, forallList]
  | cons p L ih =>
    constructor
    · intro q hq
      have hh := Finset.mem_sdiff.mp ((atom_support p (existsList L A)).1 hq)
      have ht := Finset.mem_sdiff.mp (ih.1 hh.1)
      refine Finset.mem_sdiff.mpr ⟨ht.1, ?_⟩
      simp only [List.toFinset_cons, Finset.mem_insert, not_or]
      exact ⟨by simpa using hh.2, ht.2⟩
    · intro q hq
      have hh := Finset.mem_sdiff.mp ((atom_support p (forallList L A)).2 hq)
      have ht := Finset.mem_sdiff.mp (ih.2 hh.1)
      refine Finset.mem_sdiff.mpr ⟨ht.1, ?_⟩
      simp only [List.toFinset_cons, Finset.mem_insert, not_or]
      exact ⟨by simpa using hh.2, ht.2⟩

/-- Existential outputs with the same forgotten set are equivalent. -/
theorem existsList_set_congr (L K : List α) (A : PropFormula α)
    (h : L.toFinset = K.toFinset) : SemEquivalent (existsList L A) (existsList K A) := by
  intro v
  apply Bool.eq_iff_iff.mpr
  simp only [existsList_projection, h]

/-- Universal outputs with the same forgotten set are equivalent. -/
theorem forallList_set_congr (L K : List α) (A : PropFormula α)
    (h : L.toFinset = K.toFinset) : SemEquivalent (forallList L A) (forallList K A) := by
  intro v
  apply Bool.eq_iff_iff.mpr
  simp only [forallList_projection, h]

/-- Forgetting an atom absent from the source changes no Boolean meaning. -/
theorem absent_atom (p : α) (A : PropFormula α) (h : p ∉ atoms A) :
    SemEquivalent (existsAtom p A) A ∧ SemEquivalent (forallAtom p A) A := by
  have he (v w : Valuation α) (hw : AgreeOutside {p} w v) : eval w A = eval v A := by
    apply eval_congr
    intro q hq
    have hn : q ≠ p := by intro he; exact h (he ▸ hq)
    exact hw q (by simpa using hn)
  constructor
  · intro v
    apply Bool.eq_iff_iff.mpr
    rw [existsAtom_projection]
    constructor
    · rintro ⟨w, hw, hagree⟩
      exact (he v w hagree) ▸ hw
    · intro hv
      exact ⟨v, hv, agree_refl _ _⟩
  · intro v
    apply Bool.eq_iff_iff.mpr
    rw [forallAtom_projection]
    constructor
    · intro hall
      exact hall v (agree_refl _ _)
    · intro hv w hagree
      exact (he v w hagree).symm ▸ hv

/-- Existential and universal finite elimination are Boolean duals. -/
theorem universal_dual (L : List α) (A : PropFormula α) :
    SemEquivalent (forallList L A) (neg (existsList L (neg A))) := by
  intro v
  apply Bool.eq_iff_iff.mpr
  rw [forallList_projection]
  change _ ↔ Bool.not (eval v (existsList L (neg A))) = true
  rw [Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff]
  simp only [ne_eq]
  rw [existsList_projection]
  simp only [eval, Bool.not_eq_true_eq_eq_false]
  constructor
  · intro hall
    rintro ⟨w, hw, hagree⟩
    have ht := hall w hagree
    simp [hw] at ht
  · intro hn w hagree
    cases he : eval w A with
    | false => exact False.elim (hn ⟨w, he, hagree⟩)
    | true => rfl

end Lemmatheca.ProofTheory.ClassicalPropositional.UniformInterpolation
