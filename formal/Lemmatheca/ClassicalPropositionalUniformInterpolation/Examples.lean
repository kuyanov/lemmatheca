import Lemmatheca.ClassicalPropositionalUniformInterpolation.Factors

namespace Lemmatheca.ProofTheory.ClassicalPropositional.UniformInterpolation

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u
variable {α : Type u} [DecidableEq α]

/-- Both Boolean projections of the displayed implication chain. -/
theorem implication_chain (p q r : α) (hpq : p ≠ q) (hqr : q ≠ r) (_hpr : p ≠ r) :
    SemEquivalent (existsAtom q (conj (impl (atom p) (atom q)) (impl (atom q) (atom r))))
      (impl (atom p) (atom r)) ∧
    SemEquivalent (forallAtom q (conj (impl (atom p) (atom q)) (impl (atom q) (atom r))))
      (conj (neg (atom p)) (atom r)) := by
  constructor <;> intro v <;>
    simp [existsAtom, forallAtom, constantInstance, subst, hpq, Ne.symm hqr, eval, verum]

/-- Resolving the two chain clauses has precisely the claimed remaining literals. -/
theorem chain_resolvent (p q r : α) (_hpq : p ≠ q) (_hqr : q ≠ r) :
    Resolution.resolvent q {Resolution.neg p, Resolution.pos q}
      {Resolution.neg q, Resolution.pos r} = {Resolution.neg p, Resolution.pos r} := by
  ext l
  rcases l with ⟨a, b⟩
  cases b <;> simp [Resolution.resolvent, Resolution.pos, Resolution.neg]

/-- A fresh concluding atom is permitted by the exact uniformity condition. -/
theorem fresh_conclusion (p q r : α) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :
    SemEquivalent (existsAtom q (conj (atom p) (atom q))) (atom p) ∧
      atoms (disj (atom p) (atom r)) ∩ atoms (conj (atom p) (atom q)) = {p} ∧
      Entails {conj (atom p) (atom q)} (disj (atom p) (atom r)) ∧
      Entails {existsAtom q (conj (atom p) (atom q))} (disj (atom p) (atom r)) := by
  have hf : SemEquivalent (existsAtom q (conj (atom p) (atom q))) (atom p) := by
    intro v
    simp [existsAtom, constantInstance, subst, hpq, eval, verum]
  refine ⟨hf, ?_, ?_, ?_⟩
  · ext a
    simp only [atoms, Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
    aesop
  · intro v hv
    have hA := hv _ (Finset.mem_singleton_self _)
    change eval v (conj (atom p) (atom q)) = true at hA
    exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.and_eq_true_iff.mp hA).1)
  · intro v hv
    have hE := hv _ (Finset.mem_singleton_self _)
    change eval v (existsAtom q (conj (atom p) (atom q))) = true at hE
    have hp : eval v (atom p) = true := (hf v) ▸ hE
    exact Bool.or_eq_true_iff.mpr (Or.inl hp)

/-- Complete existential forgetting has constant truth exactly when the source is satisfiable. -/
theorem complete_existential (L : List α) (A : PropFormula α) (h : atoms A ⊆ L.toFinset)
    (v : Valuation α) :
    eval v (existsList L A) = true ↔ ∃ w : Valuation α, eval w A = true := by
  rw [existsList_projection]
  constructor
  · rintro ⟨w, hw, _⟩
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    let u : Valuation α := fun q => if q ∈ atoms A then w q else v q
    refine ⟨u, ?_, ?_⟩
    · have he : eval u A = eval w A := eval_congr A u w (fun q hq => by simp [u, hq])
      exact he.symm ▸ hw
    · intro q hq
      have hn : q ∉ atoms A := fun hm => hq (h hm)
      simp [u, hn]

/-- Complete universal forgetting has constant truth exactly when the source is valid. -/
theorem complete_universal (L : List α) (A : PropFormula α) (h : atoms A ⊆ L.toFinset)
    (v : Valuation α) :
    eval v (forallList L A) = true ↔ Tautology A := by
  rw [forallList_projection]
  constructor
  · intro hall w
    let u : Valuation α := fun q => if q ∈ atoms A then w q else v q
    have ha : AgreeOutside L.toFinset u v := by
      intro q hq
      have hn : q ∉ atoms A := fun hm => hq (h hm)
      simp [u, hn]
    have hu := hall u ha
    have he : eval u A = eval w A := eval_congr A u w (fun q hq => by simp [u, hq])
    change eval w A = true
    exact he ▸ hu
  · intro hall w _
    exact hall w

/-- The two simple Craig factors need not retain all consequences on the full vocabulary. -/
theorem craig_not_uniform (p q : α) (hpq : p ≠ q) :
    Entails {conj (atom p) (atom q)} (atom p) ∧
      Entails {atom p} (disj (atom p) (atom q)) ∧
      Entails {conj (atom p) (atom q)} (atom q) ∧
      Entails {atom q} (disj (atom p) (atom q)) ∧
      ¬ Uniform (conj (atom p) (atom q)) {p, q} (atom p) ∧
      ¬ Uniform (conj (atom p) (atom q)) {p, q} (atom q) ∧
      Uniform (conj (atom p) (atom q)) {p, q} (existsList [] (conj (atom p) (atom q))) := by
  have hAp : Entails {conj (atom p) (atom q)} (atom p) := by
    intro v hv
    exact (Bool.and_eq_true_iff.mp (hv _ (Finset.mem_singleton_self _))).1
  have hAq : Entails {conj (atom p) (atom q)} (atom q) := by
    intro v hv
    exact (Bool.and_eq_true_iff.mp (hv _ (Finset.mem_singleton_self _))).2
  have hpB : Entails {atom p} (disj (atom p) (atom q)) := by
    intro v hv
    exact Bool.or_eq_true_iff.mpr (Or.inl (hv _ (Finset.mem_singleton_self _)))
  have hqB : Entails {atom q} (disj (atom p) (atom q)) := by
    intro v hv
    exact Bool.or_eq_true_iff.mpr (Or.inr (hv _ (Finset.mem_singleton_self _)))
  have hnPQ : ¬ Entails {atom p} (atom q) := by
    intro hpq'
    have hh := hpq' (Function.update (fun _ => false) p true) (by
      simp [SatisfiesContext, Satisfies, eval])
    simp [Satisfies, eval, Function.update_of_ne (Ne.symm hpq)] at hh
  have hnQP : ¬ Entails {atom q} (atom p) := by
    intro hqp'
    have hh := hqp' (Function.update (fun _ => false) q true) (by
      simp [SatisfiesContext, Satisfies, eval])
    simp [Satisfies, eval, Function.update_of_ne hpq] at hh
  refine ⟨hAp, hpB, hAq, hqB, ?_, ?_, ?_⟩
  · intro hu
    exact hnPQ (hu.2.2 (atom q) (by simp [atoms]) hAq)
  · intro hu
    apply hnQP
    apply hu.2.2 (atom p) _ hAp
    intro a ha
    have he : a = p := by simpa [atoms] using (Finset.mem_inter.mp ha).1
    simp [he]
  · apply uniform_interpolant
    · simp [atoms]
    · simp [atoms]

end Lemmatheca.ProofTheory.ClassicalPropositional.UniformInterpolation
