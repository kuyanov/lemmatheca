import Lemmatheca.FirstOrderProofFormulas.Classical

namespace Lemmatheca.Entry.FirstOrderProofFormulas
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder
universe u v w
variable {L : Language.{u,v}} {α : Type w} {n : ℕ}

/-- Distinct primitive full trees with the same classical expansion. -/
def conjunctionExample : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L α n := .conj .falsum .falsum

def expandedConjunctionExample : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L α n :=
  .neg (.impl .falsum (.neg .falsum))

theorem primitive_trees_distinct :
    conjunctionExample (L := L) (α := α) (n := n) ≠ expandedConjunctionExample := by
  intro h
  cases h

theorem classical_expansions_equal :
    (conjunctionExample (L := L) (α := α) (n := n)).toClassical =
      expandedConjunctionExample.toClassical := by
  rfl

/-- The one-slot body used in the free-replacement/opening example. -/
def captureBody (R : L.Relations 2) (x : α) : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L α 1 :=
  .all (.rel R (fun i => if i = 0 then .var (.inl x) else .var (.inr (0 : Fin 2))))

theorem captureBody_calculation (R : L.Relations 2) (x : α) (f : α → α) (t : L.Term α) :
    ((captureBody R x).rename f).instantiate t =
      .all (.rel R (fun i => if i = 0 then .var (.inl (f x)) else t.relabel Sum.inl)) := by
  simp [captureBody, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope, liftScope, scopeInclusion,
    Term.relabel]
  funext i
  by_cases h : i = 0
  · simp [h, Term.subst]
  · simp [h, Term.subst]
    rfl

/-- Opening an available outer slot shifts an internal binder without capture. -/
def openingBody (R : L.Relations 2) : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L α 1 :=
  .all (.rel R (fun i => .var (.inr (if i = 0 then (0 : Fin 2) else 1))))

theorem openingBody_calculation (R : L.Relations 2) (t : L.Term α) :
    (openingBody R).instantiate t =
      .all (.rel R (fun i => if i = 0 then t.relabel Sum.inl else .var (.inr 0))) := by
  simp [openingBody, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map, liftScope, scopeInclusion, Term.subst, Term.relabel]
  funext i
  by_cases h : i = 0 <;> simp [h] <;> rfl

/-- Quantifier and connective depth is independent of the term tree. -/
theorem quantified_depth (R : L.Relations 1) (f : L.Functions 1) :
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.all (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.disj
      (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rel R (fun _ => .func f (fun _ => .var (.inr (0 : Fin 1)))))
      (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.neg (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rel R (fun _ => .var (.inr (0 : Fin 1)))))) :
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L α 0).depth = 3 := by
  rfl

end Lemmatheca.Entry.FirstOrderProofFormulas
