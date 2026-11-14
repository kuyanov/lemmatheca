import Lemmatheca.EqualityFreeIntuitionisticFirstOrderHarropExtraction.Public
import Lemmatheca.EqualityFreeIntuitionisticFirstOrderSequents.Examples

/-! The exact retained universal/implication witness and both termless contexts. -/
namespace Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderHarropExtraction
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.IntuitionisticFirstOrder
open Lemmatheca.ProofTheory.IntuitionisticFirstOrder.EqualityFreeHarrop
abbrev Formula := Lemmatheca.ProofTheory.FirstOrder.Formula
abbrev BF := Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifohExamplesEq {K : Language.{u,v}} {δ : Type w} :
    DecidableEq (Formula K δ) := Classical.decEq _

theorem quantified_grammar_example (P Q : L.Relations 1) :
    IsHarrop (.all (.impl
      (.ex (.rel P (fun _ => .var (.inr (1 : Fin 2)))))
      (.rel Q (fun _ => .var (.inr (0 : Fin 1))))) : Formula L α) := by
  simp [IsHarrop, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.EqualityFree]

theorem arbitrary_input_example {k : ℕ} (B : BF L α 1) (Q : Formula L α)
    (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin 0))
    (hB : B.EqualityFree) (hQ : Q.EqualityFree) :
    IsHarrop (.impl (.disj (.ex B) Q) (.rel R ts)) ∧
      ¬ IsHarrop (.disj (.ex B) Q) := by
  simp [IsHarrop, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.EqualityFree, hB, hQ]

def predicateAt (R : L.Relations 1) (c : L.Term α) : Formula L α :=
  .rel R (fun _ => c.relabel Sum.inl)

def predicateBody (R : L.Relations 1) : BF L α 1 :=
  .rel R (fun _ => .var (.inr 0))

def universalImplication (P Q : L.Relations 1) : Formula L α :=
  .all (.impl (predicateBody P) (predicateBody Q))

def workedContext (P Q : L.Relations 1) (c : L.Term α) : Context L α :=
  {universalImplication P Q, predicateAt P c}

def workedDelta (P Q : L.Relations 1) (c : L.Term α) : Context L α :=
  insert (.impl (predicateAt P c) (predicateAt Q c)) (workedContext P Q c)

theorem worked_context_harrop (P Q : L.Relations 1) (c : L.Term α) :
    ContextHarrop (workedContext P Q c) := by
  intro D hD
  simp only [workedContext, Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with rfl | rfl <;>
    simp [universalImplication, predicateBody, predicateAt, IsHarrop,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.EqualityFree]

private def workedAntecedent (P Q : L.Relations 1) (c : L.Term α) :
    CoreProof L (workedDelta P Q c) (predicateAt P c) :=
  .relation P _ (by simp [workedDelta, workedContext, predicateAt])

private def workedLeaf (P Q : L.Relations 1) (c : L.Term α) :
    CoreProof L (insert (predicateAt Q c) (workedDelta P Q c)) (predicateAt Q c) :=
  .relation Q _ (Finset.mem_insert_self _ _)

/-- The actual input stores the original c and the same private antecedent tree. -/
def workedInput (P Q : L.Relations 1) (c : L.Term α) :
    RawProof L (workedContext P Q c) (.ex (predicateBody Q)) := by
  refine ⟨.allLeft (B := .impl (predicateBody P) (predicateBody Q)) c
    (by simp [workedContext, universalImplication]) ?_,
    context_pure (worked_context_harrop P Q c), True.intro⟩
  change CoreProof L (workedDelta P Q c) (.ex (predicateBody Q))
  exact .implLeft (Finset.mem_insert_self _ _) (workedAntecedent P Q c)
    (.exRight c (workedLeaf P Q c))

/-- This is the same left spine with the existential-right removed. -/
def workedFactor (P Q : L.Relations 1) (c : L.Term α) :
    RawProof L (workedContext P Q c) ((predicateBody Q).instantiate c) := by
  refine ⟨.allLeft (B := .impl (predicateBody P) (predicateBody Q)) c
    (by simp [workedContext, universalImplication]) ?_,
    context_pure (worked_context_harrop P Q c), True.intro⟩
  change CoreProof L (workedDelta P Q c) (predicateAt Q c)
  exact .implLeft (Finset.mem_insert_self _ _) (workedAntecedent P Q c) (workedLeaf P Q c)

theorem worked_extraction (P Q : L.Relations 1) (c : L.Term α) :
    outcome (worked_context_harrop P Q c) (workedInput P Q c) =
      Sum.inl (⟨c, workedFactor P Q c⟩ : WitnessPacket (workedContext P Q c) (predicateBody Q)) := by
  rfl

def bottomContext : Context Language.empty Empty := {.falsum}

theorem bottom_context_harrop : ContextHarrop bottomContext := by
  intro D hD
  have he := Finset.mem_singleton.mp hD
  subst D
  trivial

def bottomExistence : RawProof Language.empty bottomContext (.ex .falsum) :=
  ⟨.falsumLeft (Finset.mem_singleton_self _), context_pure bottom_context_harrop, True.intro⟩

def bottomContradiction : RawProof Language.empty bottomContext .falsum :=
  ⟨.falsumLeft (Finset.mem_singleton_self _), context_pure bottom_context_harrop, True.intro⟩

theorem bottom_witness_impossible :
    ¬ Nonempty (WitnessPacket bottomContext (.falsum : BF Language.empty Empty 1)) := by
  rintro ⟨d⟩
  exact Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderSequents.constantFreeNoGroundTerm ⟨d.term⟩

theorem bottom_context_inconsistent : ¬ Consistent bottomContext := by
  intro hCon
  exact hCon ⟨bottomContradiction⟩

theorem bottom_extraction : outcome bottom_context_harrop bottomExistence =
    Sum.inr bottomContradiction := by
  rfl

def universalBottomContext : Context Language.empty Empty := {.all .falsum}

theorem universalBottom_harrop : ContextHarrop universalBottomContext := by
  intro D hD
  have he := Finset.mem_singleton.mp hD
  subst D
  trivial

theorem universalBottom_raw_consistent : Consistent universalBottomContext := by
  rintro ⟨q⟩
  cases q.tree with
  | falsumLeft h => simp [universalBottomContext] at h
  | conjLeft h _ => simp [universalBottomContext] at h
  | disjLeft h _ _ => simp [universalBottomContext] at h
  | implLeft h _ _ => simp [universalBottomContext] at h
  | negLeft h _ => simp [universalBottomContext] at h
  | allLeft t _ _ =>
    exact Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderSequents.constantFreeNoGroundTerm ⟨t⟩
  | exLeft h _ => simp [universalBottomContext] at h

/-- Its actual all-left term is the first reserved variable, not an original ground term. -/
def universalBottom_reserved_contradiction :
    RawProof Language.empty (reservedContext universalBottomContext) .falsum := by
  change RawProof Language.empty ({.all .falsum} : Context Language.empty (Empty ⊕ ℕ)) .falsum
  refine ⟨.allLeft (B := (.falsum : BF Language.empty (Empty ⊕ ℕ) 1))
    (.var (.inr 0)) (Finset.mem_singleton_self _) (.falsumLeft (Finset.mem_insert_self _ _)),
    ?_, True.intro⟩
  intro C hC
  have he := Finset.mem_singleton.mp hC
  subst C
  trivial

theorem universalBottom_reserved_inconsistent :
    ¬ Consistent (reservedContext universalBottomContext) := by
  intro hCon
  exact hCon ⟨universalBottom_reserved_contradiction⟩

end
end Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderHarropExtraction
