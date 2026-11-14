import Lemmatheca.EqualityFreeIntuitionisticFirstOrderWitnessProperty.Universal
import Lemmatheca.EqualityFreeIntuitionisticFirstOrderSequents.Examples
import Lemmatheca.HerbrandModels.Examples

/-! Specified f(c), c, and u0 outputs, and the two assumption counterexamples. -/
namespace Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderWitnessProperty
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.IntuitionisticFirstOrder
open Lemmatheca.ProofTheory.IntuitionisticFirstOrder.WitnessProperty
abbrev Formula := Lemmatheca.ProofTheory.FirstOrder.Formula
abbrev BF := Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifowpExamplesEq {K : Language.{u,v}} {δ : Type w} :
    DecidableEq (Formula K δ) := Classical.decEq _

def identityBody (R : L.Relations 1) : BF L α 1 :=
  .impl (.rel R (fun _ => .var (.inr 0))) (.rel R (fun _ => .var (.inr 0)))

def identityInstance (R : L.Relations 1) (t : L.Term α) :
    RawProof L ∅ ((identityBody (α := α) R).instantiate t) := by
  refine ⟨?_, ?_, ?_⟩
  · change CoreProof L ∅ (.impl
      (.rel R (fun _ => t.relabel Sum.inl)) (.rel R (fun _ => t.relabel Sum.inl)))
    exact .implRight (.relation R _ (Finset.mem_insert_self _ _))
  · intro A hA
    exact (Finset.notMem_empty A hA).elim
  · simp [identityBody, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.EqualityFree]

def identityExistence (R : L.Relations 1) (t : L.Term α) :
    RawProof L ∅ (.ex (identityBody (α := α) R)) := by
  exact ⟨.exRight t (identityInstance R t).tree, (identityInstance R t).context_pure,
    by simp [identityBody, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.EqualityFree]⟩

theorem identityExistence_tree (R : L.Relations 1) (t : L.Term α) :
    (identityExistence R t).tree = .exRight t (identityInstance R t).tree := by rfl

def identityDisjunction (R : L.Relations 1) (t : L.Term α) :
    RawProof L ∅ (.disj (.ex (identityBody (α := α) R)) .falsum) := by
  exact ⟨.disjRightLeft (identityExistence R t).tree,
    (identityExistence R t).context_pure, ⟨(identityExistence R t).conclusion_pure, trivial⟩⟩

def workedConstant := identityExistence
  Lemmatheca.Entry.HerbrandModels.Relations.p Lemmatheca.Entry.HerbrandModels.c

def workedFunction := identityExistence
  Lemmatheca.Entry.HerbrandModels.Relations.p
  (Lemmatheca.Entry.HerbrandModels.f Lemmatheca.Entry.HerbrandModels.c)

theorem worked_constant_witness :
    (rawWitness workedConstant).term = Lemmatheca.Entry.HerbrandModels.c := by
  have e := rawWitness_exRight
    (B := identityBody (L := Lemmatheca.Entry.HerbrandModels.exampleLanguage)
      (α := Empty) Lemmatheca.Entry.HerbrandModels.Relations.p)
    (by simp [identityBody, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.EqualityFree])
    Lemmatheca.Entry.HerbrandModels.c
    (identityInstance Lemmatheca.Entry.HerbrandModels.Relations.p Lemmatheca.Entry.HerbrandModels.c)
  simpa only [workedConstant, identityExistence] using congrArg WitnessPacket.term e

theorem worked_function_witness :
    (rawWitness workedFunction).term =
      Lemmatheca.Entry.HerbrandModels.f Lemmatheca.Entry.HerbrandModels.c := by
  have e := rawWitness_exRight
    (B := identityBody (L := Lemmatheca.Entry.HerbrandModels.exampleLanguage)
      (α := Empty) Lemmatheca.Entry.HerbrandModels.Relations.p)
    (by simp [identityBody, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.EqualityFree])
    (Lemmatheca.Entry.HerbrandModels.f Lemmatheca.Entry.HerbrandModels.c)
    (identityInstance Lemmatheca.Entry.HerbrandModels.Relations.p
      (Lemmatheca.Entry.HerbrandModels.f Lemmatheca.Entry.HerbrandModels.c))
  simpa only [workedFunction, identityExistence] using congrArg WitnessPacket.term e

theorem worked_selected_tree :
    rawDisjunction (identityDisjunction Lemmatheca.Entry.HerbrandModels.Relations.p
      (Lemmatheca.Entry.HerbrandModels.f Lemmatheca.Entry.HerbrandModels.c)) =
      (Sum.inl workedFunction : DisjunctPacket
        (L := Lemmatheca.Entry.HerbrandModels.exampleLanguage) (α := Empty)
        (.ex (identityBody (L := Lemmatheca.Entry.HerbrandModels.exampleLanguage)
          (α := Empty) Lemmatheca.Entry.HerbrandModels.Relations.p)) .falsum) := by
  have e := rawDisjunction_left
    (identityExistence Lemmatheca.Entry.HerbrandModels.Relations.p
      (Lemmatheca.Entry.HerbrandModels.f Lemmatheca.Entry.HerbrandModels.c))
    (by trivial : (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.falsum :
      Formula Lemmatheca.Entry.HerbrandModels.exampleLanguage Empty).EqualityFree)
  simpa only [identityDisjunction, workedFunction] using e

theorem reserved_witness :
    (publicWitness
      Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderSequents.constantFreeExistence).term =
      .var (.inr 0) := by
  let p : RawProof Language.empty (∅ : Context Language.empty (Empty ⊕ ℕ))
      (.impl .falsum .falsum) :=
    ⟨.implRight (.falsumLeft (Finset.mem_insert_self _ _)),
      (fun A hA => (Finset.notMem_empty A hA).elim), ⟨trivial, trivial⟩⟩
  have e := rawWitness_exRight
    (B := (.impl .falsum .falsum : BF Language.empty (Empty ⊕ ℕ) 1))
    (by trivial) (.var (.inr 0)) p
  change (rawWitness (⟨.exRight (.var (.inr 0)) p.tree, p.context_pure, (by trivial)⟩ :
    RawProof Language.empty (∅ : Context Language.empty (Empty ⊕ ℕ))
      (.ex (.impl .falsum .falsum)))).term = _
  exact congrArg WitnessPacket.term e

inductive ChoiceRelation : ℕ → Type
  | atom (side : Bool) : ChoiceRelation 0

def choiceLanguage : Language := ⟨fun _ => Empty, ChoiceRelation⟩

def choiceAtom (side : Bool) : Formula choiceLanguage Empty :=
  .rel (.atom side) Fin.elim0

def choiceContext : Context choiceLanguage Empty :=
  {.disj (choiceAtom false) (choiceAtom true)}

/-- The selected side is false; the other nullary relation is true. -/
@[instance_reducible]
def choiceStructure (side : Bool) : choiceLanguage.Structure PUnit where
  funMap := fun f => f.elim
  RelMap := fun R _ => match R with | .atom b => b ≠ side

def choiceAssumption : RawProof choiceLanguage choiceContext
    (.disj (choiceAtom false) (choiceAtom true)) := by
  apply RawProof.identity
  · intro A hA
    have he := Finset.mem_singleton.mp hA
    subst A
    trivial
  · trivial
  · exact Finset.mem_singleton_self _

theorem choice_countermodel (side : Bool) :
    letI : choiceLanguage.Structure PUnit := choiceStructure side
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds (M := PUnit)
        (.disj (choiceAtom false) (choiceAtom true)) Empty.elim ∧
      ¬ Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds (M := PUnit) (choiceAtom side) Empty.elim := by
  change (false ≠ side ∨ true ≠ side) ∧ ¬ (side ≠ side)
  cases side <;> simp

theorem choice_no_factors (side : Bool) :
    ¬ Nonempty (RawProof choiceLanguage choiceContext (choiceAtom side)) ∧
    ¬ Nonempty (RawCutProof choiceLanguage choiceContext (choiceAtom side)) ∧
    ¬ Derives choiceLanguage choiceContext (choiceAtom side) ∧
    ¬ CutDerives choiceLanguage choiceContext (choiceAtom side) := by
  let : choiceLanguage.Structure (PUnit : Type) := choiceStructure side
  have hΓ : ∀ B ∈ choiceContext,
      Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds (M := (PUnit : Type)) B Empty.elim := by
    intro B hB
    have he := Finset.mem_singleton.mp hB
    subst B
    exact (choice_countermodel side).1
  have hf : ¬ Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds
      (M := (PUnit : Type)) (choiceAtom side) Empty.elim := (choice_countermodel side).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨p⟩
    exact hf (p.toNatural.sound Empty.elim hΓ)
  · rintro ⟨p⟩
    exact hf (p.toNatural.sound Empty.elim hΓ)
  · rintro ⟨p⟩
    exact hf ((Lemmatheca.ProofTheory.IntuitionisticFirstOrder.Proof.toNatural p).sound Empty.elim hΓ)
  · rintro ⟨p⟩
    exact hf ((Lemmatheca.ProofTheory.IntuitionisticFirstOrder.CutCertificate.toNatural p).sound Empty.elim hΓ)

/-- Every term in the existing no-functions unary example is its sole original name. -/
theorem escape_term (t : Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeLanguage.Term Unit) :
    t = .var () := by
  cases t with
  | var x => cases x; rfl
  | func f _ => exact f.elim

theorem escape_instance (t : Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeLanguage.Term Unit) :
    Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeBody.instantiate t =
      Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeAtom := by
  rw [escape_term t]
  rfl

def escapeAssumption :
    RawProof Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeLanguage
      {(.ex Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeBody)}
      (.ex Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeBody) := by
  apply RawProof.identity
  · intro A hA
    have he := Finset.mem_singleton.mp hA
    subst A
    trivial
  · trivial
  · exact Finset.mem_singleton_self _

theorem escape_no_instances
    (t : Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeLanguage.Term Unit) :
    ¬ Nonempty (RawProof Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeLanguage
      {(.ex Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeBody)}
      (Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeBody.instantiate t)) ∧
    ¬ Nonempty (RawCutProof Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeLanguage
      {(.ex Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeBody)}
      (Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeBody.instantiate t)) ∧
    ¬ Derives Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeLanguage
      {(.ex Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeBody)}
      (Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeBody.instantiate t) ∧
    ¬ CutDerives Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeLanguage
      {(.ex Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeBody)}
      (Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeBody.instantiate t) := by
  rw [escape_instance t]
  have hn := Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.witness_escape_not_derivable false false
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨p⟩
    exact hn ⟨p.toNatural.rename (Sum.inl : Unit → Unit ⊕ ℕ)⟩
  · rintro ⟨p⟩
    exact hn ⟨p.toNatural.rename (Sum.inl : Unit → Unit ⊕ ℕ)⟩
  · rintro ⟨p⟩
    exact hn ⟨Lemmatheca.ProofTheory.IntuitionisticFirstOrder.Proof.toNatural p⟩
  · rintro ⟨p⟩
    exact hn ⟨Lemmatheca.ProofTheory.IntuitionisticFirstOrder.CutCertificate.toNatural p⟩

end
end Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderWitnessProperty
