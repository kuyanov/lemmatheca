import Lemmatheca.Resolution.Resolution

/-! Definitional CNF on the corpus's shared propositional syntax.
Fresh names are tagged subformulas; lists retain occurrence duplicates. -/
namespace Lemmatheca.MathematicalLogic.TseitinEncoding

open Propositional
universe u
variable {α : Type u}

abbrev ExpandedAtom (α : Type u) := α ⊕ PropFormula α

def old (p : α) : ExpandedAtom α := .inl p

def fresh (A : PropFormula α) : ExpandedAtom α := .inr A

def restrict (w : Valuation (ExpandedAtom α)) : Valuation α := fun p => w (old p)

def extend (v : Valuation α) : Valuation (ExpandedAtom α)
  | .inl p => v p
  | .inr A => eval v A

def subformulas : PropFormula α → List (PropFormula α)
  | A@(.atom _) | A@(.falsum) => [A]
  | A@(.neg B) => A :: subformulas B
  | A@(.conj B C) | A@(.disj B C) | A@(.impl B C) =>
      A :: (subformulas B ++ subformulas C)

def treeSize (A : PropFormula α) : ℕ := (subformulas A).length

def pos (p : ExpandedAtom α) : PropLiteral (ExpandedAtom α) := ⟨p, true⟩
def neg (p : ExpandedAtom α) : PropLiteral (ExpandedAtom α) := ⟨p, false⟩

def gate : PropFormula α → List (List (PropLiteral (ExpandedAtom α)))
  | A@(.atom p) => [[neg (fresh A), pos (old p)], [pos (fresh A), neg (old p)]]
  | A@(.falsum) => [[neg (fresh A)]]
  | A@(.neg B) =>
      [[neg (fresh A), neg (fresh B)], [pos (fresh A), pos (fresh B)]]
  | A@(.conj B C) =>
      [[neg (fresh A), pos (fresh B)], [neg (fresh A), pos (fresh C)],
       [pos (fresh A), neg (fresh B), neg (fresh C)]]
  | A@(.disj B C) =>
      [[pos (fresh A), neg (fresh B)], [pos (fresh A), neg (fresh C)],
       [neg (fresh A), pos (fresh B), pos (fresh C)]]
  | A@(.impl B C) =>
      [[pos (fresh A), pos (fresh B)], [pos (fresh A), neg (fresh C)],
       [neg (fresh A), neg (fresh B), pos (fresh C)]]

def GateCondition (w : Valuation (ExpandedAtom α)) : PropFormula α → Prop
  | A@(.atom p) => w (fresh A) = w (old p)
  | A@(.falsum) => w (fresh A) = false
  | A@(.neg B) => w (fresh A) = !(w (fresh B))
  | A@(.conj B C) => w (fresh A) = (w (fresh B) && w (fresh C))
  | A@(.disj B C) => w (fresh A) = (w (fresh B) || w (fresh C))
  | A@(.impl B C) => w (fresh A) = (!(w (fresh B)) || w (fresh C))

def ListModels (w : Valuation β) (L : List (List (PropLiteral β))) : Prop :=
  ∀ C ∈ L, ∃ l ∈ C, w l.atom = l.positive

def definitions : PropFormula α → List (List (PropLiteral (ExpandedAtom α)))
  | A@(.atom _) | A@(.falsum) => gate A
  | A@(.neg B) => gate A ++ definitions B
  | A@(.conj B C) | A@(.disj B C) | A@(.impl B C) =>
      gate A ++ definitions B ++ definitions C

def encoding (A : PropFormula α) : List (List (PropLiteral (ExpandedAtom α))) :=
  [pos (fresh A)] :: definitions A

def encodingFormula (A : PropFormula α) : PropFormula (ExpandedAtom α) :=
  cnfFormula (encoding A)

def literalCount (L : List (List (PropLiteral β))) : ℕ := (L.map List.length).sum

theorem tags_fresh (p : α) (A B : PropFormula α) :
    old p ≠ fresh A ∧ (fresh A = fresh B ↔ A = B) := by
  simp [old, fresh]

theorem subformulas_self (A : PropFormula α) : A ∈ subformulas A := by
  cases A <;> simp [subformulas]

theorem treeSize_recursions (A B : PropFormula α) (p : α) :
    treeSize (.atom p) = 1 ∧ treeSize (.falsum : PropFormula α) = 1 ∧
    treeSize (.neg A) = 1 + treeSize A ∧
    treeSize (.conj A B) = 1 + treeSize A + treeSize B ∧
    treeSize (.disj A B) = 1 + treeSize A + treeSize B ∧
    treeSize (.impl A B) = 1 + treeSize A + treeSize B := by
  simp [treeSize, subformulas]
  omega

theorem gate_correct (w : Valuation (ExpandedAtom α)) (A : PropFormula α) :
    ListModels w (gate A) ↔ GateCondition w A := by
  cases A with
  | atom p =>
    cases h₁ : w (fresh (.atom p)) <;> cases h₂ : w (old p) <;>
      simp [ListModels, gate, GateCondition, pos, neg, h₁, h₂]
  | falsum =>
    cases h : w (fresh .falsum) <;>
      simp [ListModels, gate, GateCondition, neg, h]
  | neg B =>
    cases h₁ : w (fresh (.neg B)) <;> cases h₂ : w (fresh B) <;>
      simp [ListModels, gate, GateCondition, pos, neg, h₁, h₂]
  | conj B C =>
    cases h₁ : w (fresh (.conj B C)) <;> cases h₂ : w (fresh B) <;>
      cases h₃ : w (fresh C) <;>
      simp [ListModels, gate, GateCondition, pos, neg, h₁, h₂, h₃]
  | disj B C =>
    cases h₁ : w (fresh (.disj B C)) <;> cases h₂ : w (fresh B) <;>
      cases h₃ : w (fresh C) <;>
      simp [ListModels, gate, GateCondition, pos, neg, h₁, h₂, h₃]
  | impl B C =>
    cases h₁ : w (fresh (.impl B C)) <;> cases h₂ : w (fresh B) <;>
      cases h₃ : w (fresh C) <;>
      simp [ListModels, gate, GateCondition, pos, neg, h₁, h₂, h₃]

theorem listModels_formula {β : Type u} (w : Valuation β)
    (L : List (List (PropLiteral β))) :
    ListModels w L ↔ eval w (cnfFormula L) = true := by
  classical
  rw [Lemmatheca.ProofTheory.Resolution.list_cnf]
  simp [ListModels, Lemmatheca.ProofTheory.Resolution.Models,
    Lemmatheca.ProofTheory.Resolution.ofCnf, Lemmatheca.ProofTheory.Resolution.ClauseSat,
    Lemmatheca.ProofTheory.Resolution.LiteralSat]

theorem definitions_flatMap (A : PropFormula α) :
    definitions A = (subformulas A).flatMap gate := by
  induction A <;>
    simp_all [definitions, subformulas, List.flatMap_append, List.append_assoc]

theorem encoding_isCnf (A : PropFormula α) : IsCnf (encodingFormula A) := by
  exact ⟨encoding A, rfl⟩

private theorem models_append {β : Type u} (w : Valuation β)
    (L M : List (List (PropLiteral β))) :
    ListModels w (L ++ M) ↔ ListModels w L ∧ ListModels w M := by
  constructor
  · intro h
    exact ⟨fun C hC => h C (List.mem_append_left M hC),
      fun C hC => h C (List.mem_append_right L hC)⟩
  · rintro ⟨hL, hM⟩ C hC
    rcases List.mem_append.mp hC with hC | hC
    · exact hL C hC
    · exact hM C hC

theorem definitions_models (w : Valuation (ExpandedAtom α)) (A : PropFormula α) :
    ListModels w (definitions A) ↔
      ∀ B ∈ subformulas A, w (fresh B) = eval (restrict w) B := by
  induction A with
  | atom p =>
    simpa [definitions, subformulas, GateCondition, eval, restrict] using
      gate_correct w (.atom p)
  | falsum =>
    simpa [definitions, subformulas, GateCondition, eval] using gate_correct w .falsum
  | neg B ih =>
    rw [definitions, models_append, gate_correct, ih]
    simp only [subformulas, List.forall_mem_cons]
    constructor
    · rintro ⟨hg, h⟩
      exact ⟨by simpa [GateCondition, eval, h B (subformulas_self B)] using hg, h⟩
    · rintro ⟨hg, h⟩
      exact ⟨by simpa [GateCondition, eval, h B (subformulas_self B)] using hg, h⟩
  | conj B C ihB ihC | disj B C ihB ihC | impl B C ihB ihC =>
    rw [definitions, models_append, models_append, gate_correct, ihB, ihC]
    simp only [subformulas, List.forall_mem_cons, List.forall_mem_append]
    constructor
    · rintro ⟨⟨hg, hB⟩, hC⟩
      refine ⟨?_, hB, hC⟩
      simpa [GateCondition, eval, hB B (subformulas_self B),
        hC C (subformulas_self C)] using hg
    · rintro ⟨hg, hB, hC⟩
      refine ⟨⟨?_, hB⟩, hC⟩
      simpa [GateCondition, eval, hB B (subformulas_self B),
        hC C (subformulas_self C)] using hg

theorem restrict_extend (v : Valuation α) : restrict (extend v) = v := by
  rfl

theorem extend_definitions (v : Valuation α) (A : PropFormula α) :
    ListModels (extend v) (definitions A) := by
  apply (definitions_models _ A).mpr
  intro B _
  simp [extend, fresh, restrict_extend]

theorem encoding_restrict (w : Valuation (ExpandedAtom α)) (A : PropFormula α) :
    ListModels w (encoding A) ↔
      ListModels w (definitions A) ∧ eval (restrict w) A = true := by
  have he : ListModels w (encoding A) ↔
      w (fresh A) = true ∧ ListModels w (definitions A) := by
    simp [ListModels, encoding, pos]
  rw [he]
  have hroot (hd : ListModels w (definitions A)) :
      w (fresh A) = eval (restrict w) A :=
    (definitions_models w A).mp hd A (subformulas_self A)
  constructor
  · rintro ⟨hA, hd⟩
    exact ⟨hd, (hroot hd).symm.trans hA⟩
  · rintro ⟨hd, hA⟩
    exact ⟨(hroot hd).trans hA, hd⟩

theorem encoding_extend (v : Valuation α) (A : PropFormula α) :
    ListModels (extend v) (encoding A) ↔ eval v A = true := by
  rw [encoding_restrict, restrict_extend]
  simp [extend_definitions]

theorem equisatisfiable (A : PropFormula α) :
    (∃ w, ListModels w (encoding A)) ↔ ∃ v, eval v A = true := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨restrict w, ((encoding_restrict w A).mp hw).2⟩
  · rintro ⟨v, hv⟩
    exact ⟨extend v, (encoding_extend v A).mpr hv⟩

theorem used_values_unique (w z : Valuation (ExpandedAtom α)) (A : PropFormula α)
    (hw : ListModels w (definitions A)) (hz : ListModels z (definitions A))
    (hold : restrict w = restrict z) :
    ∀ B ∈ subformulas A,
      w (fresh B) = z (fresh B) ∧ w (fresh B) = eval (restrict w) B := by
  intro B hB
  have hwB := (definitions_models w A).mp hw B hB
  have hzB := (definitions_models z A).mp hz B hB
  exact ⟨by rw [hwB, hzB, hold], hwB⟩

theorem unused_names_irrelevant (w z : Valuation (ExpandedAtom α)) (A : PropFormula α)
    (hold : restrict w = restrict z)
    (hused : ∀ B ∈ subformulas A, w (fresh B) = z (fresh B)) :
    (ListModels w (definitions A) ↔ ListModels z (definitions A)) ∧
    (ListModels w (encoding A) ↔ ListModels z (encoding A)) := by
  have hd : ListModels w (definitions A) ↔ ListModels z (definitions A) := by
    rw [definitions_models, definitions_models]
    constructor
    · intro h B hB
      rw [← hused B hB, ← hold]
      exact h B hB
    · intro h B hB
      rw [hused B hB, hold]
      exact h B hB
  refine ⟨hd, ?_⟩
  rw [encoding_restrict, encoding_restrict, hold, hd]

theorem gate_bounds (A : PropFormula α) :
    (gate A).length ≤ 3 ∧ literalCount (gate A) ≤ 7 ∧
      ∀ C ∈ gate A, C.length ≤ 3 := by
  cases A <;> simp [gate, literalCount]

theorem definitions_bounds (A : PropFormula α) :
    (definitions A).length ≤ 3 * treeSize A ∧
      literalCount (definitions A) ≤ 7 * treeSize A := by
  induction A <;>
    simp_all [definitions, gate, literalCount, treeSize, subformulas,
      List.map_append, List.sum_append] <;> omega

theorem encoding_bounds (A : PropFormula α) :
    (encoding A).length ≤ 3 * treeSize A + 1 ∧
      literalCount (encoding A) ≤ 7 * treeSize A + 1 ∧
      ∀ C ∈ encoding A, C.length ≤ 3 := by
  obtain ⟨hc, hl⟩ := definitions_bounds A
  have hcount : (encoding A).length ≤ 3 * treeSize A + 1 := by
    simpa [encoding] using Nat.add_le_add_right hc 1
  have hlength : literalCount (encoding A) ≤ 7 * treeSize A + 1 := by
    simpa [encoding, literalCount, Nat.add_comm] using Nat.add_le_add_right hl 1
  refine ⟨hcount, hlength, ?_⟩
  intro C hC
  simp only [encoding, List.mem_cons] at hC
  rcases hC with rfl | hC
  · simp
  · rw [definitions_flatMap] at hC
    obtain ⟨B, _, hBC⟩ := List.mem_flatMap.mp hC
    exact (gate_bounds B).2.2 C hBC

theorem definitions_satisfiable (A : PropFormula α) :
    ∃ w, ListModels w (definitions A) := by
  exact ⟨extend (fun _ => false), extend_definitions _ A⟩

end Lemmatheca.MathematicalLogic.TseitinEncoding
