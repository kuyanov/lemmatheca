import Lemmatheca.PropositionalProofInterpolation.Native

namespace Lemmatheca.Entry.PropositionalProofInterpolation

open Lemmatheca.ProofTheory.ClassicalPropositional
open Interpolation
open Lemmatheca.MathematicalLogic.Propositional (PropFormula)

universe u
variable {α : Type u} [DecidableEq α]

private theorem extract_formula_cast {Γ Δ : Sequent α} (he : Γ = Δ) (p : Proof Γ)
    (L R : Sequent α) (hc : Covers Δ L R) :
    (extract (he ▸ p) L R hc).formula =
      (extract p L R (he.symm ▸ hc)).formula := by
  cases he
  rfl

/-- The actual two-branch primitive tree used in the worked extraction. -/
def conjunctionProof (p q : α) :
    Proof {Nnf.neg p, Nnf.neg q, Nnf.and (.pos p) (.pos q)} := by
  have pa : Proof (insert (.pos p) {Nnf.neg p, Nnf.neg q}) :=
    .identity p (by simp) (by simp)
  have pb : Proof (insert (.pos q) {Nnf.neg p, Nnf.neg q}) :=
    .identity q (by simp) (by simp)
  have he : (insert (Nnf.and (.pos p) (.pos q)) {Nnf.neg p, Nnf.neg q} : Sequent α) =
      {Nnf.neg p, Nnf.neg q, Nnf.and (.pos p) (.pos q)} := by
    ext C
    simp [or_comm, or_assoc]
  exact he ▸ Proof.andIntro pa pb

/-- Exact output formula and exact common vocabulary of that supplied tree and split. -/
theorem conjunction_example (p q : α) (_hpq : p ≠ q) :
    (extract (conjunctionProof p q) {Nnf.neg p, Nnf.neg q}
      {Nnf.and (.pos p) (.pos q)} (by
        intro F hF
        simpa [Covers, Finset.mem_insert, Finset.mem_singleton, or_assoc] using hF)).formula =
        Nnf.and (.pos p) (.pos q) ∧
      vocabulary {Nnf.neg p, Nnf.neg q} ∩
        vocabulary {Nnf.and (.pos p) (.pos q)} = {p, q} := by
  constructor
  · unfold conjunctionProof
    erw [extract_formula_cast]
    simp [extract, conjunctionRight, atomic]
  · simp [vocabulary, Nnf.atoms]

/-- A specified atomic-identity tree, without a proof choice. -/
def identityProof (p : α) : Proof {Nnf.pos p, Nnf.neg p} :=
  .identity p (by simp) (by simp)

theorem left_constant (p : α) :
    (extract (identityProof p) {Nnf.pos p, Nnf.neg p} ∅ (by
      intro F hF
      exact Finset.mem_union_left _ hF)).formula = .bot := by
  simp [identityProof, extract, atomic]

theorem right_constant (p : α) :
    (extract (identityProof p) ∅ {Nnf.pos p, Nnf.neg p} (by
      intro F hF
      exact Finset.mem_union_right _ hF)).formula = .top := by
  simp [identityProof, extract, atomic]

/-- An explicit second witness for overlapping sides, with the opposite constant. -/
def overlapTop (p : α) : Witness {Nnf.pos p, Nnf.neg p} {Nnf.pos p, Nnf.neg p} where
  formula := .top
  leftProof := .truth (by simp)
  rightProof := .identity p (by simp) (by simp)
  common := by
    simp [Nnf.atoms]

theorem nonunique (p : α) :
    (extract (identityProof p) {Nnf.pos p, Nnf.neg p} {Nnf.pos p, Nnf.neg p} (by
      intro F hF
      exact Finset.mem_union_left _ hF)).formula = .bot ∧
      (overlapTop p).formula = .top ∧
      ∀ v : α → Bool, (Nnf.bot : Nnf α).eval v ≠ (Nnf.top : Nnf α).eval v := by
  refine ⟨?_, rfl, ?_⟩
  · simp [identityProof, extract, atomic]
  · intro v
    simp [Nnf.eval]

/-- Ordinary native factors through the reading of bottom. -/
theorem contradiction_factors (p : α) (B : PropFormula α) :
    Lemmatheca.MathematicalLogic.Propositional.Derives
      {PropFormula.conj (.atom p) (.neg (.atom p))} PropFormula.falsum ∧
      Lemmatheca.MathematicalLogic.Propositional.Derives {PropFormula.falsum} B := by
  constructor
  · have hh : Lemmatheca.MathematicalLogic.Propositional.Derives
        {PropFormula.conj (.atom p) (.neg (.atom p))}
        (PropFormula.conj (.atom p) (.neg (.atom p))) := .assumption (by simp)
    exact .negElim (.conjElimLeft hh) (.conjElimRight hh)
  · exact .falsumElim (.assumption (by simp))

/-- Ordinary native factors through the reading of top. -/
theorem tautology_factors (A : PropFormula α) (q : α) :
    Lemmatheca.MathematicalLogic.Propositional.Derives {A}
        (Lemmatheca.MathematicalLogic.Propositional.verum) ∧
      Lemmatheca.MathematicalLogic.Propositional.Derives
        {Lemmatheca.MathematicalLogic.Propositional.verum}
        (PropFormula.disj (.atom q) (.neg (.atom q))) := by
  constructor
  · apply Lemmatheca.MathematicalLogic.Propositional.Derives.negIntro
    exact .assumption (by simp)
  · exact (Lemmatheca.MathematicalLogic.Propositional.derives_excluded_middle _).weaken
      (Finset.empty_subset _)

end Lemmatheca.Entry.PropositionalProofInterpolation
