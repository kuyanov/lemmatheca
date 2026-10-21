import Lemmatheca.QuantifierFreeValidity.Formulas

namespace Lemmatheca.MathematicalLogic.QuantifierFreeValidity
open FirstOrder FirstOrder.Language

universe u v w
variable {L : Language.{u, v}}

/-- The actual finite disjunction of the displayed equalities; empty means falsity. -/
def equationDisjunction : List (GroundEquality.TermPair L) → L.Sentence
  | [] => .falsum
  | p :: ps => (Atom.equal p.1 p.2).formula ⊔ equationDisjunction ps

theorem equationDisjunction_truth (ps : List (GroundEquality.TermPair L))
    (M : Type w) [L.Structure M] :
    (equationDisjunction ps).Realize M ↔
      ∃ p ∈ ps, p.1.realize Empty.elim = p.2.realize (Empty.elim : Empty → M) := by
  induction ps with
  | nil => simp [equationDisjunction, Sentence.Realize, Formula.Realize, BoundedFormula.Realize]
  | cons p ps ih =>
    rw [equationDisjunction, Sentence.realize_sup]
    change ((Atom.equal p.1 p.2).Realize M ∨ (equationDisjunction ps).Realize M) ↔ _
    rw [equal_truth, ih]
    simp

def EquationsHold (E : Finset (GroundEquality.TermPair L))
    (M : Type w) [L.Structure M] : Prop :=
  ∀ p ∈ E, p.1.realize Empty.elim = p.2.realize (Empty.elim : Empty → M)

/-- Semantic consequence is quantified over every nonempty structure in the term universe. -/
def EquationConsequence (E : Finset (GroundEquality.TermPair L))
    (p : GroundEquality.TermPair L) : Prop :=
  ∀ (M : Type u) (inst : L.Structure M), Nonempty M →
    @EquationsHold L E M inst →
      @Atom.Realize L (Atom.equal p.1 p.2) M inst

variable [∀ n, DecidableEq (L.Functions n)]

theorem equality_convexity (E : Finset (GroundEquality.TermPair L))
    (ps : List (GroundEquality.TermPair L)) :
    (∀ (M : Type u) (inst : L.Structure M), Nonempty M →
      @EquationsHold L E M inst → @Sentence.Realize L M inst (equationDisjunction ps)) ↔
      ∃ p ∈ ps, EquationConsequence E p := by
  constructor
  · intro h
    classical
    let P : GroundEquality.Problem L := ⟨E, ps.toFinset⟩
    let S := GroundEquality.support P
    have hE : E ⊆ S.product S := GroundEquality.equations_supported P
    have hS : GroundEquality.SubtermClosed S := GroundEquality.support_closed P
    let M := GroundEquality.Carrier S E hE
    let inst : L.Structure M := GroundEquality.modelStructure S E hE hS
    have hME : EquationsHold E M := by
      intro p hp
      obtain ⟨ht, hs⟩ := Finset.mem_product.mp (hE hp)
      exact (GroundEquality.model_equality_iff S E hE hS p.1 p.2 ht hs).mpr
        (GroundEquality.equations_subset_closure S E hp)
    obtain ⟨p, hp, heq⟩ := (equationDisjunction_truth ps M).mp (h M inst inferInstance hME)
    have hpD : p ∈ P.disequations := by simpa [P] using hp
    obtain ⟨ht, hs⟩ := Finset.mem_product.mp (GroundEquality.disequations_supported P hpD)
    have hc := (GroundEquality.model_equality_iff S E hE hS p.1 p.2 ht hs).mp heq
    refine ⟨p, hp, ?_⟩
    intro N instN _hne hN
    let : L.Structure N := instN
    exact (equal_truth p.1 p.2 N).mpr (GroundEquality.closure_sound S E hE N hN p hc)
  · rintro ⟨p, hp, he⟩ M inst hne hM
    let : L.Structure M := inst
    apply (equationDisjunction_truth ps M).mpr
    exact ⟨p, hp, (equal_truth p.1 p.2 M).mp (he M inst hne hM)⟩

end Lemmatheca.MathematicalLogic.QuantifierFreeValidity
