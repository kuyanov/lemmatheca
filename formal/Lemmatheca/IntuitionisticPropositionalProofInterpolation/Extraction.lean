import Lemmatheca.IntuitionisticPropositionalProofInterpolation.Cases

/-! Transparent recursion on the supplied eleven-rule tree. Only the original
strict premise trees are recursed into, with the displayed covering sides. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Interpolation
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
universe u
variable {α : Type u} [DecidableEq α]
noncomputable section

private theorem covers_left {Γ L R : Finset (PropFormula α)} (h : Covers Γ L R)
    (A : PropFormula α) : Covers (insert A Γ) (insert A L) R := by
  simpa only [Covers,Finset.insert_union] using Finset.insert_subset_insert A h

private theorem covers_right {Γ L R : Finset (PropFormula α)} (h : Covers Γ L R)
    (A : PropFormula α) : Covers (insert A Γ) L (insert A R) := by
  simpa only [Covers,Finset.union_insert] using Finset.insert_subset_insert A h

private theorem covers_swap {Γ L R : Finset (PropFormula α)} (h : Covers Γ L R) :
    Covers Γ R L := by simpa only [Covers,Finset.union_comm] using h

private theorem principal_right {Γ L R : Finset (PropFormula α)} (h : Covers Γ L R)
    {A : PropFormula α} (hA : A ∈ Γ) (hn : A ∉ L) : A ∈ R :=
  (Finset.mem_union.mp (h hA)).resolve_left hn

def extract {Γ : Finset (PropFormula α)} {C : PropFormula α} (p : CutFree.Proof Γ C) :
    (L R : Finset (PropFormula α)) → Covers Γ L R → Packet L R C := by
  induction p with
  | atom hp =>
      intro L R h
      exact atomCase L R _ (h hp)
  | falsumLeft hb =>
      intro L R h
      exact falsumCase L R _ (h hb)
  | @conjLeft Γ A B C hd p ih =>
      intro L R h
      by_cases hl : conj A B ∈ L
      · exact conjLeftCase hl (ih (insert A (insert B L)) R (covers_left (covers_left h B) A))
      · exact conjRightSideCase (principal_right h hd hl) (ih L (insert A (insert B R)) (covers_right (covers_right h B) A))
  | conjRight p q ihp ihq =>
      intro L R h
      exact conjRightCase (ihp L R h) (ihq L R h)
  | @disjLeft Γ A B C hd p q ihp ihq =>
      intro L R h
      by_cases hl : disj A B ∈ L
      · exact disjLeftCase hl (ihp (insert A L) R (covers_left h A)) (ihq (insert B L) R (covers_left h B))
      · exact disjRightSideCase (principal_right h hd hl) (ihp L (insert A R) (covers_right h A)) (ihq L (insert B R) (covers_right h B))
  | disjRightLeft p ih =>
      intro L R h
      exact disjRightLeftCase (ih L R h)
  | disjRightRight p ih =>
      intro L R h
      exact disjRightRightCase (ih L R h)
  | @implLeft Γ A B C hd p q ihp ihq =>
      intro L R h
      by_cases hl : impl A B ∈ L
      · exact implLeftCase hl (ihp R L (covers_swap h)) (ihq (insert B L) R (covers_left h B))
      · exact implRightSideCase (principal_right h hd hl) (ihp L R h) (ihq L (insert B R) (covers_right h B))
  | @implRight Γ A B p ih =>
      intro L R h
      exact implRightCase (ih L (insert A R) (covers_right h A))
  | @negLeft Γ A C hd p ih =>
      intro L R h
      by_cases hl : neg A ∈ L
      · exact negLeftCase hl (ih R L (covers_swap h))
      · exact negRightSideCase (principal_right h hd hl) (ih L R h)
  | @negRight Γ A p ih =>
      intro L R h
      exact negRightCase (ih L (insert A R) (covers_right h A))

/-- Exact cut-removal composition on the same antecedent and succedent. -/
def extractCut {Γ : Finset (PropFormula α)} {C : PropFormula α} (p : CutFree.CutProof Γ C)
    (L R : Finset (PropFormula α)) (h : Covers Γ L R) : Packet L R C :=
  extract p.eliminate L R h

end
end Lemmatheca.ProofTheory.Intuitionistic.Interpolation
