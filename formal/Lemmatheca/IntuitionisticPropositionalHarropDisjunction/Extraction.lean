import Lemmatheca.IntuitionisticPropositionalHarropDisjunction.Syntax

/-! Follow the supplied continuation tree; each lift retains its original tag. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Harrop
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open CutFree
universe u
variable {α : Type u} [DecidableEq α]

abbrev Packet (Γ : Finset (PropFormula α)) (A B : PropFormula α) :=
  Sum (Proof Γ A) (Proof Γ B)

/-- Reuse the principal membership and rebuild exactly this conjunction-left. -/
def liftConjunction {Γ : Finset (PropFormula α)} {X Y A B : PropFormula α}
    (h : .conj X Y ∈ Γ) (d : Packet (insert X (insert Y Γ)) A B) : Packet Γ A B :=
  Sum.map (fun p => Proof.conjLeft h p) (fun p => Proof.conjLeft h p) d

/-- Retain the same antecedent tree on either selected continuation side. -/
def liftImplication {Γ : Finset (PropFormula α)} {X Y A B : PropFormula α}
    (h : .impl X Y ∈ Γ) (u : Proof Γ X) (d : Packet (insert Y Γ) A B) : Packet Γ A B :=
  Sum.map (fun p => Proof.implLeft h u p) (fun p => Proof.implLeft h u p) d

/-- Generalized motive permits structural recursion on the original indexed tree. -/
private def ExtractTarget (Γ : Finset (PropFormula α)) : PropFormula α → Type u
  | .disj A B => ContextHarrop Γ → Packet Γ A B
  | _ => PUnit

private def extractAux {Γ : Finset (PropFormula α)} {C : PropFormula α}
    (p : Proof Γ C) : ExtractTarget Γ C :=
  match p with
  | .atom _ => PUnit.unit
  | .falsumLeft h => match C with
    | .disj _ _ => fun _ => Sum.inl (.falsumLeft h)
    | .atom _ | .falsum | .conj _ _ | .impl _ _ | .neg _ => PUnit.unit
  | .conjLeft h q => match C with
    | .disj _ _ => fun hΓ => liftConjunction h (extractAux q (context_conj hΓ h))
    | .atom _ | .falsum | .conj _ _ | .impl _ _ | .neg _ => PUnit.unit
  | .conjRight _ _ => PUnit.unit
  | .disjLeft h _ _ => match C with
    | .disj _ _ => fun hΓ => False.elim (hΓ _ h)
    | .atom _ | .falsum | .conj _ _ | .impl _ _ | .neg _ => PUnit.unit
  | .disjRightLeft q => fun _ => Sum.inl q
  | .disjRightRight q => fun _ => Sum.inr q
  | .implLeft h u q => match C with
    | .disj _ _ => fun hΓ => liftImplication h u (extractAux q (context_impl hΓ h))
    | .atom _ | .falsum | .conj _ _ | .impl _ _ | .neg _ => PUnit.unit
  | .implRight _ => PUnit.unit
  | .negLeft h u => match C with
    | .disj _ _ => fun _ => Sum.inl (.negLeft h u)
    | .atom _ | .falsum | .conj _ _ | .impl _ _ | .neg _ => PUnit.unit
  | .negRight _ => PUnit.unit
termination_by structural p

/-- Exactly the six reachable cases of a Harrop-context disjunction tree. -/
def extract {Γ : Finset (PropFormula α)} {A B : PropFormula α}
    (hΓ : ContextHarrop Γ) (p : Proof Γ (.disj A B)) : Packet Γ A B :=
  extractAux p hΓ

variable {Γ : Finset (PropFormula α)} {A B X Y : PropFormula α}

theorem extract_left (hΓ : ContextHarrop Γ) (p : Proof Γ A) :
    extract hΓ (.disjRightLeft (B := B) p) = Sum.inl p := by rfl

theorem extract_right (hΓ : ContextHarrop Γ) (p : Proof Γ B) :
    extract hΓ (.disjRightRight (A := A) p) = Sum.inr p := by rfl

theorem extract_falsum (hΓ : ContextHarrop Γ) (h : .falsum ∈ Γ) :
    extract (A := A) (B := B) hΓ (.falsumLeft h) = Sum.inl (.falsumLeft h) := by rfl

theorem extract_negation (hΓ : ContextHarrop Γ) (h : .neg X ∈ Γ) (u : Proof Γ X) :
    extract (A := A) (B := B) hΓ (.negLeft h u) = Sum.inl (.negLeft h u) := by rfl

theorem extract_conjunction (hΓ : ContextHarrop Γ) (h : .conj X Y ∈ Γ)
    (q : Proof (insert X (insert Y Γ)) (.disj A B)) :
    extract hΓ (.conjLeft h q) =
      liftConjunction h (extract (context_conj hΓ h) q) := by rfl

theorem extract_implication (hΓ : ContextHarrop Γ) (h : .impl X Y ∈ Γ)
    (u : Proof Γ X) (q : Proof (insert Y Γ) (.disj A B)) :
    extract hΓ (.implLeft h u q) =
      liftImplication h u (extract (context_impl hΓ h) q) := by rfl

/-- The normalized tree is the actual established elimination of the supplied input. -/
def extractCut (hΓ : ContextHarrop Γ) (p : CutProof Γ (.disj A B)) : Packet Γ A B :=
  extract hΓ p.eliminate

/-- The exact inversion, extraction, tag-preserving introduction composition. -/
def implicationChoice {H : PropFormula α} (hΓ : ContextHarrop Γ) (hH : IsHarrop H)
    (p : Proof Γ (.impl H (.disj A B))) : Packet Γ (.impl H A) (.impl H B) :=
  Sum.map Proof.implRight Proof.implRight
    (extract (context_insert hΓ hH) p.invertImpl)

end Lemmatheca.ProofTheory.Intuitionistic.Harrop
