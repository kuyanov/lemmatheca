import Lemmatheca.MathematicalLogic.DiagramRealization
import Mathlib.Tactic.FinCases
import Lemmatheca.MathematicalLogic.BasicStructures

/-! Positive-diagram counterexamples and a new point above the original natural numbers. -/

namespace Lemmatheca.Entry.DiagramsAndExtensions

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.Diagrams
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics

noncomputable section

local instance : Language.empty.Structure (Fin 2) := Language.emptyStructure
local instance : Language.empty.Structure (Fin 1) := Language.emptyStructure

theorem positive_equality_diagram_allows_collapse :
    letI := namedExpansion (L := Language.empty) (fun _ : Fin 2 => (0 : Fin 1))
    (Fin 1) ⊨ positiveDiagram Language.empty (Fin 2) ∧
      ¬Function.Injective (canonicalMap Language.empty (Fin 2) (Fin 1)) := by
  let f : Fin 2 →[Language.empty] Fin 1 :=
    { toFun := fun _ => 0
      map_fun' := by intro n F; exact F.elim
      map_rel' := by intro n R; exact R.elim }
  refine ⟨hom_namedExpansion_models_positive f, ?_⟩
  change ¬Function.Injective (fun _ : Fin 2 => (0 : Fin 1))
  intro hinj
  exact (by decide : (0 : Fin 2) ≠ 1) (hinj rfl)

inductive UnaryPredicateSymbol : ℕ → Type
  | pred : UnaryPredicateSymbol 1

def predicateLanguage : Language := ⟨fun _ => Empty, UnaryPredicateSymbol⟩

@[instance_reducible]
def predicateStructure (truth : Prop) : predicateLanguage.Structure Unit where
  funMap f := f.elim
  RelMap := fun s _ => match s with | .pred => truth

theorem positive_predicate_diagram_does_not_reflect :
    letI : predicateLanguage.Structure Unit := predicateStructure False
    let N := ULift Unit
    letI : predicateLanguage.Structure N :=
      { funMap := fun f => f.elim, RelMap := fun _ _ => True }
    letI := namedExpansion (L := predicateLanguage) (fun _ : Unit => (⟨()⟩ : N))
    N ⊨ positiveDiagram predicateLanguage Unit ∧
      Function.Injective (canonicalMap predicateLanguage Unit N) ∧
      ¬∃ e : Unit ↪[predicateLanguage] N,
        (e : Unit → N) = canonicalMap predicateLanguage Unit N := by
  dsimp only
  let : predicateLanguage.Structure Unit := predicateStructure False
  let N := ULift Unit
  let : predicateLanguage.Structure N :=
    { funMap := fun f => f.elim, RelMap := fun _ _ => True }
  let f : Unit →[predicateLanguage] N :=
    { toFun := fun _ => ⟨()⟩
      map_fun' := by intro n F; exact F.elim
      map_rel' := by intro n R x hx; trivial }
  refine ⟨hom_namedExpansion_models_positive f, ?_, ?_⟩
  · intro a b _
    exact Subsingleton.elim a b
  · rintro ⟨e, _⟩
    have hr := e.map_rel UnaryPredicateSymbol.pred (fun _ => ())
    change True ↔ False at hr
    exact hr.mp trivial

theorem natural_order_countable_extension_upper_bound :
    letI := binaryRelStructure ℕ (· < ·)
    ∃ (N : Type) (r : N → N → Prop), Countable N ∧ IsStrictTotalOrder N r ∧
      (∀ x : N, ∃ y : N, r x y) ∧
      letI := binaryRelStructure N r
      ∃ (h : ℕ ↪ₑ[binaryRelLanguage] N) (b : N),
        (∀ n : ℕ, r (h n) b) ∧ (∀ n : ℕ, h n ≠ b) := by
  classical
  let := binaryRelStructure ℕ (· < ·)
  have natRel (a b : ℕ) :
      Structure.RelMap (L := binaryRelLanguage) .rel ![a, b] ↔ a < b := Iff.rfl
  let φ : ℕ → binaryRelLanguage.Formula (Option ℕ) := fun n =>
    Relations.formula₂ (L := binaryRelLanguage) BinaryRelationSymbol.rel (.var (some n)) (.var none)
  have φRealize {A : Type} [binaryRelLanguage.Structure A]
      (n : ℕ) (v : Option ℕ → A) :
      (φ n).Realize v ↔ Structure.RelMap (L := binaryRelLanguage) .rel ![v (some n), v none] := by
    exact FirstOrder.Language.Formula.realize_rel₂
  have hp (s : Finset (binaryRelLanguage.Formula (Option ℕ)))
      (hs : (↑s : Set _) ⊆ Set.range φ) :
      ∃ b : ℕ, ∀ ψ ∈ s, ψ.Realize (fun o => o.elim b id) := by
    let index : {ψ // ψ ∈ s} → ℕ := fun ψ => Classical.choose (hs ψ.property)
    have hindex (ψ : {ψ // ψ ∈ s}) : φ (index ψ) = ψ :=
      Classical.choose_spec (hs ψ.property)
    let indices := s.attach.image index
    refine ⟨indices.sup id + 1, ?_⟩
    intro ψ hψ
    have hψeq : φ (index ⟨ψ, hψ⟩) = ψ := hindex ⟨ψ, hψ⟩
    rw [← hψeq]
    change index ⟨ψ, hψ⟩ < indices.sup id + 1
    have hmem : index ⟨ψ, hψ⟩ ∈ indices :=
      Finset.mem_image.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _, rfl⟩
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hmem)
  obtain ⟨N, S, hcount, h, b, hb⟩ :=
    exists_countable_elementary_realization (L := binaryRelLanguage) (Set.range φ) hp
  let := S
  let r : N → N → Prop := fun a b => Structure.RelMap (L := binaryRelLanguage) .rel ![a, b]
  let ltAtom : {n : ℕ} → Fin n → Fin n → binaryRelLanguage.BoundedFormula Empty n :=
    fun i j => Relations.boundedFormula₂ (L := binaryRelLanguage) BinaryRelationSymbol.rel (.var (.inr i)) (.var (.inr j))
  have atomRealize {A : Type} [binaryRelLanguage.Structure A] {n : ℕ}
      (i j : Fin n) (v : Empty → A) (xs : Fin n → A) :
      (ltAtom i j).Realize v xs ↔
        Structure.RelMap (L := binaryRelLanguage) .rel ![xs i, xs j] := by
    exact BoundedFormula.realize_rel₂
  let irr : binaryRelLanguage.Sentence := (ltAtom (n := 1) 0 0).not.all
  let trans : binaryRelLanguage.Sentence :=
    ((ltAtom (n := 3) 0 1).imp ((ltAtom 1 2).imp (ltAtom 0 2))).all.all.all
  let total : binaryRelLanguage.Sentence :=
    (ltAtom (n := 2) 0 1 ⊔
      (BoundedFormula.equal (.var (.inr 0)) (.var (.inr 1)) ⊔ ltAtom 1 0)).all.all
  let noMax : binaryRelLanguage.Sentence := (ltAtom (n := 2) 0 1).ex.all
  have hirr : ∀ a : N, ¬r a a := by
    have hn : ℕ ⊨ irr := by
      change ∀ a : ℕ, ¬a < a
      exact Nat.lt_irrefl
    simpa [atomRealize, natRel, irr, Sentence.Realize, FirstOrder.Language.Formula.Realize, Fin.snoc, r]
      using (h.map_sentence irr).mp hn
  have htrans : ∀ a b c : N, r a b → r b c → r a c := by
    have hn : ℕ ⊨ trans := by
      change ∀ a b c : ℕ, a < b → b < c → a < c
      exact fun _ _ _ => Nat.lt_trans
    simpa [atomRealize, natRel, trans, Sentence.Realize, FirstOrder.Language.Formula.Realize, Fin.snoc, r]
      using (h.map_sentence trans).mp hn
  have htotal : ∀ a b : N, r a b ∨ a = b ∨ r b a := by
    have hn : ℕ ⊨ total := by
      simpa [atomRealize, natRel, total, Sentence.Realize, FirstOrder.Language.Formula.Realize,
        BoundedFormula.Realize, Term.realize, Fin.snoc]
        using (fun a b : ℕ => Nat.lt_trichotomy a b)
    simpa [atomRealize, natRel, total, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      BoundedFormula.Realize, Term.realize, Fin.snoc, r]
      using (h.map_sentence total).mp hn
  have hmax : ∀ a : N, ∃ b : N, r a b := by
    have hn : ℕ ⊨ noMax := by
      simpa [atomRealize, natRel, noMax, Sentence.Realize, FirstOrder.Language.Formula.Realize, Fin.snoc]
        using (fun a : ℕ => ⟨a + 1, Nat.lt_succ_self a⟩ : ∀ a : ℕ, ∃ b : ℕ, a < b)
    simpa [atomRealize, natRel, noMax, Sentence.Realize, FirstOrder.Language.Formula.Realize, Fin.snoc, r]
      using (h.map_sentence noMax).mp hn
  have horder : IsStrictTotalOrder N r :=
    { irrefl := hirr
      trans := htrans
      trichotomous := fun a b hab hba => ((htotal a b).resolve_left hab).resolve_right hba }
  have habove (n : ℕ) : r (h n) b := by
    simpa only [φRealize, Option.elim_some, Option.elim_none] using hb (φ n) ⟨n, rfl⟩
  have hout (n : ℕ) : h n ≠ b := by
    intro heq
    exact hirr b (heq ▸ habove n)
  have hS : binaryRelStructure N r = S := by
    apply Language.Structure.ext
    · funext n F
      exact F.elim
    · funext n R x
      cases R
      change Structure.RelMap (L := binaryRelLanguage) .rel ![x 0, x 1] =
        Structure.RelMap (L := binaryRelLanguage) .rel x
      congr 1
      funext i
      fin_cases i <;> rfl
  refine ⟨N, r, hcount, horder, hmax, ?_⟩
  rw [hS]
  exact ⟨h, b, habove, hout⟩

end
end Lemmatheca.Entry.DiagramsAndExtensions
