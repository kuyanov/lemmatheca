import Lemmatheca.HomomorphismsAndPositiveFormulas.Preservation
import Lemmatheca.FirstOrderStructures.BasicStructures

/-! Concrete graph maps, their shared-syntax formulas, and the nullary-function condition. -/
namespace Lemmatheca.Entry.HomomorphismsAndPositiveFormulas
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.MathematicalLogic.BasicStructures
open Lemmatheca.ModelTheory.PositiveHomomorphisms

inductive EdgeVertex | zero | one deriving DecidableEq, Inhabited
inductive LoopVertex | star deriving DecidableEq, Inhabited
inductive NoLoopVertex | star deriving DecidableEq, Inhabited
inductive EdgelessPair | zero | one deriving DecidableEq, Inhabited
inductive EdgelessPoint | star deriving DecidableEq, Inhabited
inductive LoopAndIsolated | loop | isolated deriving DecidableEq, Inhabited

instance edgeStructure : binaryRelLanguage.Structure EdgeVertex :=
  binaryRelStructure EdgeVertex (fun a b => a = .zero ∧ b = .one)
instance loopStructure : binaryRelLanguage.Structure LoopVertex :=
  binaryRelStructure LoopVertex (fun _ _ => True)
instance noLoopStructure : binaryRelLanguage.Structure NoLoopVertex :=
  binaryRelStructure NoLoopVertex (fun _ _ => False)
instance edgelessPairStructure : binaryRelLanguage.Structure EdgelessPair :=
  binaryRelStructure EdgelessPair (fun _ _ => False)
instance edgelessPointStructure : binaryRelLanguage.Structure EdgelessPoint :=
  binaryRelStructure EdgelessPoint (fun _ _ => False)
instance loopAndIsolatedStructure : binaryRelLanguage.Structure LoopAndIsolated :=
  binaryRelStructure LoopAndIsolated (fun a b => a = .loop ∧ b = .loop)

def edgeAtom : binaryRelLanguage.Formula (Fin 2) :=
  strictRel.formula₂ (.var 0) (.var 1)
def equalityAtom : binaryRelLanguage.Formula (Fin 2) :=
  (Term.var 0 : binaryRelLanguage.Term (Fin 2)).equal (.var 1)
def inequality : binaryRelLanguage.Formula (Fin 2) := equalityAtom.not

def edgeCollapse : EdgeVertex → LoopVertex := fun _ => .star
def addLoop : NoLoopVertex → LoopVertex := fun _ => .star
def edgelessCollapse : EdgelessPair → EdgelessPoint := fun _ => .star
def loopInclusion : LoopVertex → LoopAndIsolated := fun _ => .loop

private theorem no_positive_equivalent {A B : Type} [binaryRelLanguage.Structure A]
    [binaryRelLanguage.Structure B] [Nonempty A] [Nonempty B]
    (h : A →[binaryRelLanguage] B) (σ : binaryRelLanguage.Sentence)
    (ha : A ⊨ σ) (hb : ¬B ⊨ σ) :
    ¬∃ θ : binaryRelLanguage.Sentence, IsExistentialPositive θ ∧
      (∅ : binaryRelLanguage.Theory) ⊨ᵇ (σ.iff θ) := by
  rintro ⟨θ,hθ,heq⟩
  have hea : A ⊨ σ ↔ A ⊨ θ := by
    exact (Formula.realize_iff).mp (heq.realize_formula A)
  have heb : B ⊨ σ ↔ B ⊨ θ := by
    exact (Formula.realize_iff).mp (heq.realize_formula B)
  have ht := hom_preserves_positive h hθ (default : Empty → A) (default : Fin 0 → A) (hea.mp ha)
  apply hb
  apply heb.mpr
  simpa only [Sentence.Realize, Formula.Realize,
    Subsingleton.elim (h ∘ (default : Empty → A)) (default : Empty → B),
    Subsingleton.elim (h ∘ (default : Fin 0 → A)) (default : Fin 0 → B)] using ht

theorem edge_collapse_example :
    (∃ h : EdgeVertex →[binaryRelLanguage] LoopVertex,
      (h : EdgeVertex → LoopVertex) = edgeCollapse) ∧
    inequality.Realize ![EdgeVertex.zero, EdgeVertex.one] ∧
    ¬inequality.Realize (edgeCollapse ∘ ![EdgeVertex.zero, EdgeVertex.one]) ∧
    edgeAtom.not.Realize ![EdgeVertex.zero, EdgeVertex.zero] ∧
    ¬edgeAtom.not.Realize (edgeCollapse ∘ ![EdgeVertex.zero, EdgeVertex.zero]) := by
  let h : EdgeVertex →[binaryRelLanguage] LoopVertex := {
    toFun := edgeCollapse
    map_fun' := fun f _ => Empty.elim f
    map_rel' := by intro n r xs hx; cases r; trivial }
  refine ⟨⟨h,rfl⟩, ?_, ?_, ?_, ?_⟩
  · change EdgeVertex.zero ≠ EdgeVertex.one; decide
  · change ¬ (LoopVertex.star ≠ LoopVertex.star); simp
  · change ¬ (EdgeVertex.zero = .zero ∧ EdgeVertex.zero = .one); simp
  · change ¬¬ True; simp

theorem injective_nonreflecting_example :
    (∃ h : NoLoopVertex →[binaryRelLanguage] LoopVertex,
      (h : NoLoopVertex → LoopVertex) = addLoop) ∧
    Function.Injective addLoop ∧
    ¬∃ e : NoLoopVertex ↪[binaryRelLanguage] LoopVertex,
      (e : NoLoopVertex → LoopVertex) = addLoop := by
  let h : NoLoopVertex →[binaryRelLanguage] LoopVertex := {
    toFun := addLoop
    map_fun' := fun f _ => Empty.elim f
    map_rel' := by intro n r xs hx; cases r; trivial }
  refine ⟨⟨h,rfl⟩, ?_, ?_⟩
  · intro x y _; cases x; cases y; rfl
  · rintro ⟨e, he⟩
    have bad := (e.map_rel strictRel (fun _ => NoLoopVertex.star)).mp (by trivial)
    exact bad

/-- The quantified variable is the intermediate vertex; the endpoints stay free. -/
def walkTwo : binaryRelLanguage.Formula (Fin 2) :=
  ((strictRel.boundedFormula₂ (.var (.inl 0)) (.var (.inr 0))) ⊓
    (strictRel.boundedFormula₂ (.var (.inr 0)) (.var (.inl 1)))).ex

def walkSentence : binaryRelLanguage.Sentence :=
  ((strictRel.boundedFormula₂ (.var (.inr 0)) (.var (.inr 1))) ⊓
    (strictRel.boundedFormula₂ (.var (.inr 1)) (.var (.inr 2)))).ex.ex.ex

def twoVertices : binaryRelLanguage.Sentence :=
  ((.var (.inr 0) : binaryRelLanguage.Term (Empty ⊕ Fin 2)).bdEqual
    (.var (.inr 1))).not.ex.ex

def everyOutgoing : binaryRelLanguage.Sentence :=
  (strictRel.boundedFormula₂ (.var (.inr 0)) (.var (.inr 1))).ex.all

theorem walkTwo_semantics {V : Type*} [binaryRelLanguage.Structure V] (a : Fin 2 → V) :
    walkTwo.Realize a ↔
      ∃ z : V, Structure.RelMap strictRel ![a 0, z] ∧
        Structure.RelMap strictRel ![z, a 1] := by
  simp [walkTwo, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_rel₂, Term.realize, Fin.snoc]

theorem walkSentence_semantics {V : Type*} [binaryRelLanguage.Structure V] :
    V ⊨ walkSentence ↔
      ∃ x y z : V, Structure.RelMap strictRel ![x, y] ∧
        Structure.RelMap strictRel ![y, z] := by
  simp [walkSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_rel₂, Term.realize, Fin.snoc]

theorem graph_example_formulas :
    IsExistentialPositive walkTwo ∧ IsExistentialPositive walkSentence ∧
      HomPreserved.{0, 0, 0} walkSentence ∧ LoopVertex ⊨ walkSentence := by
  have hw : IsExistentialPositive walkTwo :=
    .ex (.inf (.atomic (.rel _ _)) (.atomic (.rel _ _)))
  have hs : IsExistentialPositive walkSentence :=
    .ex (.ex (.ex (.inf (.atomic (.rel _ _)) (.atomic (.rel _ _)))))
  refine ⟨hw, hs, ?_, ?_⟩
  · intro M N f hm
    have hf := hom_preserves_positive f hs (default : Empty → M) (default : Fin 0 → M) hm
    simpa only [Sentence.Realize, Formula.Realize,
      Subsingleton.elim (f ∘ (default : Empty → M)) (default : Empty → N),
      Subsingleton.elim (f ∘ (default : Fin 0 → M)) (default : Fin 0 → N)] using hf
  · exact walkSentence_semantics.mpr ⟨.star, .star, .star, trivial, trivial⟩

theorem edgeless_collapse_counterexample :
    (∃ h : EdgelessPair →[binaryRelLanguage] EdgelessPoint,
      (h : EdgelessPair → EdgelessPoint) = edgelessCollapse) ∧
    EdgelessPair ⊨ twoVertices ∧ ¬EdgelessPoint ⊨ twoVertices ∧
    ¬∃ θ : binaryRelLanguage.Sentence, IsExistentialPositive θ ∧
      (∅ : binaryRelLanguage.Theory) ⊨ᵇ (twoVertices.iff θ) := by
  let h : EdgelessPair →[binaryRelLanguage] EdgelessPoint := {
    toFun := edgelessCollapse
    map_fun' := fun f _ => Empty.elim f
    map_rel' := by intro n r xs hx; cases r; exact hx }
  have ha : EdgelessPair ⊨ twoVertices := by
    simp only [twoVertices, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex]
    change ∃ x y : EdgelessPair, x ≠ y
    exact ⟨.zero, .one, by decide⟩
  have hb : ¬EdgelessPoint ⊨ twoVertices := by
    simp only [twoVertices, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex]
    change ¬∃ x y : EdgelessPoint, x ≠ y
    rintro ⟨x,y,hxy⟩
    cases x; cases y; exact hxy rfl
  refine ⟨⟨h,rfl⟩, ha, hb, ?_⟩
  exact no_positive_equivalent h twoVertices ha hb

theorem outgoing_edge_counterexample :
    (∃ h : LoopVertex →[binaryRelLanguage] LoopAndIsolated,
      (h : LoopVertex → LoopAndIsolated) = loopInclusion) ∧
    LoopVertex ⊨ everyOutgoing ∧ ¬LoopAndIsolated ⊨ everyOutgoing ∧
    ¬∃ θ : binaryRelLanguage.Sentence, IsExistentialPositive θ ∧
      (∅ : binaryRelLanguage.Theory) ⊨ᵇ (everyOutgoing.iff θ) := by
  let h : LoopVertex →[binaryRelLanguage] LoopAndIsolated := {
    toFun := loopInclusion
    map_fun' := fun f _ => Empty.elim f
    map_rel' := by intro n r xs hx; cases r; exact ⟨rfl,rfl⟩ }
  have ha : LoopVertex ⊨ everyOutgoing := by
    simp only [everyOutgoing, Sentence.Realize, Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_ex]
    change ∀ x : LoopVertex, ∃ y : LoopVertex, True
    intro x; exact ⟨.star,trivial⟩
  have hb : ¬LoopAndIsolated ⊨ everyOutgoing := by
    simp only [everyOutgoing, Sentence.Realize, Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_ex]
    change ¬∀ x : LoopAndIsolated, ∃ y : LoopAndIsolated, x = .loop ∧ y = .loop
    intro hbad
    obtain ⟨y,hy,_⟩ := hbad .isolated
    cases hy
  refine ⟨⟨h,rfl⟩, ha, hb, ?_⟩
  exact no_positive_equivalent h everyOutgoing ha hb

inductive SuccessorSymbol : ℕ → Type
  | succ : SuccessorSymbol 1
def successorOnlyLanguage : Language := ⟨SuccessorSymbol, fun _ => Empty⟩
instance successorOnlyStructure : successorOnlyLanguage.Structure ℕ where
  funMap f xs := match f with | .succ => xs 0 + 1
  RelMap r _ := r.elim

def equalsZero : naturalSuccessorLanguage.Formula (Fin 1) :=
  (Term.var 0 : naturalSuccessorLanguage.Term (Fin 1)).equal
    (.func NaturalFunctionSymbol.zero Fin.elim0)

theorem successor_constant_counterexample :
    (∀ n : ℕ, Nat.succ (n + 1) = Nat.succ n + 1) ∧
    (¬∃ h : ℕ →[naturalSuccessorLanguage] ℕ, (h : ℕ → ℕ) = Nat.succ) ∧
    equalsZero.Realize ![0] ∧ ¬equalsZero.Realize ![1] ∧
    (∃ h : ℕ →[successorOnlyLanguage] ℕ, (h : ℕ → ℕ) = Nat.succ) := by
  refine ⟨fun n => rfl, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h,heq⟩
    have hz := h.map_fun NaturalFunctionSymbol.zero Fin.elim0
    change h 0 = 0 at hz
    rw [heq] at hz
    exact Nat.one_ne_zero hz
  · change (0 : ℕ) = 0; rfl
  · change ¬((1 : ℕ) = 0); decide
  · refine ⟨{toFun := Nat.succ, map_fun' := ?_, map_rel' := ?_},rfl⟩
    · intro n f xs
      cases f
      rfl
    · intro n r xs hx
      exact Empty.elim r

end Lemmatheca.Entry.HomomorphismsAndPositiveFormulas
