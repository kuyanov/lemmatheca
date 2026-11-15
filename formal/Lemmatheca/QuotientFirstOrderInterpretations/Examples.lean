import Lemmatheca.QuotientFirstOrderInterpretations.Core
import Lemmatheca.FiniteDimensionalFirstOrderInterpretations.Examples

namespace Lemmatheca.Entry.QuotientFirstOrderInterpretations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.QuotientInterpretations
open Lemmatheca.MathematicalLogic.QuotientInterpretations.InterpretationData
open Lemmatheca.Entry.FiniteDimensionalFirstOrderInterpretations (pairLanguage)
universe u v w
noncomputable section
variable {K : Language.{u,v}}

def redundantData (s : K.Functions 1) (p : K.Relations 1) :
    InterpretationData pairLanguage K 2 where
  tuple :=
    { positive := by decide
      domain := ⊤
      functionGraph := fun {n} f => by
        obtain ⟨hf⟩ := f
        cases hf
        exact (Term.var (.inr 0)).equal (.func s (fun _ => .var (.inl (0,0))))
      relationFormula := fun {n} R => match R with
        | .inl R => by
            obtain ⟨hR⟩ := R
            cases hR
            exact p.formula (fun _ => .var (0,0))
        | .inr .equality => (Term.var (0,0)).equal (.var (1,0)) }

variable (s : K.Functions 1) (p : K.Relations 1) {M : Type w} [K.Structure M]

private theorem redundant_e (a b : (redundantData s p).Domain M) :
    (redundantData s p).E M a b ↔ a.val 0 = b.val 0 := by
  simp only [E, equalityFormula, redundantData, Formula.realize_equal, Term.realize_var,
    coordinates, Lemmatheca.MathematicalLogic.FiniteDimensionalInterpretations.InterpretationData.coordinates]
  rfl

private theorem redundant_graph (a : Fin 1 → (redundantData s p).Domain M)
    (y : (redundantData s p).Domain M) :
    (redundantData s p).Graph M (⟨rfl⟩ : pairLanguage.Functions 1) a y ↔
      y.val 0 = Structure.funMap s (fun _ => (a 0).val 0) := by
  simp only [Graph, redundantData, Formula.realize_equal, Term.realize_var,
    Term.realize_func, Sum.elim_inl, Sum.elim_inr,
    coordinates, Lemmatheca.MathematicalLogic.FiniteDimensionalInterpretations.InterpretationData.coordinates]

private theorem redundant_relation (a : Fin 1 → (redundantData s p).Domain M) :
    (redundantData s p).Relation M (⟨rfl⟩ : pairLanguage.Relations 1) a ↔
      Structure.RelMap p (fun _ => (a 0).val 0) := by
  simp only [Relation, redundantData, Formula.realize_rel, Term.realize_var,
    coordinates, Lemmatheca.MathematicalLogic.FiniteDimensionalInterpretations.InterpretationData.coordinates]

theorem redundant_good [Nonempty M] : (redundantData s p).Good M := by
  refine {
    nonempty := ⟨⟨fun _ => Classical.ofNonempty, Formula.realize_top.mpr trivial⟩⟩
    reflexive := fun a => (redundant_e s p a a).mpr rfl
    symmetric := fun {a b} hab => (redundant_e s p b a).mpr ((redundant_e s p a b).mp hab).symm
    transitive := fun {a b c} hab hbc => (redundant_e s p a c).mpr
      (((redundant_e s p a b).mp hab).trans ((redundant_e s p b c).mp hbc))
    total := ?_
    unique := ?_
    graphs := ?_
    relations := ?_ }
  · intro n f a
    obtain ⟨hf⟩ := f
    cases hf
    refine ⟨⟨fun _ => Structure.funMap s (fun _ => (a 0).val 0),
      Formula.realize_top.mpr trivial⟩, ?_⟩
    exact (redundant_graph s p a _).mpr rfl
  · intro n f a y z hy hz
    obtain ⟨hf⟩ := f
    cases hf
    exact (redundant_e s p y z).mpr
      (((redundant_graph s p a y).mp hy).trans ((redundant_graph s p a z).mp hz).symm)
  · intro n f a b y z hab hyz
    obtain ⟨hf⟩ := f
    cases hf
    rw [redundant_graph, redundant_graph,
      (redundant_e s p y z).mp hyz, (redundant_e s p (a 0) (b 0)).mp (hab 0)]
  · intro n R a b hab
    obtain ⟨hR⟩ := R
    cases hR
    rw [redundant_relation, redundant_relation,
      (redundant_e s p (a 0) (b 0)).mp (hab 0)]

theorem redundant_equivalence (a b : (redundantData s p).Domain M) :
    (redundantData s p).E M a b ↔ a.val 0 = b.val 0 := by
  exact redundant_e s p a b

/-- The ambient source-language structure reads only the designated symbols s and p. -/
@[instance_reducible] def projectedStructure : pairLanguage.Structure M where
  funMap {n} f x := by
    obtain ⟨hf⟩ := f
    cases hf
    exact Structure.funMap s (fun _ => x 0)
  RelMap {n} R x := by
    obtain ⟨hR⟩ := R
    cases hR
    exact Structure.RelMap p (fun _ => x 0)

def firstCoordinate [Nonempty M] :
    (redundantData s p).QuotientDomain (redundant_good s p (M := M)) → M :=
  Quotient.lift (fun a : (redundantData s p).Domain M => a.val 0) (by
    intro a b hab
    apply (redundant_equivalence s p a b).mp
    exact hab)

def diagonalClass [Nonempty M] (a : M) :
    (redundantData s p).QuotientDomain (redundant_good s p (M := M)) :=
  (redundantData s p).projection (redundant_good s p (M := M))
    ⟨fun _ => a, Formula.realize_top.mpr trivial⟩

theorem firstCoordinate_projection [Nonempty M] (a : (redundantData s p).Domain M) :
    firstCoordinate s p ((redundantData s p).projection (redundant_good s p (M := M)) a) =
      a.val 0 := by
  rfl

theorem firstCoordinate_diagonal [Nonempty M] (a : M) :
    firstCoordinate s p (diagonalClass s p a) = a := by
  rfl

theorem diagonal_firstCoordinate [Nonempty M]
    (x : (redundantData s p).QuotientDomain (redundant_good s p (M := M))) :
    diagonalClass s p (firstCoordinate s p x) = x := by
  induction x using Quotient.inductionOn with
  | h a =>
    apply ((redundantData s p).projection_eq (redundant_good s p) _ a).mpr
    exact (redundant_equivalence s p _ a).mpr rfl

def firstCoordinateEquiv [Nonempty M] :
    (redundantData s p).QuotientDomain (redundant_good s p (M := M)) ≃ M where
  toFun := firstCoordinate s p
  invFun := diagonalClass s p
  left_inv := diagonal_firstCoordinate s p
  right_inv := firstCoordinate_diagonal s p

theorem firstCoordinate_isomorphism [Nonempty M] :
    letI := projectedStructure s p (M := M)
    ∃ e : (redundantData s p).QuotientDomain (redundant_good s p (M := M)) ≃[pairLanguage] M,
      e.toEquiv = firstCoordinateEquiv s p := by
  let := projectedStructure s p (M := M)
  refine ⟨{ toEquiv := firstCoordinateEquiv s p
            map_fun' := ?_
            map_rel' := ?_ }, rfl⟩
  · intro n f x
    obtain ⟨hf⟩ := f
    cases hf
    choose a ha using fun i => (redundantData s p).projection_surjective (redundant_good s p) (x i)
    have hx : (redundantData s p).projection (redundant_good s p) ∘ a = x := funext ha
    rw [← hx]
    let y : (redundantData s p).Domain M :=
      ⟨fun _ => Structure.funMap s (fun _ => (a 0).val 0), Formula.realize_top.mpr trivial⟩
    rw [(redundantData s p).quotient_function (redundant_good s p) _ a y
      ((redundant_graph s p a y).mpr rfl)]
    rfl
  · intro n R x
    obtain ⟨hR⟩ := R
    cases hR
    choose a ha using fun i => (redundantData s p).projection_surjective (redundant_good s p) (x i)
    have hx : (redundantData s p).projection (redundant_good s p) ∘ a = x := funext ha
    rw [← hx]
    change Structure.RelMap p (fun _ => (a 0).val 0) ↔
      Structure.RelMap (L := pairLanguage) (⟨rfl⟩ : pairLanguage.Relations 1)
        ((redundantData s p).projection (redundant_good s p) ∘ a)
    exact (redundant_relation s p a).symm.trans
      ((redundantData s p).quotient_relation (redundant_good s p) _ a).symm

def singleTerm : pairLanguage.Term Unit := .func ⟨rfl⟩ (fun _ => .var ())

def redundantSentence : pairLanguage.Sentence :=
  ((Relations.formula (⟨rfl⟩ : pairLanguage.Relations 1) (fun _ => singleTerm)).relabel
    (Sum.inr : Unit → Empty ⊕ Unit)).iAlls Unit

theorem redundant_sentence [Nonempty M] :
    M ⊨ (redundantData s p).translateSentence redundantSentence ↔
      ∀ a : M, Structure.RelMap p (fun _ => Structure.funMap s (fun _ => a)) := by
  let := projectedStructure s p (M := M)
  obtain ⟨e, _⟩ := firstCoordinate_isomorphism s p (M := M)
  rw [(redundantData s p).quotient_sentence_truth (redundant_good s p),
    StrongHomClass.realize_sentence e]
  change Formula.Realize redundantSentence (default : Empty → M) ↔ _
  simp only [redundantSentence, Formula.realize_iAlls, Formula.realize_relabel,
    Sum.elim_comp_inr, singleTerm]
  change (∀ x : Unit → M,
    Structure.RelMap p (fun _ => Structure.funMap s (fun _ => x ()))) ↔ _
  exact ⟨fun h a => h (fun _ => a), fun h x => h (x ())⟩

theorem nonunique_tuple_outputs [Nonempty M] (b c : M) (hbc : b ≠ c)
    (a : (redundantData s p).Domain M) :
    let y : Fin 2 → M := ![Structure.funMap s (fun _ => a.val 0), b]
    let z : Fin 2 → M := ![Structure.funMap s (fun _ => a.val 0), c]
    let G : (Fin 2 → M) → Prop := fun t =>
      ((redundantData s p).tuple.guardedGraph (⟨rfl⟩ : pairLanguage.Functions 1)).Realize
        (Sum.elim ((redundantData s p).coordinates M (fun _ => a)) t)
    y ≠ z ∧ G y ∧ G z ∧ ¬ ∃! t, G t := by
  dsimp only
  let y : Fin 2 → M := ![Structure.funMap s (fun _ => a.val 0), b]
  let z : Fin 2 → M := ![Structure.funMap s (fun _ => a.val 0), c]
  let G := fun t : Fin 2 → M =>
    ((redundantData s p).tuple.guardedGraph (⟨rfl⟩ : pairLanguage.Functions 1)).Realize
      (Sum.elim ((redundantData s p).coordinates M (fun _ => a)) t)
  have hg (t : Fin 2 → M) : G t ↔ t 0 = Structure.funMap s (fun _ => a.val 0) := by
    simp only [G, Lemmatheca.MathematicalLogic.FiniteDimensionalInterpretations.InterpretationData.guardedGraph,
      redundantData, Formula.realize_inf, Formula.realize_relabel, Formula.realize_top,
      true_and, Formula.realize_equal, Term.realize_var, Term.realize_func,
      Sum.elim_inl, Sum.elim_inr, coordinates,
      Lemmatheca.MathematicalLogic.FiniteDimensionalInterpretations.InterpretationData.coordinates]
  have hne : y ≠ z := fun he => hbc (congrFun he 1)
  have hy : G y := (hg y).mpr rfl
  have hz : G z := (hg z).mpr rfl
  refine ⟨hne,hy,hz,?_⟩
  rintro ⟨t,_,ht⟩
  exact hne ((ht y hy).trans (ht z hz).symm)

def equalityAtom : pairLanguage.Formula (Fin 2) := (Term.var 0).equal (.var 1)

theorem equality_counterexample [Nonempty M] (a b c : M) (hbc : b ≠ c) :
    let x : (redundantData s p).Domain M := ⟨![a,b], Formula.realize_top.mpr trivial⟩
    let y : (redundantData s p).Domain M := ⟨![a,c], Formula.realize_top.mpr trivial⟩
    x.val ≠ y.val ∧
      (redundantData s p).projection (redundant_good s p (M := M)) x =
        (redundantData s p).projection (redundant_good s p (M := M)) y ∧
      ((redundantData s p).translate equalityAtom).Realize
        ((redundantData s p).coordinates M ![x,y]) := by
  dsimp only
  let x : (redundantData s p).Domain M := ⟨![a,b], Formula.realize_top.mpr trivial⟩
  let y : (redundantData s p).Domain M := ⟨![a,c], Formula.realize_top.mpr trivial⟩
  have he : (redundantData s p).projection (redundant_good s p) x =
      (redundantData s p).projection (redundant_good s p) y := by
    apply ((redundantData s p).projection_eq (redundant_good s p) x y).mpr
    exact (redundant_equivalence s p x y).mpr rfl
  refine ⟨fun h => hbc (congrFun h 1), he, ?_⟩
  apply ((redundantData s p).quotient_formula_truth (redundant_good s p) equalityAtom ![x,y]).mpr
  exact he

end
end Lemmatheca.Entry.QuotientFirstOrderInterpretations
