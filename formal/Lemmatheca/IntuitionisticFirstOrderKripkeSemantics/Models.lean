import Lemmatheca.IntuitionisticFirstOrderDeduction.Soundness
import Lemmatheca.IntuitionisticKripkeSemantics.Models

/-! Varying-domain models with coherent homomorphisms.  Equality is literal
value equality; transition maps need neither injectivity nor reflection. -/
namespace Lemmatheca.ProofTheory.FirstOrder.Kripke
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w d a b

/-- A nonempty preordered diagram of nonempty structures and homomorphisms. -/
structure Model (L : Language.{u,v}) (W : Type w) [Preorder W] where
  world_nonempty : Nonempty W
  Domain : W → Type d
  domain_nonempty : ∀ w, Nonempty (Domain w)
  structureAt : ∀ w, L.Structure (Domain w)
  map : ∀ {w z : W}, w ≤ z →
    @Language.Hom L (Domain w) (Domain z) (structureAt w) (structureAt z)
  map_refl : ∀ w (x : Domain w), map (le_refl w) x = x
  map_trans : ∀ {w z t : W} (hwz : w ≤ z) (hzt : z ≤ t) (x : Domain w),
    map hzt (map hwz x) = map (le_trans hwz hzt) x

variable {L : Language.{u,v}} {W : Type w} [Preorder W]

/-- Transport every assigned value by the supplied transition homomorphism. -/
def Model.transport (K : Model.{u,v,w,d} L W) {w z : W} (h : w ≤ z)
    {α : Type a} (s : α → K.Domain w) : α → K.Domain z := K.map h ∘ s

/-- The ordinary term value in the specified world's actual structure. -/
def Model.termValue (K : Model.{u,v,w,d} L W) (w : W) {α : Type a}
    (s : α → K.Domain w) (t : L.Term α) : K.Domain w :=
  letI := K.structureAt w
  t.realize s

/-- Recursive forcing of the actual primitive full syntax. -/
def Forces (K : Model.{u,v,w,d} L W) {α : Type a} :
    ∀ {n}, BoundedFormula L α n → (w : W) → (α ⊕ Fin n → K.Domain w) → Prop
  | _, .falsum, _, _ => False
  | _, .equal s t, w, a => K.termValue w a s = K.termValue w a t
  | _, .rel R ts, w, a =>
      @Structure.RelMap L (K.Domain w) (K.structureAt w) _ R (fun i => K.termValue w a (ts i))
  | _, .neg A, w, a => ∀ z (h : w ≤ z), ¬ Forces K A z (K.transport h a)
  | _, .conj A B, w, a => Forces K A w a ∧ Forces K B w a
  | _, .disj A B, w, a => Forces K A w a ∨ Forces K B w a
  | _, .impl A B, w, a => ∀ z (h : w ≤ z),
      Forces K A z (K.transport h a) → Forces K B z (K.transport h a)
  | _, .all A, w, a => ∀ z (h : w ≤ z) (x : K.Domain z),
      Forces K A z (extendAssignment (K.transport h a) x)
  | _, .ex A, w, a => ∃ x : K.Domain w, Forces K A w (extendAssignment a x)

/-- Forcing of a complete formula at its original free-name assignment. -/
def Holds (K : Model.{u,v,w,d} L W) (w : W) {α : Type a}
    (A : Formula L α) (s : α → K.Domain w) : Prop := Forces K A w (Sum.elim s Fin.elim0)

/-- Forcing every member of a possibly infinite allowed premise set. -/
def ForcesContext (K : Model.{u,v,w,d} L W) (w : W) {α : Type a}
    (T : Set (Formula L α)) (s : α → K.Domain w) : Prop := ∀ A ∈ T, Holds K w A s

/-- A specified assignment forcing the premises and failing to force the conclusion. -/
def Countermodel (K : Model.{u,v,w,d} L W) (w : W) {α : Type a}
    (T : Set (Formula L α)) (A : Formula L α) (s : α → K.Domain w) : Prop :=
  ForcesContext K w T s ∧ ¬ Holds K w A s

/-- Consequence over all world sets and model diagrams in the indicated universes. -/
def Entails {α : Type a} (T : Set (Formula L α)) (A : Formula L α) : Prop :=
  ∀ (X : Type w) [Preorder X] (K : Model.{u,v,w,d} L X) (x : X) (s : α → K.Domain x),
    ForcesContext K x T s → Holds K x A s

/-- Kripke validity is consequence from the empty premise set. -/
def Valid {α : Type a} (A : Formula L α) : Prop := Entails.{u,v,w,d} ∅ A

end Lemmatheca.ProofTheory.FirstOrder.Kripke
