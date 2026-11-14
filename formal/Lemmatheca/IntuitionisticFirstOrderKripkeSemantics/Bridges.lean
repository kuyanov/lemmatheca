import Lemmatheca.IntuitionisticFirstOrderKripkeSemantics.Soundness

namespace Lemmatheca.ProofTheory.FirstOrder.Kripke
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.MathematicalLogic.Propositional
universe u v w d a p
variable {L : Language.{u,v}} {W : Type w} [Preorder W]

/-- The given classical structure is repeated at the sole world. -/
def singleton (L : Language.{u,v}) (M : Type d) [L.Structure M] [Nonempty M] :
    Model.{u,v,w,d} L PUnit.{w+1} where
  world_nonempty := inferInstance
  Domain _ := M
  domain_nonempty _ := inferInstance
  structureAt _ := inferInstance
  map _ := Language.Hom.id L M
  map_refl _ _ := rfl
  map_trans _ _ _ := rfl

private theorem singleton_transport (M : Type d) [L.Structure M] [Nonempty M]
    {α : Type a} {x y : PUnit.{w+1}} (h : x ≤ y) (s : α → M) :
    (singleton L M).transport h s = s := rfl

theorem singleton_forcing (M : Type d) [L.Structure M] [Nonempty M] {α : Type a} {n}
    (A : BoundedFormula L α n) (x : PUnit.{w+1}) (s : α ⊕ Fin n → M) :
    Forces (singleton L M) A x s ↔ A.realize s := by
  induction A generalizing x with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | neg A ih =>
      constructor
      · intro h hA
        have hp := h x le_rfl
        rw [singleton_transport] at hp
        exact hp ((ih x s).mpr hA)
      · intro h z hz hp
        rw [singleton_transport] at hp
        exact h ((ih z s).mp hp)
  | conj A B ihA ihB => exact and_congr (ihA x s) (ihB x s)
  | disj A B ihA ihB => exact or_congr (ihA x s) (ihB x s)
  | impl A B ihA ihB =>
      constructor
      · intro h hA
        have hp := h x le_rfl
        rw [singleton_transport] at hp
        exact (ihB x s).mp (hp ((ihA x s).mpr hA))
      · intro h z hz hp
        rw [singleton_transport] at hp ⊢
        exact (ihB z s).mpr (h ((ihA z s).mp hp))
  | all A ih =>
      constructor
      · intro h m
        have hp := h x le_rfl m
        rw [singleton_transport] at hp
        exact (ih x (extendAssignment s m)).mp hp
      · intro h z hz m
        rw [singleton_transport]
        exact (ih z (extendAssignment s m)).mpr (h m)
  | ex A ih => exact exists_congr (fun m => ih x (extendAssignment s m))

theorem valid_classical {α : Type a} (A : Formula L α) (h : Valid.{u,v,w,d} A)
    (M : Type d) [L.Structure M] [Nonempty M] (s : α → M) :
    A.Realize s Fin.elim0 := by
  have hp := h PUnit.{w+1} (singleton L M) PUnit.unit s (by simp [ForcesContext])
  exact (singleton_forcing M A PUnit.unit (Sum.elim s Fin.elim0)).mp hp

/-- Retain the frame and evaluate each nullary relation at its empty tuple. -/
def reduct (K : Model.{u,v,w,d} L W) :
    Lemmatheca.ProofTheory.Intuitionistic.Kripke.Model (L.Relations 0) W where
  world_nonempty := K.world_nonempty
  valuation w R := @Structure.RelMap L (K.Domain w) (K.structureAt w) 0 R Fin.elim0
  persistent := by
    intro w z h R hp
    let instw : L.Structure (K.Domain w) := K.structureAt w
    let instz : L.Structure (K.Domain z) := K.structureAt z
    have hm := (K.map h).map_rel' R Fin.elim0 hp
    have he : ((K.map h).toFun ∘ (Fin.elim0 : Fin 0 → K.Domain w)) = Fin.elim0 :=
      Subsingleton.elim _ _
    simpa only [he] using hm

/-- Include the actual native propositional constructors using the supplied nullary atoms. -/
def includePropositional {P : Type p} (ρ : P → L.Relations 0) {α : Type a} {n} :
    PropFormula P → BoundedFormula L α n
  | .atom x => .rel (ρ x) Fin.elim0
  | .falsum => .falsum
  | .neg A => .neg (includePropositional ρ A)
  | .conj A B => .conj (includePropositional ρ A) (includePropositional ρ B)
  | .disj A B => .disj (includePropositional ρ A) (includePropositional ρ B)
  | .impl A B => .impl (includePropositional ρ A) (includePropositional ρ B)

theorem reduct_forcing (K : Model.{u,v,w,d} L W) (A : PropFormula (L.Relations 0))
    {α : Type a} {n} (w : W) (s : α ⊕ Fin n → K.Domain w) :
    Forces K (includePropositional id A) w s ↔
      Lemmatheca.ProofTheory.Intuitionistic.Kripke.Forces (reduct K) w A := by
  induction A generalizing w with
  | atom R =>
      apply Iff.of_eq
      change @Structure.RelMap L (K.Domain w) (K.structureAt w) 0 R _ =
        @Structure.RelMap L (K.Domain w) (K.structureAt w) 0 R _
      congr 1
      funext i
      exact Fin.elim0 i
  | falsum => rfl
  | neg A ih => simp only [includePropositional, Forces,
      Lemmatheca.ProofTheory.Intuitionistic.Kripke.Forces, ih]
  | conj A B ihA ihB => exact and_congr (ihA w s) (ihB w s)
  | disj A B ihA ihB => exact or_congr (ihA w s) (ihB w s)
  | impl A B ihA ihB => simp only [includePropositional, Forces,
      Lemmatheca.ProofTheory.Intuitionistic.Kripke.Forces, ihA, ihB]

inductive NullaryRelation (P : Type p) : ℕ → Type p
  | atom : P → NullaryRelation P 0

/-- The relational language with exactly the supplied propositional atoms. -/
def propositionalLanguage (P : Type p) : Language.{0,p} :=
  ⟨fun _ => Empty, NullaryRelation P⟩

@[instance_reducible]
def propositionalStructure {P : Type p}
    (M : Lemmatheca.ProofTheory.Intuitionistic.Kripke.Model P W) (w : W) :
    (propositionalLanguage P).Structure PUnit.{1} where
  funMap := fun f => f.elim
  RelMap := fun R _ => match R with | .atom x => M.valuation w x

/-- A propositional model is realized on a fixed one-element first-order domain. -/
def liftPropositional {P : Type p}
    (M : Lemmatheca.ProofTheory.Intuitionistic.Kripke.Model P W) :
    Model.{0,p,w,0} (propositionalLanguage P) W where
  world_nonempty := M.world_nonempty
  Domain _ := PUnit
  domain_nonempty _ := inferInstance
  structureAt := propositionalStructure M
  map := fun {w z} h => @Language.Hom.mk _ _ _
    (propositionalStructure M w) (propositionalStructure M z) id
    (by intro n f; exact f.elim) (by
      intro n R xs hx
      cases R with
      | atom x => exact M.persistent h x hx)
  map_refl _ _ := rfl
  map_trans _ _ _ := rfl

theorem liftPropositional_forcing {P : Type p}
    (M : Lemmatheca.ProofTheory.Intuitionistic.Kripke.Model P W) (A : PropFormula P)
    {α : Type a} {n} (w : W) (s : α ⊕ Fin n → (liftPropositional M).Domain w) :
    Forces (liftPropositional M) (includePropositional NullaryRelation.atom A) w s ↔
      Lemmatheca.ProofTheory.Intuitionistic.Kripke.Forces M w A := by
  induction A generalizing w with
  | atom x => rfl
  | falsum => rfl
  | neg A ih => simp only [includePropositional, Forces,
      Lemmatheca.ProofTheory.Intuitionistic.Kripke.Forces, ih]
  | conj A B ihA ihB => exact and_congr (ihA w s) (ihB w s)
  | disj A B ihA ihB => exact or_congr (ihA w s) (ihB w s)
  | impl A B ihA ihB => simp only [includePropositional, Forces,
      Lemmatheca.ProofTheory.Intuitionistic.Kripke.Forces, ihA, ihB]

end Lemmatheca.ProofTheory.FirstOrder.Kripke
