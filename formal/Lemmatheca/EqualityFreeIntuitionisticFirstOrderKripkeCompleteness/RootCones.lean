import Lemmatheca.IntuitionisticFirstOrderKripkeSemantics.Operations

namespace Lemmatheca.ProofTheory.FirstOrder.KripkeCompleteness
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w d a
variable {L : Language.{u,v}} {W : Type w} [Preorder W]
variable (K : Kripke.Model.{u,v,w,d} L W) (root : W)

abbrev Cone := {z : W // root ≤ z}

def coneRoot : Cone root := ⟨root,le_refl root⟩

def coneModel : Kripke.Model.{u,v,w,d} L (Cone root) where
  world_nonempty := ⟨coneRoot root⟩
  Domain := fun z => K.Domain z.val
  domain_nonempty := fun z => K.domain_nonempty z.val
  structureAt := fun z => K.structureAt z.val
  map := fun h => K.map h
  map_refl := fun z x => K.map_refl z.val x
  map_trans := fun h k x => K.map_trans h k x

theorem cone_least (z : Cone root) : coneRoot root ≤ z := by
  exact z.property

theorem cone_forces {α : Type a} {n : ℕ} (A : BoundedFormula L α n)
    (z : Cone root) (s : α ⊕ Fin n → K.Domain z.val) :
    Kripke.Forces (coneModel K root) A z s ↔ Kripke.Forces K A z.val s := by
  induction A generalizing z with
  | falsum => rfl
  | equal t q => rfl
  | rel R ts => rfl
  | neg A ih =>
      constructor
      · intro hf t hzt ht
        exact hf ⟨t,le_trans z.property hzt⟩ hzt
          ((ih ⟨t,le_trans z.property hzt⟩ (K.transport hzt s)).mpr ht)
      · intro hf t hzt ht
        exact hf t.val hzt ((ih t ((coneModel K root).transport hzt s)).mp ht)
  | conj A B ihA ihB => exact and_congr (ihA z s) (ihB z s)
  | disj A B ihA ihB => exact or_congr (ihA z s) (ihB z s)
  | impl A B ihA ihB =>
      constructor
      · intro hf t hzt ht
        exact (ihB ⟨t,le_trans z.property hzt⟩ (K.transport hzt s)).mp
          (hf ⟨t,le_trans z.property hzt⟩ hzt
            ((ihA ⟨t,le_trans z.property hzt⟩ (K.transport hzt s)).mpr ht))
      · intro hf t hzt ht
        exact (ihB t ((coneModel K root).transport hzt s)).mpr
          (hf t.val hzt ((ihA t ((coneModel K root).transport hzt s)).mp ht))
  | all A ih =>
      constructor
      · intro hf t hzt x
        exact (ih ⟨t,le_trans z.property hzt⟩ (extendAssignment (K.transport hzt s) x)).mp
          (hf ⟨t,le_trans z.property hzt⟩ hzt x)
      · intro hf t hzt x
        exact (ih t (extendAssignment ((coneModel K root).transport hzt s) x)).mpr
          (hf t.val hzt x)
  | ex A ih =>
      constructor
      · rintro ⟨x,hx⟩
        exact ⟨x,(ih z (extendAssignment s x)).mp hx⟩
      · rintro ⟨x,hx⟩
        exact ⟨x,(ih z (extendAssignment s x)).mpr hx⟩

theorem cone_countermodel {α : Type a} (Γ : Set (Formula L α)) (A : Formula L α)
    (s : α → K.Domain root) (h : Kripke.Countermodel K root Γ A s) :
    Kripke.Countermodel (coneModel K root) (coneRoot root) Γ A s := by
  constructor
  · intro B hB
    exact (cone_forces K root B (coneRoot root) (Sum.elim s Fin.elim0)).mpr (h.1 B hB)
  · intro hA
    exact h.2 ((cone_forces K root A (coneRoot root) (Sum.elim s Fin.elim0)).mp hA)

end Lemmatheca.ProofTheory.FirstOrder.KripkeCompleteness
