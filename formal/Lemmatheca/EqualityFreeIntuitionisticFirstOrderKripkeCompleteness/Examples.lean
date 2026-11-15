import Lemmatheca.EqualityFreeIntuitionisticFirstOrderKripkeCompleteness.Consequences
import Lemmatheca.EqualityFreeIntuitionisticFirstOrderKripkeCompleteness.RootCones

namespace Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderKripkeCompleteness
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder
universe w d
noncomputable section

inductive OrderRelation : ℕ → Type
  | lt : OrderRelation 2

/-- Exactly one binary relation symbol and no function symbols. -/
def orderLanguage : Language where
  Functions := fun _ => Empty
  Relations := OrderRelation

def relation : orderLanguage.Relations 2 := .lt

def atom {n : ℕ} (i j : Fin n) : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula orderLanguage Empty n :=
  .rel relation (fun k => .var (.inr (if k = 0 then i else j)))

def irreflexive : Lemmatheca.ProofTheory.FirstOrder.Formula orderLanguage Empty := .all (.neg (atom 0 0))

def transitive : Lemmatheca.ProofTheory.FirstOrder.Formula orderLanguage Empty :=
  .all (.all (.all (.impl (.conj (atom 0 1) (atom 1 2)) (atom 0 2))))

def serial : Lemmatheca.ProofTheory.FirstOrder.Formula orderLanguage Empty := .all (.ex (atom 0 1))

local instance exampleFormulaDecidable : DecidableEq (Lemmatheca.ProofTheory.FirstOrder.Formula orderLanguage Empty) := Classical.decEq _

def premises : Finset (Lemmatheca.ProofTheory.FirstOrder.Formula orderLanguage Empty) := {irreflexive,transitive,serial}

theorem premises_equalityFree : ∀ A ∈ premises, A.EqualityFree := by
  intro A hA
  simp only [premises,Finset.mem_insert,Finset.mem_singleton] at hA
  rcases hA with rfl | rfl | rfl <;> trivial

@[instance_reducible]
def natStructure : orderLanguage.Structure ℕ where
  funMap := fun f => nomatch f
  RelMap := fun R xs => match R with | .lt => xs 0 < xs 1

/-- A single-world frame, with the usual strict natural-number relation. -/
def natModel : Kripke.Model.{0,0,0,0} orderLanguage (Fin 1) where
  world_nonempty := ⟨0⟩
  Domain := fun _ => ℕ
  domain_nonempty := fun _ => ⟨0⟩
  structureAt := fun _ => natStructure
  map := fun _ => @Language.Hom.mk _ _ _ natStructure natStructure id
    (fun {_} f => f.elim) (fun _ _ h => h)
  map_refl := fun _ x => Eq.refl x
  map_trans := fun _ _ x => Eq.refl x

@[simp] private theorem slot_1_0 {M : Type*} (x : M) (f : Fin 0 → M) :
    Fin.lastCases x f (0 : Fin 1) = x := Fin.lastCases_last

@[simp] private theorem slot_2_0 {M : Type*} (x : M) (f : Fin 1 → M) :
    Fin.lastCases x f (0 : Fin 2) = f 0 := Fin.lastCases_castSucc (0 : Fin 1)

@[simp] private theorem slot_2_1 {M : Type*} (x : M) (f : Fin 1 → M) :
    Fin.lastCases x f (1 : Fin 2) = x := Fin.lastCases_last

@[simp] private theorem slot_3_0 {M : Type*} (x : M) (f : Fin 2 → M) :
    Fin.lastCases x f (0 : Fin 3) = f 0 := Fin.lastCases_castSucc (0 : Fin 2)

@[simp] private theorem slot_3_1 {M : Type*} (x : M) (f : Fin 2 → M) :
    Fin.lastCases x f (1 : Fin 3) = f 1 := Fin.lastCases_castSucc (1 : Fin 2)

@[simp] private theorem slot_3_2 {M : Type*} (x : M) (f : Fin 2 → M) :
    Fin.lastCases x f (2 : Fin 3) = x := Fin.lastCases_last

theorem natModel_forces :
    Kripke.ForcesContext natModel 0 (↑premises : Set (Lemmatheca.ProofTheory.FirstOrder.Formula orderLanguage Empty)) Empty.elim := by
  intro A hA
  simp only [Finset.mem_coe,premises,Finset.mem_insert,Finset.mem_singleton] at hA
  rcases hA with rfl | rfl | rfl
  · simp [irreflexive,atom,Kripke.Holds,Kripke.Forces,Kripke.Model.termValue,natModel,natStructure,relation,
      Kripke.Model.transport,extendAssignment]
    intro x hx
    change x < x at hx
    exact Nat.lt_irrefl x hx
  · simp [transitive,atom,Kripke.Holds,Kripke.Forces,Kripke.Model.termValue,natModel,natStructure,relation,
      Kripke.Model.transport,extendAssignment]
    exact fun x y z hxy hyz => lt_trans hxy hyz
  · simp [serial,atom,Kripke.Holds,Kripke.Forces,Kripke.Model.termValue,natModel,natStructure,relation,
      Kripke.Model.transport,extendAssignment]
    exact fun x => ⟨x+1,Nat.lt_succ_self x⟩

theorem premises_consistent :
    ¬NaturalDeduction.TheoryDerives false false orderLanguage
      (↑premises : Set (Lemmatheca.ProofTheory.FirstOrder.Formula orderLanguage Empty)) .falsum := by
  exact Kripke.countermodel_not_derivable natModel 0 Empty.elim ⟨natModel_forces,False.elim⟩

private def presentR {W : Type w} [Preorder W]
    (K : Kripke.Model.{0,0,w,d} orderLanguage W) (z : W) (x y : K.Domain z) : Prop :=
  @Structure.RelMap orderLanguage (K.Domain z) (K.structureAt z) 2 relation
    (fun k => if k = 0 then x else y)

private theorem forces_atom {W : Type w} [Preorder W]
    (K : Kripke.Model.{0,0,w,d} orderLanguage W) (z : W) {n} (i j : Fin n)
    (s : Empty ⊕ Fin n → K.Domain z) :
    Kripke.Forces K (atom i j) z s ↔ presentR K z (s (.inr i)) (s (.inr j)) := by
  unfold atom Kripke.Forces Kripke.Model.termValue presentR
  simp only [Term.realize_var]
  have he : (fun k : Fin 2 => s (.inr (if k = 0 then i else j))) =
      (fun k => if k = 0 then s (.inr i) else s (.inr j)) := by
    funext k
    by_cases hk : k = 0 <;> simp [hk]
  rw [he]

theorem present_relation {W : Type w} [Preorder W]
    (K : Kripke.Model.{0,0,w,d} orderLanguage W) (z : W)
    (h : Kripke.ForcesContext K z (↑premises : Set (Lemmatheca.ProofTheory.FirstOrder.Formula orderLanguage Empty)) Empty.elim) :
    let R := fun x y : K.Domain z => @Structure.RelMap orderLanguage (K.Domain z)
      (K.structureAt z) 2 relation (fun k => if k = 0 then x else y)
    (∀ x, ¬R x x) ∧ (∀ x y t, R x y → R y t → R x t) ∧ (∀ x, ∃ y, R x y) := by
  have hi := h irreflexive (by simp [premises])
  have ht := h transitive (by simp [premises])
  have hs := h serial (by simp [premises])
  change (∀ x, ¬presentR K z x x) ∧
    (∀ x y t, presentR K z x y → presentR K z y t → presentR K z x t) ∧
    (∀ x, ∃ y, presentR K z x y)
  constructor
  · intro x hx
    have hn := hi z (le_refl z) x z (le_refl z)
    simp only [Kripke.transport_refl] at hn
    apply hn
    apply (forces_atom K z 0 0 _).mpr
    simpa [extendAssignment] using hx
  · constructor
    · intro x y t hxy hyt
      have hm := ht z (le_refl z) x z (le_refl z) y z (le_refl z) t z (le_refl z)
      simp only [Kripke.transport_refl] at hm
      have hx : Kripke.Forces K (atom (0 : Fin 3) 1) z
          (extendAssignment (extendAssignment (extendAssignment (Sum.elim Empty.elim Fin.elim0) x) y) t) := by
        apply (forces_atom K z 0 1 _).mpr
        simpa [extendAssignment] using hxy
      have hy : Kripke.Forces K (atom (1 : Fin 3) 2) z
          (extendAssignment (extendAssignment (extendAssignment (Sum.elim Empty.elim Fin.elim0) x) y) t) := by
        apply (forces_atom K z 1 2 _).mpr
        simpa [extendAssignment] using hyt
      have hh := (forces_atom K z 0 2 _).mp (hm ⟨hx,hy⟩)
      simpa [extendAssignment] using hh
    · intro x
      obtain ⟨y,hy⟩ := hs z (le_refl z) x
      refine ⟨y,?_⟩
      have hh := (forces_atom K z 0 1 _).mp hy
      simpa [Kripke.transport_refl,extendAssignment] using hh

theorem infinite_present_domain {W : Type w} [Preorder W]
    (K : Kripke.Model.{0,0,w,d} orderLanguage W) (z : W)
    (h : Kripke.ForcesContext K z (↑premises : Set (Lemmatheca.ProofTheory.FirstOrder.Formula orderLanguage Empty)) Empty.elim) :
    Infinite (K.Domain z) := by
  classical
  obtain ⟨hi,ht,hs⟩ := present_relation K z h
  let R := presentR K z
  let next (x : K.Domain z) : K.Domain z := Classical.choose (hs x)
  have hn (x : K.Domain z) : R x (next x) := Classical.choose_spec (hs x)
  let f : ℕ → K.Domain z := Nat.rec (Classical.choice (K.domain_nonempty z)) (fun _ x => next x)
  have hc : ∀ i j, i < j → R (f i) (f j) := by
    intro i j
    induction j with
    | zero => intro hij; omega
    | succ j ih =>
        intro hij
        by_cases he : i = j
        · subst i
          exact hn (f j)
        · exact ht _ _ _ (ih (by omega)) (hn (f j))
  apply Infinite.of_injective f
  intro i j he
  rcases lt_trichotomy i j with hij | hij | hji
  · exact False.elim (hi (f i) (he ▸ hc i j hij))
  · exact hij
  · exact False.elim (hi (f j) (he ▸ hc j i hji))

theorem no_finite_present_countermodel {W : Type w} [Preorder W]
    (K : Kripke.Model.{0,0,w,d} orderLanguage W) (z : W) [Finite (K.Domain z)] :
    ¬Kripke.Countermodel K z (↑premises : Set (Lemmatheca.ProofTheory.FirstOrder.Formula orderLanguage Empty)) .falsum Empty.elim := by
  intro h
  have hi := infinite_present_domain K z h.1
  exact hi.false

end
end Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderKripkeCompleteness
