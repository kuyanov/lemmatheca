import Lemmatheca.EhrenfeuchtMostowskiModels.Models
import Lemmatheca.QuantifierElimination.QuantifierEliminationShared
import Lemmatheca.BackAndForth.BackAndForth
import Mathlib.Logic.Equiv.Fintype

/-! Template incompatibility and the distinction between a skeleton and its full hull. -/
namespace Lemmatheca.Entry.EhrenfeuchtMostowskiModels
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.EhrenfeuchtMostowski
open Lemmatheca.ModelTheory.IndiscernibleSequences
universe u v w z

inductive PredicateSymbol : ℕ → Type
  | p : PredicateSymbol 1

def predicateLanguage : Language := ⟨fun _ => Empty, PredicateSymbol⟩

structure PredicateWorld (truth : Bool) where
  val : ℕ

instance predicateWorldStructure (truth : Bool) :
    predicateLanguage.Structure (PredicateWorld truth) where
  funMap f _ := f.elim
  RelMap R _ := match R with | .p => truth = true

def predicateSequence (truth : Bool) (i : ℕ) : PredicateWorld truth := ⟨i⟩

theorem constant_predicate_indiscernible (truth : Bool) :
    Function.Injective (predicateSequence truth) ∧
      OrderIndiscernible (L := predicateLanguage) (∅ : Set (PredicateWorld truth))
        (fun i (_ : Fin 1) => predicateSequence truth i) := by
  classical
  refine ⟨fun i j h => congrArg PredicateWorld.val h,?_⟩
  intro n hn φ s t
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair s t s.injective t.injective
  let e0 : PredicateWorld truth ≃ ℕ :=
    { toFun := PredicateWorld.val
      invFun := PredicateWorld.mk
      left_inv := by intro a; cases a; rfl
      right_inv := fun _ => rfl }
  let e : PredicateWorld truth ≃[predicateLanguage[[(∅ : Set (PredicateWorld truth))]]]
      PredicateWorld truth :=
    { toEquiv := (e0.trans σ).trans e0.symm
      map_fun' := by
        intro r f
        rcases f with f | c
        · exact Empty.elim f
        · cases r with
          | zero => exact (Set.notMem_empty _ c.property).elim
          | succ r => exact isEmptyElim c
      map_rel' := by
        intro r R xs
        rcases R with R | R
        · cases R
          rfl
        · exact Empty.elim R }
  have hmap : e ∘ tupleAssignment (fun i (_ : Fin 1) => predicateSequence truth i) s =
      tupleAssignment (fun i (_ : Fin 1) => predicateSequence truth i) t := by
    funext x
    exact congrArg (PredicateWorld.mk : ℕ → PredicateWorld truth)
      (hσ (finProdFinEquiv.symm x).1)
  have he := (StrongHomClass.realize_formula e φ
    (v := tupleAssignment (fun i (_ : Fin 1) => predicateSequence truth i) s)).symm
  rw [hmap] at he
  exact he

theorem incompatible_predicate_templates :
    ¬Nonempty (PredicateWorld true ↪ₑ[predicateLanguage] PredicateWorld false) := by
  rintro ⟨e⟩
  let φ : predicateLanguage.Formula Unit := Relations.formula (L := predicateLanguage) PredicateSymbol.p ![.var ()]
  have h : φ.Realize (fun _ : Unit => (⟨0⟩ : PredicateWorld true)) := by rfl
  have hc := (e.map_formula φ (fun _ : Unit => (⟨0⟩ : PredicateWorld true))).mpr h
  change (false : Bool) = true at hc
  exact Bool.noConfusion hc

theorem equality_generated_carrier {M : Type w} [Language.empty.Structure M] (B : Set M) :
    (Substructure.closure Language.empty B : Set M) = B := by
  let S : Language.empty.Substructure M :=
    { carrier := B
      fun_mem := by intro n f; exact Empty.elim f }
  have hS : Substructure.closure Language.empty B ≤ S :=
    Substructure.closure_le.mpr (fun _ h => h)
  exact Set.Subset.antisymm hS Substructure.subset_closure

theorem infinite_equality_generated_elementary {M : Type w}
    [Language.empty.Structure M] [Infinite M] (B : Set M) (hB : B.Infinite) :
    (Substructure.closure Language.empty B).IsElementary := by
  let S := Substructure.closure Language.empty B
  let : Infinite S := by
    change Infinite (↥(S : Set M))
    rw [equality_generated_carrier B]
    exact hB.to_subtype
  let e := Lemmatheca.ModelTheory.QuantifierElimination.Shared.equality_elementaryEmbedding
    (Subtype.val : S → M) Subtype.val_injective
  intro n φ a
  exact e.map_formula φ a

private def oneSelection {J : Type*} [LinearOrder J] (i : J) : Fin 1 ↪o J where
  toFun := fun _ => i
  inj' := fun _ _ _ => Subsingleton.elim _ _
  map_rel_iff' := by
    intro a b
    have hab : a = b := Subsingleton.elim _ _
    simp only [hab,le_refl]

theorem indiscernible_avoids_constant {L : Language.{u,v}} {M : Type w}
    [L.Structure M] {I : Type z} [LinearOrder I] [Infinite I]
    (b : I → M) (hb : Function.Injective b)
    (hi : OrderIndiscernible (L := L) (∅ : Set M) (fun i (_ : Fin 1) => b i))
    (c : L.Constants) : ∀ i, b i ≠ (c : M) := by
  intro i hci
  obtain ⟨j,hji⟩ := exists_ne i
  let ψ : L.Formula (Fin (1*1)) := (Term.var 0).equal (Constants.term c)
  let φ := (L.lhomWithConstants (∅ : Set M)).onFormula ψ
  have hφ := hi 1 (by decide) φ (oneSelection i) (oneSelection j)
  simp only [φ,LHom.realize_onFormula,ψ,Formula.realize_equal,
    Term.realize_var,Term.realize_constants] at hφ
  change (b i = (c : M) ↔ b j = (c : M)) at hφ
  have hcj := hφ.mp hci
  exact hji (hb (hcj.trans hci.symm))

noncomputable def addedWitnessConstant (L : Language.{u,v}) :
    (fullySkolemizedLanguage L).Constants :=
  witnessSymbol (normalizedLanguage L)
    (⊤ : (fullySkolemizedLanguage L).BoundedFormula Empty 1)

theorem full_hull_strictly_contains_skeleton
    (L : Language.{u,v}) {M : Type w} [L.Structure M] (m₀ : M)
    (p : Template.{max u v,max u v,w} (expansionTheory L m₀))
    {I : Type z} [LinearOrder I] [Infinite I]
    (R : EMRealization (expansionTheory L m₀) p I) :
    let d : R.ambient := (addedWitnessConstant L : R.ambient)
    d ∈ hull (fullySkolemizedLanguage L) R.skeleton ∧ d ∉ Set.range R.skeleton := by
  dsimp only
  refine ⟨Substructure.constants_mem (S := hull (fullySkolemizedLanguage L) R.skeleton) (addedWitnessConstant L),?_⟩
  rintro ⟨i,hi⟩
  exact indiscernible_avoids_constant R.skeleton R.distinct
    (realizesTemplate_indiscernible _ p R.skeleton R.realizes) (addedWitnessConstant L) i hi

theorem nat_rat_orders_not_isomorphic : ¬Nonempty (ℕ ≃o ℚ) := by
  rintro ⟨e⟩
  obtain ⟨q,hq⟩ := exists_lt (e 0)
  have h0 : e 0 ≤ q := by
    rw [←e.apply_symm_apply q]
    exact e.monotone (Nat.zero_le _)
  exact not_lt_of_ge h0 hq

end Lemmatheca.Entry.EhrenfeuchtMostowskiModels
