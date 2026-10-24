import Lemmatheca.Absoluteness.Absoluteness
import Mathlib.ModelTheory.Encoding

/-! Definability uses actual finite shared membership formulas and finite tuples
from the supplied domain. It does not use ZFSet.Definable, which describes lifted
functions on pre-sets rather than first-order definable subsets. Semantics is
allowed on the empty domain, without a Nonempty instance. -/
namespace Lemmatheca.SetTheory.ConstructibleHierarchy
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
universe u
noncomputable section

/-- Parameters occupy the first slots and the candidate object the appended slot. -/
abbrev DefinitionCode (M : ZFSet.{u}) :=
  Σ n : ℕ, membershipLanguage.BoundedFormula Empty (n+1) × (Fin n → M)

def definedSubset (M : ZFSet.{u}) (c : DefinitionCode M) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ hx : x ∈ M,
    setSatisfies M c.2.1 (Fin.snoc c.2.2 ⟨x,hx⟩)) M

def Def (M : ZFSet.{u}) : ZFSet.{u} := ZFSet.range (definedSubset M)

theorem definedSubset_members (M : ZFSet.{u}) (c : DefinitionCode M) (x : M) :
    x.val ∈ definedSubset M c ↔ setSatisfies M c.2.1 (Fin.snoc c.2.2 x) := by
  simp only [definedSubset,ZFSet.mem_sep]
  exact ⟨fun ⟨_,_,h⟩ => h,fun h => ⟨x.property,x.property,h⟩⟩

theorem Def_members (M X : ZFSet.{u}) :
    X ∈ Def M ↔ ∃ c : DefinitionCode M, definedSubset M c = X := by
  exact ZFSet.mem_range

theorem Def_subset_powerset (M : ZFSet.{u}) : Def M ⊆ ZFSet.powerset M := by
  intro X hX
  obtain ⟨c,rfl⟩ := (Def_members M X).mp hX
  exact ZFSet.mem_powerset.mpr (fun _ hx => (ZFSet.mem_sep.mp hx).1)

def fullCode (M : ZFSet.{u}) : DefinitionCode M :=
  ⟨0,.equal (.var (.inr 0)) (.var (.inr 0)),Fin.elim0⟩
def emptyCode (M : ZFSet.{u}) : DefinitionCode M :=
  ⟨0,(BoundedFormula.equal (.var (.inr 0)) (.var (.inr 0))).not,Fin.elim0⟩
def memberCode (M : ZFSet.{u}) (a : M) : DefinitionCode M :=
  ⟨1,memScoped (α := Empty) (n := 2) 1 0,![a]⟩
def singletonCode (M : ZFSet.{u}) (a : M) : DefinitionCode M :=
  ⟨1,.equal (.var (.inr 1)) (.var (.inr 0)),![a]⟩
def ordinalCode (M : ZFSet.{u}) : DefinitionCode M :=
  ⟨0,(ordinalTest (0 : Fin 1)).toShared,Fin.elim0⟩

theorem full_empty_codes (M : ZFSet.{u}) :
    definedSubset M (fullCode M) = M ∧ definedSubset M (emptyCode M) = ∅ := by
  constructor <;> ext z <;>
    simp [definedSubset,fullCode,emptyCode,nativeSatisfies,BoundedFormula.Realize]

theorem Def_empty : Def (∅ : ZFSet.{u}) = {∅} := by
  ext X
  rw [ZFSet.mem_singleton]
  constructor
  · intro hX
    have hs := ZFSet.mem_powerset.mp (Def_subset_powerset _ hX)
    ext z
    exact ⟨fun hz => (ZFSet.notMem_empty _ (hs hz)).elim,fun hz => (ZFSet.notMem_empty _ hz).elim⟩
  · rintro rfl
    exact (Def_members _ _).mpr ⟨emptyCode _,(full_empty_codes _).2⟩

theorem full_and_empty_mem (M : ZFSet.{u}) : M ∈ Def M ∧ (∅ : ZFSet.{u}) ∈ Def M := by
  constructor
  · exact (Def_members _ _).mpr ⟨fullCode M,(full_empty_codes M).1⟩
  · exact (Def_members _ _).mpr ⟨emptyCode M,(full_empty_codes M).2⟩

theorem memberCode_correct (M : ZFSet.{u}) (hM : M.IsTransitive) (a : M) :
    definedSubset M (memberCode M a) = a.val := by
  ext z
  rw [definedSubset,ZFSet.mem_sep]
  change (z ∈ M ∧ ∃ hz : z ∈ M,
    setSatisfies M (memScoped (1 : Fin 2) 0) (Fin.snoc ![a] ⟨z,hz⟩)) ↔ z ∈ a.val
  change (z ∈ M ∧ ∃ _ : z ∈ M, z ∈ a.val) ↔ z ∈ a.val
  exact ⟨fun ⟨_,_,h⟩ => h,fun h => ⟨hM.mem_trans h a.property,hM.mem_trans h a.property,h⟩⟩

theorem singletonCode_correct (M : ZFSet.{u}) (a : M) :
    definedSubset M (singletonCode M a) = {a.val} := by
  ext z
  rw [definedSubset,ZFSet.mem_sep]
  change (z ∈ M ∧ ∃ hz : z ∈ M, (⟨z,hz⟩ : M) = a) ↔ z ∈ ({a.val} : ZFSet.{u})
  simp only [ZFSet.mem_singleton,Subtype.ext_iff]
  exact ⟨fun ⟨_,_,h⟩ => h,fun h => ⟨h ▸ a.property,h ▸ a.property,h⟩⟩

theorem ordinalCode_correct (M : ZFSet.{u}) (hM : M.IsTransitive) :
    definedSubset M (ordinalCode M) = ZFSet.sep ZFSet.IsOrdinal M := by
  have he (x : M) :
      setSatisfies M (ordinalTest (0 : Fin 1)).toShared (Fin.snoc Fin.elim0 x) ↔
        x.val.IsOrdinal :=
    (bounded_to_universe M hM _ _).trans (ordinalTest_correct _ _)
  ext z
  rw [definedSubset,ZFSet.mem_sep]
  change (z ∈ M ∧ ∃ hz : z ∈ M, setSatisfies M
    (ordinalTest (0 : Fin 1)).toShared (Fin.snoc Fin.elim0 ⟨z,hz⟩)) ↔ z ∈ ZFSet.sep ZFSet.IsOrdinal M
  simp only [he,ZFSet.mem_sep]
  exact ⟨fun ⟨hz,_,h⟩ => ⟨hz,h⟩,fun ⟨hz,h⟩ => ⟨hz,hz,h⟩⟩

theorem transitive_Def (M : ZFSet.{u}) (hM : M.IsTransitive) :
    M ⊆ Def M ∧ (Def M).IsTransitive := by
  have hi : M ⊆ Def M := by
    intro a ha
    exact (Def_members _ _).mpr ⟨memberCode M ⟨a,ha⟩,memberCode_correct M hM ⟨a,ha⟩⟩
  exact ⟨hi,fun X hX z hz => hi ((ZFSet.mem_powerset.mp (Def_subset_powerset M hX)) hz)⟩

/-- Explicit equality disjunction over the finite parameter list. -/
def finiteDisjunction {n} (is : List (Fin n)) : membershipLanguage.BoundedFormula Empty (n+1) :=
  is.foldr (fun i p => (.equal (.var (.inr (Fin.last n))) (.var (.inr i.castSucc))) ⊔ p) .falsum

def finiteSubsetCode (M : ZFSet.{u}) (as : List M) : DefinitionCode M :=
  ⟨as.length,finiteDisjunction (List.finRange as.length),as.get⟩

private theorem finiteDisjunction_realize {M : Type*} (E : M → M → Prop) {n}
    (is : List (Fin n)) (a : Fin (n+1) → M) :
    nativeSatisfies E (finiteDisjunction is) a ↔
      ∃ i ∈ is, a (Fin.last n) = a i.castSucc := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  induction is with
  | nil => simp [finiteDisjunction,nativeSatisfies,BoundedFormula.Realize]
  | cons i is ih =>
    change ((_ ⊔ finiteDisjunction is).Realize Empty.elim a) ↔ _
    rw [BoundedFormula.realize_sup]
    change (a (Fin.last n) = a i.castSucc ∨ nativeSatisfies E (finiteDisjunction is) a) ↔ _
    exact (or_congr Iff.rfl ih).trans (by simp only [List.mem_cons,exists_eq_or_imp])

theorem finiteSubsetCode_correct (M : ZFSet.{u}) (as : List M) :
    definedSubset M (finiteSubsetCode M as) =
      ZFSet.range (fun i : Fin as.length => (as.get i).val) := by
  ext z
  rw [ZFSet.mem_range]
  constructor
  · intro hz
    have hzM := (ZFSet.mem_sep.mp hz).1
    have ht := (definedSubset_members M (finiteSubsetCode M as) ⟨z,hzM⟩).mp hz
    change nativeSatisfies (fun x y : M => x.val ∈ y.val)
      (finiteDisjunction (List.finRange as.length)) (Fin.snoc as.get ⟨z,hzM⟩) at ht
    obtain ⟨i,_,hi⟩ := (finiteDisjunction_realize _ _ _).mp ht
    simp only [Fin.snoc_last,Fin.snoc_castSucc] at hi
    exact ⟨i,(congrArg Subtype.val hi).symm⟩
  · rintro ⟨i,rfl⟩
    apply (definedSubset_members M (finiteSubsetCode M as) (as.get i)).mpr
    change nativeSatisfies (fun x y : M => x.val ∈ y.val)
      (finiteDisjunction (List.finRange as.length)) (Fin.snoc as.get (as.get i))
    apply (finiteDisjunction_realize _ _ _).mpr
    exact ⟨i,List.mem_finRange i,by simp⟩

theorem finite_Def (M : ZFSet.{u}) [Finite M] : Def M = ZFSet.powerset M := by
  classical
  apply le_antisymm (Def_subset_powerset M)
  intro X hX
  have hs := ZFSet.mem_powerset.mp hX
  let := Fintype.ofFinite M
  let as : List M := (Finset.univ.filter (fun a : M => a.val ∈ X)).toList
  have he : ZFSet.range (fun i : Fin as.length => (as.get i).val) = X := by
    ext z
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨i,rfl⟩
      have hi : as.get i ∈ as := List.get_mem as i
      simpa only [as,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    · intro hz
      let a : M := ⟨z,hs hz⟩
      have ha : a ∈ as := by simp [as,a,hz]
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha
      exact ⟨i,congrArg Subtype.val hi⟩
  exact (Def_members _ _).mpr ⟨finiteSubsetCode M as,(finiteSubsetCode_correct M as).trans he⟩

theorem countable_codes (M : ZFSet.{u}) [Countable M] : Countable (DefinitionCode M) := by
  let : Countable membershipLanguage.Symbols := countable_membership_symbols
  let (n : ℕ) : Countable (membershipLanguage.BoundedFormula Empty (n+1)) := by
    apply Function.Injective.countable (f := fun p : membershipLanguage.BoundedFormula Empty (n+1) =>
      (⟨n+1,p⟩ : Σ k, membershipLanguage.BoundedFormula Empty k))
    intro p q hpq
    simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hpq
  dsimp only [DefinitionCode]
  infer_instance

theorem countable_Def (M : ZFSet.{u}) [Countable M] : Countable (Def M) := by
  let : Countable (DefinitionCode M) := countable_codes M
  let f : DefinitionCode M → Def M := fun c => ⟨definedSubset M c,(Def_members _ _).mpr ⟨c,rfl⟩⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨c,hc⟩ := ZFSet.mem_range.mp x.property
    exact ⟨c,Subtype.ext hc⟩
  exact hf.countable

def singletonIntoDef (M : ZFSet.{u}) : M → Def M :=
  fun a => ⟨{a.val},by
    rw [← singletonCode_correct M a]
    exact ZFSet.mem_range_self (singletonCode M a)⟩

theorem singletonIntoDef_spec (M : ZFSet.{u}) :
    (∀ a, (singletonIntoDef M a).val = {a.val}) ∧
    Function.Injective (singletonIntoDef M) := by
  refine ⟨fun _ => rfl,?_⟩
  intro a b hab
  apply Subtype.ext
  exact ZFSet.singleton_injective (congrArg Subtype.val hab)

theorem infinite_Def (M : ZFSet.{u}) [Infinite M] : Infinite (Def M) := by
  exact Infinite.of_injective (singletonIntoDef M) (singletonIntoDef_spec M).2

theorem countable_infinite_Def (M : ZFSet.{u}) [Countable M] [Infinite M] :
    Countable (Def M) ∧ Infinite (Def M) ∧ ¬Countable (ZFSet.powerset M) ∧
      Def M ⊂ ZFSet.powerset M := by
  have hc : Countable (Def M) := countable_Def M
  have hi : Infinite (Def M) := infinite_Def M
  have hM : M.card = Cardinal.aleph0 := by
    apply Cardinal.lift_injective.{u+1,u}
    rw [←ZFSet.cardinalMk_coe_sort,Cardinal.lift_aleph0]
    exact Cardinal.mk_eq_aleph0 M
  have hn : ¬Countable (ZFSet.powerset M) := by
    intro h
    have hp : (ZFSet.powerset M).card ≤ Cardinal.aleph0 := by
      apply Cardinal.lift_le.{u+1,u}.mp
      rw [←ZFSet.cardinalMk_coe_sort,Cardinal.lift_aleph0]
      exact Cardinal.mk_le_aleph0_iff.mpr h
    rw [ZFSet.card_powerset,hM] at hp
    exact not_le_of_gt (Cardinal.cantor _) hp
  refine ⟨hc,hi,hn,?_⟩
  apply lt_of_le_of_ne (Def_subset_powerset M)
  intro he
  exact hn (he ▸ hc)

end
end Lemmatheca.SetTheory.ConstructibleHierarchy
