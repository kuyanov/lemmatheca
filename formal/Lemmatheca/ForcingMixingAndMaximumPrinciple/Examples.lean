import Lemmatheca.ForcingMixingAndMaximumPrinciple.Mixing
import Lemmatheca.CumulativeHierarchy.CumulativeHierarchy

namespace Lemmatheca.Entry.ForcingMixingAndMaximumPrinciple
open Set Order FirstOrder FirstOrder.Language
open scoped ZFSet Ordinal
open Lemmatheca.SetTheory.ForcingNames
open Lemmatheca.SetTheory.ForcingTheorem
open Lemmatheca.SetTheory.ForcingTheorem.ThreePoint
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.ForcingMixingAndMaximumPrinciple
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

def forkAntichain : Set Condition := {Condition.left, Condition.right}

def zeroName (C : Context.{u,0} Condition) : ZFSet.{u} :=
  checkName (C.code Condition.one).val ∅

def oneName (C : Context.{u,0} Condition) : ZFSet.{u} :=
  checkName (C.code Condition.one).val {∅}

def forkNames (C : Context.{u,0} Condition) (a : forkAntichain) : ZFSet.{u} :=
  if a.val = Condition.left then zeroName C else oneName C

def forkName (C : Context.{u,0} Condition) : ZFSet.{u} :=
  mixedName C forkAntichain (forkNames C)

theorem fork_antichain : Antichain forkAntichain := by
  intro p hp q hq hpq
  have hp' : p = Condition.left ∨ p = Condition.right := by
    simpa only [forkAntichain,Set.mem_insert_iff,Set.mem_singleton_iff] using hp
  have hq' : q = Condition.left ∨ q = Condition.right := by
    simpa only [forkAntichain,Set.mem_insert_iff,Set.mem_singleton_iff] using hq
  rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
  · exact (hpq rfl).elim
  · exact finite_order.2.2.1
  · rintro ⟨r,hrq,hrp⟩
    exact finite_order.2.2.1 ⟨r,hrp,hrq⟩
  · exact (hpq rfl).elim

private theorem fork_names_valid (C : Context.{u,0} Condition) (a : forkAntichain) :
    IsName C.conditions (forkNames C a) := by
  unfold forkNames
  split_ifs
  · exact checkName_isName C.conditions (C.code Condition.one).val ∅
      (C.code Condition.one).property
  · exact checkName_isName C.conditions (C.code Condition.one).val {∅}
      (C.code Condition.one).property

theorem fork_name_valid (C : Context.{u,0} Condition) : IsName C.conditions (forkName C) := by
  exact mixedName_valid C forkAntichain (forkNames C) (fork_names_valid C)

theorem fork_filters :
    ((PFilter.principal Condition.left : PFilter Condition) : Set Condition) =
      {Condition.left,Condition.one} ∧
    ((PFilter.principal Condition.right : PFilter Condition) : Set Condition) =
      {Condition.right,Condition.one} ∧
    ∀ S : Set (Set Condition), GenericFor (PFilter.principal Condition.left) S ∧
      GenericFor (PFilter.principal Condition.right) S := by
  refine ⟨?_,?_,?_⟩
  · ext p
    change (Condition.left = p ∨ p = Condition.one) ↔
      (p = Condition.left ∨ p = Condition.one)
    exact or_congr eq_comm Iff.rfl
  · ext p
    change (Condition.right = p ∨ p = Condition.one) ↔
      (p = Condition.right ∨ p = Condition.one)
    exact or_congr eq_comm Iff.rfl
  · intro S
    constructor
    · intro D _ hD
      obtain ⟨q,hqD,hq⟩ := hD Condition.left
      have he : q = Condition.left := finite_order.2.2.2.2.2.1 q hq
      exact ⟨q,PFilter.mem_principal.mpr (he ▸ le_rfl),hqD⟩
    · intro D _ hD
      obtain ⟨q,hqD,hq⟩ := hD Condition.right
      have he : q = Condition.right := finite_order.2.2.2.2.2.2 q hq
      exact ⟨q,PFilter.mem_principal.mpr (he ▸ le_rfl),hqD⟩

private theorem top_code_mem (C : Context.{u,0} Condition) (G : PFilter Condition) :
    (C.code Condition.one).val ∈ C.filterCode G := by
  exact (filterSet_mem C.conditions C.code G _).mpr
    ⟨Condition.one,PFilter.top_mem,rfl⟩

private theorem fork_value_left (C : Context.{u,0} Condition) (G : PFilter Condition)
    (ha : Condition.left ∈ G) : evaluation (C.filterCode G) (forkName C) = ∅ := by
  have h := mixedName_value C forkAntichain (forkNames C) (fork_names_valid C)
    fork_antichain G ⟨Condition.left,by simp [forkAntichain]⟩ ha
  have h' : evaluation (C.filterCode G) (forkName C) =
      evaluation (C.filterCode G) (zeroName C) := by
    simpa only [forkName,forkNames,ite_true] using h
  exact h'.trans (checkName_value _ _ _ (top_code_mem C G))

private theorem fork_value_right (C : Context.{u,0} Condition) (G : PFilter Condition)
    (hb : Condition.right ∈ G) : evaluation (C.filterCode G) (forkName C) = {∅} := by
  have h := mixedName_value C forkAntichain (forkNames C) (fork_names_valid C)
    fork_antichain G ⟨Condition.right,by simp [forkAntichain]⟩ hb
  have h' : evaluation (C.filterCode G) (forkName C) =
      evaluation (C.filterCode G) (oneName C) := by
    simpa only [forkName,forkNames,ite_eq_right (by decide : Condition.right ≠ Condition.left)] using h
  exact h'.trans (checkName_value _ _ _ (top_code_mem C G))

theorem fork_values (C : Context.{u,0} Condition) :
    evaluation (C.filterCode (PFilter.principal Condition.left)) (forkName C) = ∅ ∧
    evaluation (C.filterCode (PFilter.principal Condition.right)) (forkName C) = {∅} := by
  exact ⟨fork_value_left C _ (PFilter.mem_principal.mpr le_rfl),
    fork_value_right C _ (PFilter.mem_principal.mpr le_rfl)⟩

theorem fork_not_fixed_check (C : Context.{u,0} Condition) (x : ZFSet.{u}) :
    ¬(∀ G : PFilter Condition,
      evaluation (C.filterCode G) (forkName C) =
        evaluation (C.filterCode G) (checkName (C.code Condition.one).val x)) := by
  intro h
  have hl : (∅ : ZFSet.{u}) = x :=
    (fork_values C).1.symm.trans ((h _).trans (checkName_value _ _ x (top_code_mem C _)))
  have hr : ({∅} : ZFSet.{u}) = x :=
    (fork_values C).2.symm.trans ((h _).trans (checkName_value _ _ x (top_code_mem C _)))
  have he : (∅ : ZFSet.{u}) = {∅} := hl.trans hr.symm
  have hm : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := by simp
  rw [← he] at hm
  exact ZFSet.notMem_empty _ hm

def forkGroundName (C : Context.{u,0} Condition) (hM : forkName C ∈ C.ground) : C.Name :=
  ⟨forkName C,hM,fork_name_valid C⟩

def zeroGroundName (C : Context.{u,0} Condition) (hM : zeroName C ∈ C.ground) : C.Name :=
  ⟨zeroName C,hM,checkName_isName C.conditions (C.code Condition.one).val ∅
    (C.code Condition.one).property⟩

def oneGroundName (C : Context.{u,0} Condition) (hM : oneName C ∈ C.ground) : C.Name :=
  ⟨oneName C,hM,checkName_isName C.conditions (C.code Condition.one).val {∅}
    (C.code Condition.one).property⟩

def equalityFormula (i j : Fin 3) : membershipLanguage.BoundedFormula Empty 3 :=
  .equal (.var (.inr i)) (.var (.inr j))

def forkChoiceFormula : membershipLanguage.BoundedFormula Empty 3 :=
  equalityFormula 0 1 ⊔ equalityFormula 0 2

private theorem equalityFormula_truth (C : Context.{u,0} Condition) (G : PFilter Condition)
    (ρ : Fin 3 → C.Name) (i j : Fin 3) :
    setSatisfies (C.valueDomain G) (equalityFormula i j) (C.valueAssignment G ρ) ↔
      evaluation (C.filterCode G) (ρ i).val = evaluation (C.filterCode G) (ρ j).val := by
  let := actualMembershipStructure (C.valueDomain G)
  change C.value G (ρ i) = C.value G (ρ j) ↔ _
  exact Subtype.ext_iff

theorem fork_semantic_choices (C : Context.{u,0} Condition)
    (hM : forkName C ∈ C.ground) (h0 : zeroName C ∈ C.ground)
    (h1 : oneName C ∈ C.ground) (hA : forkAntichain ∈ C.groundFamily) :
    let ρ : Fin 3 → C.Name :=
      ![forkGroundName C hM,zeroGroundName C h0,oneGroundName C h1]
    C.semanticForce forkChoiceFormula ρ Condition.one ∧
      ¬C.semanticForce (equalityFormula 0 1) ρ Condition.one ∧
      ¬C.semanticForce (equalityFormula 0 2) ρ Condition.one := by
  let ρ : Fin 3 → C.Name :=
    ![forkGroundName C hM,zeroGroundName C h0,oneGroundName C h1]
  change C.semanticForce forkChoiceFormula ρ Condition.one ∧
    ¬C.semanticForce (equalityFormula 0 1) ρ Condition.one ∧
    ¬C.semanticForce (equalityFormula 0 2) ρ Condition.one
  refine ⟨?_,?_,?_⟩
  · intro G hG _
    let := actualMembershipStructure (C.valueDomain G)
    change (equalityFormula 0 1 ⊔ equalityFormula 0 2).Realize Empty.elim
      (C.valueAssignment G ρ)
    rw [BoundedFormula.realize_sup]
    obtain ⟨p,hpG,hpA⟩ := hG forkAntichain hA split_dense
    have hp : p = Condition.left ∨ p = Condition.right := by
      simpa only [forkAntichain,Set.mem_insert_iff,Set.mem_singleton_iff] using hpA
    rcases hp with rfl | rfl
    · left
      apply (equalityFormula_truth C G ρ 0 1).mpr
      change evaluation (C.filterCode G) (forkName C) = evaluation (C.filterCode G) (zeroName C)
      exact (fork_value_left C G hpG).trans (checkName_value _ _ _ (top_code_mem C G)).symm
    · right
      apply (equalityFormula_truth C G ρ 0 2).mpr
      change evaluation (C.filterCode G) (forkName C) = evaluation (C.filterCode G) (oneName C)
      exact (fork_value_right C G hpG).trans (checkName_value _ _ _ (top_code_mem C G)).symm
  · intro h
    have ht := h (PFilter.principal Condition.right) (fork_filters.2.2 C.groundFamily).2
      (PFilter.mem_principal.mpr (show Condition.right ≤ Condition.one from le_top))
    have he := (equalityFormula_truth C _ ρ 0 1).mp ht
    change evaluation (C.filterCode _) (forkName C) = evaluation (C.filterCode _) (zeroName C) at he
    rw [(fork_values C).2,show evaluation _ (zeroName C) = ∅ from
      checkName_value _ _ _ (top_code_mem C _)] at he
    have hm : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := by simp
    rw [he] at hm
    exact ZFSet.notMem_empty _ hm
  · intro h
    have ht := h (PFilter.principal Condition.left) (fork_filters.2.2 C.groundFamily).1
      (PFilter.mem_principal.mpr (show Condition.left ≤ Condition.one from le_top))
    have he := (equalityFormula_truth C _ ρ 0 2).mp ht
    change evaluation (C.filterCode _) (forkName C) = evaluation (C.filterCode _) (oneName C) at he
    rw [(fork_values C).1,show evaluation _ (oneName C) = {∅} from
      checkName_value _ _ _ (top_code_mem C _)] at he
    have hm : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := by simp
    rw [← he] at hm
    exact ZFSet.notMem_empty _ hm

/-- The actual infinite graph, not a predicate assuming collection closure. -/
def identityGraph : ZFSet.{u} :=
  ZFSet.range (fun n : ℕ => ZFSet.pair (n : Ordinal.{u}).toZFSet (n : Ordinal.{u}).toZFSet)

theorem transitive_family_counterexample :
    (ZFSet.vonNeumann (ω : Ordinal.{u})).IsTransitive ∧
    (∀ n : ℕ, (n : Ordinal.{u}).toZFSet ∈ ZFSet.vonNeumann (ω : Ordinal.{u})) ∧
    (ω : Ordinal.{u}).toZFSet ∉ ZFSet.vonNeumann (ω : Ordinal.{u}) ∧
    identityGraph ∉ ZFSet.vonNeumann (ω : Ordinal.{u}) ∧
    (∀ x : ZFSet.{u}, x ∈ (ω : Ordinal.{u}).toZFSet ↔
      ∃ n : ℕ, x = (n : Ordinal.{u}).toZFSet) ∧
    (∀ z : ZFSet.{u}, z ∈ identityGraph ↔
      ∃ n : ℕ, z = ZFSet.pair (n : Ordinal.{u}).toZFSet (n : Ordinal.{u}).toZFSet) := by
  have hgraph : Infinite (identityGraph : ZFSet.{u}) := by
    apply Infinite.of_injective (fun n : ℕ =>
      (⟨ZFSet.pair (n : Ordinal.{u}).toZFSet (n : Ordinal.{u}).toZFSet,
        (by exact ZFSet.mem_range.mpr ⟨n, rfl⟩)⟩ : (identityGraph : ZFSet.{u})))
    intro a b hab
    have he := (ZFSet.pair_inj.mp (congrArg Subtype.val hab)).1
    exact_mod_cast Ordinal.toZFSet_injective he
  refine ⟨ZFSet.isTransitive_vonNeumann _, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (Lemmatheca.SetTheory.CumulativeHierarchy.ordinal_part _ _).mpr
      (Ordinal.natCast_lt_omega0 n)
  · rw [Lemmatheca.SetTheory.CumulativeHierarchy.ordinal_part]
    exact lt_irrefl _
  · intro h
    have := (Lemmatheca.SetTheory.CumulativeHierarchy.omega_stage.{u}).2 _ h
    exact not_finite (identityGraph : ZFSet.{u})
  · intro x
    rw [Ordinal.mem_toZFSet_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp ha
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, Ordinal.natCast_lt_omega0 n, rfl⟩
  · intro z
    simp only [identityGraph, ZFSet.mem_range]
    exact exists_congr (fun _ => eq_comm)


end
end Lemmatheca.Entry.ForcingMixingAndMaximumPrinciple
