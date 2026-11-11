import Lemmatheca.EffectiveEnumerations.Stages
import Lemmatheca.TuringDegrees.Joins

namespace Lemmatheca.ComputabilityTheory.EnumerationReducibility
open UniversalComputation

abbrev RuleRelation := ℕ → ℕ → Prop

def finiteSet (d : ℕ) : Finset ℕ := (FiniteSequenceCoding.decode d).toFinset

def singletonCode (n : ℕ) : ℕ := FiniteSequenceCoding.code [n]

def JointCE (R : RuleRelation) : Prop :=
  REPred (fun z : ℕ => R z.unpair.1 z.unpair.2)

def indexedRule (e n d : ℕ) : Prop := (phi e (Nat.pair n d)).Dom

def operatorOf (R : RuleRelation) (B : Set ℕ) : Set ℕ :=
  {n | ∃ d, R n d ∧ (finiteSet d : Set ℕ) ⊆ B}

def operator (e : ℕ) : Set ℕ → Set ℕ := operatorOf (indexedRule e)

def Reducible (A B : Set ℕ) : Prop := ∃ e, operator e B = A

def Equivalent (A B : Set ℕ) : Prop := Reducible A B ∧ Reducible B A

def identityRules (n d : ℕ) : Prop := d = singletonCode n

theorem finiteSet_empty (d : ℕ) : finiteSet d = ∅ ↔ d = 0 := by
  constructor
  · intro h
    have hd : FiniteSequenceCoding.decode d = [] := by simpa [finiteSet] using h
    simpa using congrArg FiniteSequenceCoding.code hd
  · rintro rfl
    simp [finiteSet]

theorem finiteSet_singleton (n : ℕ) : finiteSet (singletonCode n) = {n} := by
  simp [finiteSet, singletonCode]

theorem finiteSet_surjective (F : Finset ℕ) : ∃ d, finiteSet d = F := by
  exact ⟨FiniteSequenceCoding.code F.toList, by simp [finiteSet]⟩

theorem singletonCode_primitive : Primrec singletonCode := by
  exact (FiniteSequenceCoding.primrec_cons.comp Primrec.id (Primrec.const 0)).of_eq
    fun n => by simp [singletonCode, FiniteSequenceCoding.cons, Nat.add_comm]

theorem jointCE_iff_index (R : RuleRelation) :
    JointCE R ↔ ∃ e, ∀ n d, indexedRule e n d ↔ R n d := by
  unfold JointCE
  rw [enumerable_iff_index]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, fun n d => by simpa [indexedRule] using (he (Nat.pair n d)).symm⟩
  · rintro ⟨e, he⟩
    exact ⟨e, fun z => (he z.unpair.1 z.unpair.2).symm.trans (by simp [indexedRule])⟩

theorem operator_monotone (R : RuleRelation) : Monotone (operatorOf R) := by
  rintro B C hBC n ⟨d, hR, hd⟩
  exact ⟨d, hR, hd.trans hBC⟩

theorem operator_finite_information (R : RuleRelation) (B : Set ℕ) (n : ℕ) :
    n ∈ operatorOf R B ↔ ∃ F : Finset ℕ, (F : Set ℕ) ⊆ B ∧ n ∈ operatorOf R (F : Set ℕ) := by
  constructor
  · rintro ⟨d, hd, hB⟩
    exact ⟨finiteSet d, hB, d, hd, Set.Subset.rfl⟩
  · rintro ⟨F, hF, hn⟩
    exact operator_monotone R hF hn

private theorem finite_subset_stage (e : ℕ) (F : Finset ℕ)
    (hF : ∀ x ∈ F, x ∈ EffectiveEnumerations.indexSet e) :
    ∃ t, ∀ x ∈ F, x ∈ EffectiveEnumerations.stage e t := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x F hx ih =>
    obtain ⟨s, hs⟩ := (EffectiveEnumerations.stage_union e x).mp (hF x (by simp))
    obtain ⟨t, ht⟩ := ih (fun y hy => hF y (by simp [hy]))
    refine ⟨max s t, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact EffectiveEnumerations.stage_monotone e (le_max_left s t) hs
    · exact EffectiveEnumerations.stage_monotone e (le_max_right s t) (ht y hy)

theorem output_enumerable (R : RuleRelation) (hR : JointCE R) (B : Set ℕ)
    (hB : REPred (fun n => n ∈ B)) : REPred (fun n => n ∈ operatorOf R B) := by
  classical
  obtain ⟨b, hb⟩ := (enumerable_iff_index (fun n => n ∈ B)).mp hB
  have hstage : PrimrecRel (fun x t : ℕ => x ∈ EffectiveEnumerations.stage b t) :=
    EffectiveEnumerations.stage_predicate_primitive.comp
      (((Primrec.const b).pair Primrec.snd).pair Primrec.fst)
  have hall : PrimrecRel (fun d t : ℕ =>
      ∀ x ∈ FiniteSequenceCoding.decode d, x ∈ EffectiveEnumerations.stage b t) :=
    hstage.forall_mem_list.comp ((Primrec.ofNat (List ℕ)).comp Primrec.fst) Primrec.snd
  have hfinite : REPred (fun d => ∃ t, ∀ x ∈ FiniteSequenceCoding.decode d,
      x ∈ EffectiveEnumerations.stage b t) := enumerable_exists hall.computablePred.to_re
  have hsub (d : ℕ) : (finiteSet d : Set ℕ) ⊆ B ↔
      ∃ t, ∀ x ∈ FiniteSequenceCoding.decode d, x ∈ EffectiveEnumerations.stage b t := by
    constructor
    · intro hd
      have hF : ∀ x ∈ finiteSet d, x ∈ EffectiveEnumerations.indexSet b :=
        fun x hx => (hb x).mp (hd hx)
      obtain ⟨t, ht⟩ := finite_subset_stage b (finiteSet d) hF
      exact ⟨t, fun x hx => ht x (by simpa [finiteSet] using hx)⟩
    · rintro ⟨t, ht⟩ x hx
      exact (hb x).mpr ((EffectiveEnumerations.stage_union b x).mpr
        ⟨t, ht x (by simpa [finiteSet] using hx)⟩)
  have hpair : REPred (fun z : ℕ => R z.unpair.1 z.unpair.2 ∧
      ∃ t, ∀ x ∈ FiniteSequenceCoding.decode z.unpair.2,
        x ∈ EffectiveEnumerations.stage b t) :=
    enumerable_inter hR (hfinite.comp (Computable.snd.comp Computable.unpair))
  have hprod : REPred (fun p : ℕ × ℕ => R p.1 p.2 ∧
      ∃ t, ∀ x ∈ FiniteSequenceCoding.decode p.2,
        x ∈ EffectiveEnumerations.stage b t) := by
    have hh : REPred (fun p : ℕ × ℕ =>
        R (Nat.pair p.1 p.2).unpair.1 (Nat.pair p.1 p.2).unpair.2 ∧
        ∃ t, ∀ x ∈ FiniteSequenceCoding.decode (Nat.pair p.1 p.2).unpair.2,
          x ∈ EffectiveEnumerations.stage b t) := hpair.comp Primrec₂.natPair.to_comp
    exact hh.of_eq fun p => by simp only [Nat.unpair_pair]
  exact (enumerable_exists (A := fun n d => R n d ∧ ∃ t,
    ∀ x ∈ FiniteSequenceCoding.decode d, x ∈ EffectiveEnumerations.stage b t) hprod).of_eq fun n => by
    change (∃ d, R n d ∧ _) ↔ ∃ d, R n d ∧ _
    exact exists_congr fun d => and_congr_right fun _ => (hsub d).symm

theorem identityRules_enumerable : JointCE identityRules := by
  unfold JointCE identityRules
  exact (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair)
    (singletonCode_primitive.comp (Primrec.fst.comp Primrec.unpair))).computablePred.to_re

theorem identity_operator (B : Set ℕ) : operatorOf identityRules B = B := by
  ext n
  simp [operatorOf, identityRules, finiteSet_singleton]

theorem reducible_refl (A : Set ℕ) : Reducible A A := by
  obtain ⟨e, he⟩ := jointCE_iff_index identityRules |>.mp identityRules_enumerable
  refine ⟨e, ?_⟩
  have hop : operator e A = operatorOf identityRules A := by
    ext n
    simp [operator, operatorOf, he]
  exact hop.trans (identity_operator A)

theorem operator_empty (R : RuleRelation) : operatorOf R ∅ = {n | R n 0} := by
  ext n
  change (∃ d, R n d ∧ (finiteSet d : Set ℕ) ⊆ ∅) ↔ R n 0
  simp only [Set.subset_empty_iff, Finset.coe_eq_empty, finiteSet_empty]
  simp

def constantRules (A : Set ℕ) (n d : ℕ) : Prop := n ∈ A ∧ d = 0

theorem constantRules_enumerable (A : Set ℕ) (hA : REPred (fun n => n ∈ A)) :
    JointCE (constantRules A) := by
  unfold JointCE constantRules
  exact enumerable_inter (hA.comp (Computable.fst.comp Computable.unpair))
    ((Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 0)).computablePred.to_re)

theorem constant_operator (A B : Set ℕ) : operatorOf (constantRules A) B = A := by
  ext n
  simp [operatorOf, constantRules, finiteSet_empty 0 |>.mpr rfl]

theorem ce_reducible_everywhere (A : Set ℕ) (hA : REPred (fun n => n ∈ A)) (B : Set ℕ) :
    Reducible A B := by
  obtain ⟨e, he⟩ := jointCE_iff_index (constantRules A) |>.mp (constantRules_enumerable A hA)
  refine ⟨e, ?_⟩
  have hop : operator e B = operatorOf (constantRules A) B := by
    ext n
    simp [operator, operatorOf, he]
  exact hop.trans (constant_operator A B)

theorem reducible_empty_iff (A : Set ℕ) :
    Reducible A ∅ ↔ REPred (fun n => n ∈ A) := by
  constructor
  · rintro ⟨e, he⟩
    have h : REPred (fun n => indexedRule e n 0) :=
      (phi_recursive.comp (Computable.const e)
        (Primrec₂.natPair.comp Primrec.id (Primrec.const 0)).to_comp).dom_re
    exact h.of_eq fun n => by rw [← he, operator, operator_empty]; rfl
  · intro hA
    exact ce_reducible_everywhere A hA ∅

end Lemmatheca.ComputabilityTheory.EnumerationReducibility
