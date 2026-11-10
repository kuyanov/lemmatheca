import Lemmatheca.EffectiveOperators.Characterization
import Lemmatheca.TruthTableAndWeakTruthTableReductions.Examples

/-! Precomposition, parallel positive tests, negative graph answers, and redundant rules. -/
namespace Lemmatheca.Entry.EffectiveOperators

open Lemmatheca.ComputabilityTheory
open UniversalComputation RiceShapiroTheorem EffectiveOperators
open RicesTheorem (PartialFunction)

noncomputable section
open Classical

private theorem empty_inclusion (f : PartialFunction) :
    GraphInclusion (fragment (pairListCode [])) f := by
  rw [empty_fragment.2]
  intro x y h
  exact (Part.notMem_none _ h).elim

private theorem singleton_valid (x y : ℕ) : Valid (pairListCode [(x, y)]) := by
  simp [Valid, pairList_code, Consistent]

private theorem singleton_inclusion (f : PartialFunction) (x y : ℕ) (hy : y ∈ f x) :
    GraphInclusion (fragment (pairListCode [(x, y)])) f := by
  intro a b hab
  have h := (tableFunction_mem _ (singleton_valid x y) a b).mp hab
  rw [pairList_code] at h
  have he := List.mem_singleton.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact hy

private theorem one_rule_enumerable (d x y : ℕ) :
    JointlyEnumerable (fun c a b => c = d ∧ a = x ∧ b = y) := by
  have hu : Primrec (fun z : ℕ => z.unpair) := Primrec.unpair
  have hv := Primrec.unpair.comp (Primrec.snd.comp hu)
  exact ((Primrec.eq.comp (Primrec.fst.comp hu) (Primrec.const d)).and
    ((Primrec.eq.comp (Primrec.fst.comp hv) (Primrec.const x)).and
      (Primrec.eq.comp (Primrec.snd.comp hv) (Primrec.const y)))).computablePred.to_re

private theorem rules_union_enumerable (R S : RuleRelation)
    (hR : JointlyEnumerable R) (hS : JointlyEnumerable S) :
    JointlyEnumerable (fun d x y => R d x y ∨ S d x y) :=
  enumerable_union hR hS

private theorem fragment_output_enumerable (k : ℕ → ℕ) (hk : Computable k) :
    REPred (fun z : ℕ => z.unpair.2.unpair.2 ∈ fragment z.unpair.1 (k z.unpair.2.unpair.1)) := by
  have hu : Computable (fun z : ℕ => z.unpair) := Computable.unpair
  have hv := Computable.unpair.comp (Computable.snd.comp hu)
  have hc := Primrec₂.natPair.to_comp.comp (Computable.fst.comp hu)
    (Primrec₂.natPair.to_comp.comp (hk.comp (Computable.fst.comp hv)) (Computable.snd.comp hv))
  apply REPred.of_eq ((output_jointly_enumerable fragmentIndex fragmentIndex_primitive.to_comp).comp hc)
  intro z
  simp only [Nat.unpair_pair, fragmentIndex_eval]

theorem incoherent_empty_rules :
    let R : RuleRelation := fun d x y => d = pairListCode [] ∧ x = 0 ∧ (y = 0 ∨ y = 1)
    Positive R ∧ JointlyEnumerable R ∧ ¬ Coherent R ∧
      RuleOutput R RicesTheorem.bottom 0 0 ∧ RuleOutput R RicesTheorem.bottom 0 1 := by
  dsimp only
  let R : RuleRelation := fun d x y => d = pairListCode [] ∧ x = 0 ∧ (y = 0 ∨ y = 1)
  have hp : Positive R := by
    rintro d x y ⟨rfl, _, _⟩
    exact empty_fragment.1
  have he : JointlyEnumerable R := by
    apply (rules_union_enumerable _ _ (one_rule_enumerable (pairListCode []) 0 0)
      (one_rule_enumerable (pairListCode []) 0 1)).of_eq
    intro z
    change ((_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _)) ↔ (_ ∧ _ ∧ (_ ∨ _))
    tauto
  have h0 : R (pairListCode []) 0 0 := ⟨rfl, rfl, Or.inl rfl⟩
  have h1 : R (pairListCode []) 0 1 := ⟨rfl, rfl, Or.inr rfl⟩
  refine ⟨hp, he, ?_, ⟨pairListCode [], empty_inclusion _, h0⟩,
    ⟨pairListCode [], empty_inclusion _, h1⟩⟩
  intro hc
  have h := hc (pairListCode []) (pairListCode []) 0 0 1 h0 h1
    (subfragments_compatible RicesTheorem.bottom _ _ empty_fragment.1 empty_fragment.1
      (empty_inclusion _) (empty_inclusion _))
  omega

def precompositionRules (k : ℕ → ℕ) : RuleRelation :=
  fun d x y => Valid d ∧ (k x, y) ∈ pairList d

theorem precomposition_rules (k : ℕ → ℕ) (hk : Computable k) :
    Positive (precompositionRules k) ∧ Coherent (precompositionRules k) ∧
      JointlyEnumerable (precompositionRules k) := by
  refine ⟨fun _ _ _ h => h.1, ?_, ?_⟩
  · intro d c x y z hd hc hcompat
    exact hcompat.2.2 (k x) y z
      ((tableFunction_mem _ hd.1 _ _).mpr hd.2)
      ((tableFunction_mem _ hc.1 _ _).mpr hc.2)
  · have hv : REPred (fun z : ℕ => Valid z.unpair.1) :=
      (valid_primitive.comp (Primrec.fst.comp Primrec.unpair)).computablePred.to_re
    apply (enumerable_inter hv (fragment_output_enumerable k hk)).of_eq
    intro z
    change (Valid _ ∧ _ ∈ fragment _ _) ↔ (Valid _ ∧ (_, _) ∈ pairList _)
    constructor
    · rintro ⟨hd, hy⟩
      exact ⟨hd, (tableFunction_mem _ hd _ _).mp hy⟩
    · rintro ⟨hd, hy⟩
      exact ⟨hd, (tableFunction_mem _ hd _ _).mpr hy⟩

theorem precomposition_operator (k : ℕ → ℕ) (f : PartialFunction) (x : ℕ) :
    operator (precompositionRules k) f x = f (k x) := by
  have hp : Positive (precompositionRules k) := fun _ _ _ h => h.1
  have hc : Coherent (precompositionRules k) := by
    intro d c x y z hd hc hcompat
    exact hcompat.2.2 (k x) y z
      ((tableFunction_mem _ hd.1 _ _).mpr hd.2)
      ((tableFunction_mem _ hc.1 _ _).mpr hc.2)
  apply Part.ext
  intro y
  rw [operator_mem _ hp hc]
  constructor
  · rintro ⟨d, hdf, hd⟩
    exact hdf (k x) y ((tableFunction_mem _ hd.1 _ _).mpr hd.2)
  · intro hy
    refine ⟨pairListCode [(k x, y)], singleton_inclusion f _ _ hy, singleton_valid _ _, ?_⟩
    simp only [pairList_code, List.mem_singleton]

def parallelRules : RuleRelation :=
  fun d _ y => Valid d ∧ y = 0 ∧ ∃ a b, (a, b) ∈ pairList d ∧ (a = 0 ∨ a = 1)

def parallel (f : PartialFunction) (_x : ℕ) : Part ℕ :=
  if (f 0).Dom ∨ (f 1).Dom then Part.some 0 else Part.none

theorem parallel_rules : Positive parallelRules ∧ Coherent parallelRules ∧
    JointlyEnumerable parallelRules := by
  refine ⟨fun _ _ _ h => h.1, ?_, ?_⟩
  · intro d c x y z hd hc _
    exact hd.2.1.trans hc.2.1.symm
  · have hu : Computable (fun z : ℕ => z.unpair.1) :=
      Computable.fst.comp Computable.unpair
    have h0 := (phi_recursive.comp (fragmentIndex_primitive.to_comp.comp hu)
      (Computable.const 0)).dom_re
    have h1 := (phi_recursive.comp (fragmentIndex_primitive.to_comp.comp hu)
      (Computable.const 1)).dom_re
    have hp : REPred (fun z : ℕ => Valid z.unpair.1 ∧ z.unpair.2.unpair.2 = 0) := by
      have u := Primrec.unpair
      have v := Primrec.unpair.comp (Primrec.snd.comp u)
      exact ((valid_primitive.comp (Primrec.fst.comp u)).and
        (Primrec.eq.comp (Primrec.snd.comp v) (Primrec.const 0))).computablePred.to_re
    apply (enumerable_inter hp (enumerable_union h0 h1)).of_eq
    intro z
    simp only [fragmentIndex_eval]
    constructor
    · rintro ⟨⟨hd, hy⟩, h0 | h1⟩
      · obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h0
        exact ⟨hd, hy, 0, v, (tableFunction_mem _ hd _ _).mp hv, Or.inl rfl⟩
      · obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h1
        exact ⟨hd, hy, 1, v, (tableFunction_mem _ hd _ _).mp hv, Or.inr rfl⟩
    · rintro ⟨hd, hy, a, b, hab, ha | ha⟩
      · subst a
        exact ⟨⟨hd, hy⟩, Or.inl (Part.dom_iff_mem.mpr
          ⟨b, (tableFunction_mem _ hd _ _).mpr hab⟩)⟩
      · subst a
        exact ⟨⟨hd, hy⟩, Or.inr (Part.dom_iff_mem.mpr
          ⟨b, (tableFunction_mem _ hd _ _).mpr hab⟩)⟩

theorem parallel_operator (f : PartialFunction) : operator parallelRules f = parallel f := by
  funext x
  apply Part.ext
  intro y
  rw [operator_mem _ parallel_rules.1 parallel_rules.2.1]
  have hraw : RuleOutput parallelRules f x y ↔
      y = 0 ∧ ((f 0).Dom ∨ (f 1).Dom) := by
    constructor
    · rintro ⟨d, hdf, hd, hy, a, b, hab, ha | ha⟩
      · subst a
        exact ⟨hy, Or.inl (Part.dom_iff_mem.mpr
          ⟨b, hdf 0 b ((tableFunction_mem _ hd _ _).mpr hab)⟩)⟩
      · subst a
        exact ⟨hy, Or.inr (Part.dom_iff_mem.mpr
          ⟨b, hdf 1 b ((tableFunction_mem _ hd _ _).mpr hab)⟩)⟩
    · rintro ⟨rfl, h0 | h1⟩
      · obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h0
        refine ⟨pairListCode [(0, v)], singleton_inclusion f _ _ hv,
          singleton_valid _ _, rfl, 0, v, ?_, Or.inl rfl⟩
        simp only [pairList_code, List.mem_singleton]
      · obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h1
        refine ⟨pairListCode [(1, v)], singleton_inclusion f _ _ hv,
          singleton_valid _ _, rfl, 1, v, ?_, Or.inr rfl⟩
        simp only [pairList_code, List.mem_singleton]
  rw [hraw]
  by_cases h : (f 0).Dom ∨ (f 1).Dom <;> simp [parallel, h]

theorem parallel_strict_order_failures (x : ℕ) (K : ℕ → Part ℕ) :
    let leftMissing := tableFunction [(1, 0)]
    let rightMissing := tableFunction [(0, 0)]
    parallel leftMissing x = Part.some 0 ∧
      (leftMissing 0).bind K = Part.none ∧
      parallel rightMissing x = Part.some 0 ∧ (rightMissing 1).bind K = Part.none := by
  simp [parallel, tableFunction, Part.ofOption]

def codedGraph (f : PartialFunction) : Set ℕ := {z | z.unpair.2 ∈ f z.unpair.1}

def negativeMembership (f : PartialFunction) (_x : ℕ) : Part ℕ :=
  if 0 ∈ f 0 then Part.none else Part.some 0

theorem negative_graph_program_eval (f : PartialFunction) (x : ℕ) :
    OracleComputation.eval (codedGraph f) Lemmatheca.Entry.TruthTableAndWeakTruthTableReductions.partialOneQuery x =
      negativeMembership f x := by
  rw [Lemmatheca.Entry.TruthTableAndWeakTruthTableReductions.partial_one_query_eval]
  rfl

theorem negative_membership_obstruction :
    GraphInclusion RicesTheorem.bottom (tableFunction [(0, 0)]) ∧
      negativeMembership RicesTheorem.bottom 0 = Part.some 0 ∧
      negativeMembership (tableFunction [(0, 0)]) 0 = Part.none ∧
      ¬ IsEffective negativeMembership := by
  have hi : GraphInclusion RicesTheorem.bottom (tableFunction [(0, 0)]) := by
    intro x y hy
    exact (Part.notMem_none _ hy).elim
  have hb : negativeMembership RicesTheorem.bottom 0 = Part.some 0 := by
    simp [negativeMembership, RicesTheorem.bottom]
  have hs : negativeMembership (tableFunction [(0, 0)]) 0 = Part.none := by
    simp [negativeMembership, tableFunction, Part.ofOption]
  refine ⟨hi, hb, hs, ?_⟩
  intro heff
  have h := effective_monotone negativeMembership heff _ _ hi 0 0
    (by rw [hb]; exact Part.mem_some 0)
  rw [hs] at h
  exact Part.notMem_none _ h

def emptyEvidenceRules : RuleRelation :=
  fun d x y => d = pairListCode [] ∧ x = 0 ∧ y = 0

def redundantEvidenceRules : RuleRelation :=
  fun d x y => emptyEvidenceRules d x y ∨
    (d = pairListCode [(0, 7)] ∧ x = 0 ∧ y = 0)

theorem redundant_rules_properties :
    Positive emptyEvidenceRules ∧ Coherent emptyEvidenceRules ∧ JointlyEnumerable emptyEvidenceRules ∧
      Positive redundantEvidenceRules ∧ Coherent redundantEvidenceRules ∧
        JointlyEnumerable redundantEvidenceRules := by
  have hp : Positive emptyEvidenceRules := by
    rintro d x y ⟨rfl, _, _⟩
    exact empty_fragment.1
  have hc : Coherent emptyEvidenceRules := by
    intro d c x y z hd he _
    exact hd.2.2.trans he.2.2.symm
  have he : JointlyEnumerable emptyEvidenceRules := one_rule_enumerable _ _ _
  refine ⟨hp, hc, he, ?_, ?_, ?_⟩
  · intro d x y h
    rcases h with h | h
    · exact hp d x y h
    · rcases h with ⟨rfl, _, _⟩
      exact singleton_valid _ _
  · intro d c x y z hd he _
    have hy : y = 0 := hd.elim (fun h => h.2.2) (fun h => h.2.2)
    have hz : z = 0 := he.elim (fun h => h.2.2) (fun h => h.2.2)
    exact hy.trans hz.symm
  · exact rules_union_enumerable _ _ he (one_rule_enumerable _ _ _)

theorem redundant_rules_distinct : emptyEvidenceRules ≠ redundantEvidenceRules := by
  intro h
  have hc : redundantEvidenceRules (pairListCode [(0, 7)]) 0 0 :=
    Or.inr ⟨rfl, rfl, rfl⟩
  rw [← h] at hc
  have he := congrArg pairList hc.1
  simp only [pairList_code, List.cons_ne_nil] at he

private theorem zero_rule_operator (R : RuleRelation) (hp : Positive R) (hc : Coherent R)
    (hzero : ∀ d x y, R d x y → x = 0 ∧ y = 0)
    (hempty : R (pairListCode []) 0 0) (f : PartialFunction) (x : ℕ) :
    operator R f x = if x = 0 then Part.some 0 else Part.none := by
  apply Part.ext
  intro y
  rw [operator_mem _ hp hc]
  have hout : RuleOutput R f x y ↔ x = 0 ∧ y = 0 := by
    constructor
    · rintro ⟨d, _, hd⟩
      exact hzero d x y hd
    · rintro ⟨rfl, rfl⟩
      exact ⟨pairListCode [], empty_inclusion f, hempty⟩
  rw [hout]
  by_cases hx : x = 0 <;> simp [hx]

theorem redundant_rules_operator (f : PartialFunction) (x : ℕ) :
    operator emptyEvidenceRules f x = (if x = 0 then Part.some 0 else Part.none) ∧
      operator redundantEvidenceRules f x = (if x = 0 then Part.some 0 else Part.none) := by
  obtain ⟨hp, hc, _, hsp, hsc, _⟩ := redundant_rules_properties
  constructor
  · exact zero_rule_operator _ hp hc (fun _ _ _ h => ⟨h.2.1, h.2.2⟩)
      ⟨rfl, rfl, rfl⟩ f x
  · apply zero_rule_operator _ hsp hsc _ (Or.inl ⟨rfl, rfl, rfl⟩) f x
    intro d x y h
    exact h.elim (fun h => ⟨h.2.1, h.2.2⟩) (fun h => ⟨h.2.1, h.2.2⟩)

end
end Lemmatheca.Entry.EffectiveOperators
