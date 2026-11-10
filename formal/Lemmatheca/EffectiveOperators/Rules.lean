import Lemmatheca.RiceShapiroTheorem.Basis

/-! Coherent positive rules on the existing Rice–Shapiro finite graphs. -/
namespace Lemmatheca.ComputabilityTheory.EffectiveOperators

open UniversalComputation RiceShapiroTheorem
open RicesTheorem (PartialFunction)

noncomputable section
open Classical

abbrev RuleRelation := ℕ → ℕ → ℕ → Prop

def Compatible (d c : ℕ) : Prop :=
  Valid d ∧ Valid c ∧ ∀ x y z, y ∈ fragment d x → z ∈ fragment c x → y = z

theorem compatible_iff_consistent_append (d c : ℕ) :
    Compatible d c ↔ Consistent (pairList d ++ pairList c) := by
  constructor
  · rintro ⟨hd, hc, hcross⟩ p hp q hq he
    rcases List.mem_append.mp hp with hp | hp <;>
      rcases List.mem_append.mp hq with hq | hq
    · exact hd p hp q hq he
    · have hp' : p.2 ∈ fragment d p.1 := (tableFunction_mem _ hd _ _).mpr (by simpa using hp)
      have hq' : q.2 ∈ fragment c p.1 := he ▸ ((tableFunction_mem _ hc _ _).mpr (by simpa using hq))
      exact hcross p.1 p.2 q.2 hp' hq'
    · have hp' : p.2 ∈ fragment c q.1 := he ▸ ((tableFunction_mem _ hc _ _).mpr (by simpa using hp))
      have hq' : q.2 ∈ fragment d q.1 := (tableFunction_mem _ hd _ _).mpr (by simpa using hq)
      exact (hcross q.1 q.2 p.2 hq' hp').symm
    · exact hc p hp q hq he
  · intro h
    have hd : Valid d := fun p hp q hq he =>
      h p (List.mem_append_left _ hp) q (List.mem_append_left _ hq) he
    have hc : Valid c := fun p hp q hq he =>
      h p (List.mem_append_right _ hp) q (List.mem_append_right _ hq) he
    refine ⟨hd, hc, ?_⟩
    intro x y z hy hz
    exact h (x, y) (List.mem_append_left _ ((tableFunction_mem _ hd x y).mp hy))
      (x, z) (List.mem_append_right _ ((tableFunction_mem _ hc x z).mp hz)) rfl

theorem compatible_common_fragment (d c : ℕ) (h : Compatible d c) :
    let b := pairListCode (pairList d ++ pairList c)
    Valid b ∧ GraphInclusion (fragment d) (fragment b) ∧
      GraphInclusion (fragment c) (fragment b) := by
  dsimp only
  have hs := (compatible_iff_consistent_append d c).mp h
  have hb : Valid (pairListCode (pairList d ++ pairList c)) := by
    simpa only [Valid, pairList_code] using hs
  refine ⟨hb, ?_, ?_⟩
  · intro x y hy
    apply (tableFunction_mem _ hb x y).mpr
    rw [pairList_code]
    exact List.mem_append_left _ ((tableFunction_mem _ h.1 x y).mp hy)
  · intro x y hy
    apply (tableFunction_mem _ hb x y).mpr
    rw [pairList_code]
    exact List.mem_append_right _ ((tableFunction_mem _ h.2.1 x y).mp hy)

theorem subfragments_compatible (f : PartialFunction) (d c : ℕ)
    (hd : Valid d) (hc : Valid c)
    (hdf : GraphInclusion (fragment d) f) (hcf : GraphInclusion (fragment c) f) :
    Compatible d c := by
  exact ⟨hd, hc, fun x y z hy hz => Part.mem_unique (hdf x y hy) (hcf x z hz)⟩

def ruleCode (d x y : ℕ) : ℕ := Nat.pair d (Nat.pair x y)

def JointlyEnumerable (R : RuleRelation) : Prop :=
  REPred (fun z : ℕ => R z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2)

def Positive (R : RuleRelation) : Prop := ∀ d x y, R d x y → Valid d

def Coherent (R : RuleRelation) : Prop :=
  ∀ d c x y z, R d x y → R c x z → Compatible d c → y = z

def EnumeratesRules (r : ℕ) (R : RuleRelation) : Prop :=
  ∀ d x y, ruleCode d x y ∈ EffectiveEnumerations.indexSet r ↔ R d x y

theorem jointly_enumerable_iff_index (R : RuleRelation) :
    JointlyEnumerable R ↔ ∃ r, EnumeratesRules r R := by
  constructor
  · intro hR
    obtain ⟨r, hr⟩ := (enumerable_iff_index _).mp hR
    refine ⟨r, fun d x y => ?_⟩
    simpa only [ruleCode, Nat.unpair_pair, EffectiveEnumerations.indexSet, Membership.mem, Set.Mem, Set.ofPred] using (hr (ruleCode d x y)).symm
  · rintro ⟨r, hr⟩
    apply (enumerable_iff_index _).mpr
    refine ⟨r, fun z => ?_⟩
    have h := hr z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2
    simpa only [ruleCode, Nat.pair_unpair, EffectiveEnumerations.indexSet, Membership.mem, Set.Mem, Set.ofPred] using h.symm

def RuleOutput (R : RuleRelation) (f : PartialFunction) (x y : ℕ) : Prop :=
  ∃ d, GraphInclusion (fragment d) f ∧ R d x y

def operator (R : RuleRelation) (f : PartialFunction) (x : ℕ) : Part ℕ :=
  ⟨∃ y, RuleOutput R f x y, fun h => Classical.choose h⟩

def IsEffective (Φ : PartialFunction → PartialFunction) : Prop :=
  ∃ R, Positive R ∧ Coherent R ∧ JointlyEnumerable R ∧ Φ = operator R

theorem rule_output_unique (R : RuleRelation) (hpos : Positive R) (hcoh : Coherent R)
    (f : PartialFunction) (x y z : ℕ)
    (hy : RuleOutput R f x y) (hz : RuleOutput R f x z) : y = z := by
  obtain ⟨d, hd, hy⟩ := hy
  obtain ⟨c, hc, hz⟩ := hz
  exact hcoh d c x y z hy hz
    (subfragments_compatible f d c (hpos d x y hy) (hpos c x z hz) hd hc)

theorem operator_mem (R : RuleRelation) (hpos : Positive R) (hcoh : Coherent R)
    (f : PartialFunction) (x y : ℕ) :
    y ∈ operator R f x ↔ RuleOutput R f x y := by
  constructor
  · rintro ⟨h, he⟩
    have hs : RuleOutput R f x (Classical.choose h) := Classical.choose_spec h
    exact he ▸ hs
  · intro hy
    have h : ∃ y, RuleOutput R f x y := ⟨y, hy⟩
    refine ⟨h, ?_⟩
    exact rule_output_unique R hpos hcoh f x _ y (Classical.choose_spec h) hy

theorem empty_rules_operator (f : PartialFunction) :
    operator (fun _ _ _ => False) f = RicesTheorem.bottom := by
  funext x
  change operator (fun _ _ _ => False) f x = Part.none
  apply Part.eq_none_iff'.mpr
  change ¬ ∃ y, RuleOutput (fun _ _ _ => False) f x y
  rintro ⟨y, d, _, h⟩
  exact h

theorem operator_monotone (R : RuleRelation) (hpos : Positive R) (hcoh : Coherent R)
    (f g : PartialFunction) (hfg : GraphInclusion f g) :
    GraphInclusion (operator R f) (operator R g) := by
  intro x y hy
  obtain ⟨d, hd, hr⟩ := (operator_mem R hpos hcoh f x y).mp hy
  apply (operator_mem R hpos hcoh g x y).mpr
  exact ⟨d, fun z v hv => hfg z v (hd z v hv), hr⟩

theorem operator_finite_information (R : RuleRelation) (hpos : Positive R)
    (hcoh : Coherent R) (f : PartialFunction) (x y : ℕ) :
    y ∈ operator R f x ↔
      ∃ d, Valid d ∧ GraphInclusion (fragment d) f ∧ y ∈ operator R (fragment d) x := by
  constructor
  · intro hy
    obtain ⟨d, hd, hr⟩ := (operator_mem R hpos hcoh f x y).mp hy
    refine ⟨d, hpos d x y hr, hd, ?_⟩
    exact (operator_mem R hpos hcoh (fragment d) x y).mpr ⟨d, fun _ _ h => h, hr⟩
  · rintro ⟨d, _, hd, hy⟩
    exact operator_monotone R hpos hcoh (fragment d) f hd x y hy

theorem effective_monotone (Φ : PartialFunction → PartialFunction) (hΦ : IsEffective Φ)
    (f g : PartialFunction) (hfg : GraphInclusion f g) :
    GraphInclusion (Φ f) (Φ g) := by
  obtain ⟨R, hp, hc, _, rfl⟩ := hΦ
  exact operator_monotone R hp hc f g hfg

end
end Lemmatheca.ComputabilityTheory.EffectiveOperators
