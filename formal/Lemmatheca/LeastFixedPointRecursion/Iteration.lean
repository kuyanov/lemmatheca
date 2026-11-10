import Lemmatheca.LeastFixedPointRecursion.Chains

/-! The actual bottom iterates, their numerical compiler iteration, and the union search. -/
namespace Lemmatheca.ComputabilityTheory.LeastFixedPointRecursion
open UniversalComputation RiceShapiroTheorem EffectiveOperators
open RicesTheorem (PartialFunction)
noncomputable section
open Classical

def iterateFromBottom (Φ : PartialFunction → PartialFunction) : ℕ → PartialFunction
  | 0 => RicesTheorem.bottom
  | n + 1 => Φ (iterateFromBottom Φ n)

def leastFixedPoint (Φ : PartialFunction → PartialFunction) : PartialFunction :=
  chainUnion (iterateFromBottom Φ)

def IsLeastFixedPoint (Φ : PartialFunction → PartialFunction) (f : PartialFunction) : Prop :=
  Function.IsFixedPt Φ f ∧ ∀ g, Function.IsFixedPt Φ g → GraphInclusion f g

theorem bottom_iterates_increasing (Φ : PartialFunction → PartialFunction) (hΦ : IsEffective Φ) :
    Increasing (iterateFromBottom Φ) := by
  intro n
  induction n with
  | zero =>
    intro x y hy
    exact (Part.notMem_none _ hy).elim
  | succ n ih => exact effective_monotone Φ hΦ _ _ ih

def bottomIndex : ℕ := fragmentIndex (pairListCode [])

def iterateIndex (r : ℕ) : ℕ → ℕ
  | 0 => bottomIndex
  | n + 1 => compiler r (iterateIndex r n)

theorem iterate_index_primitive : Primrec₂ iterateIndex := by
  have hq : Primrec₂ compiler :=
    UniformSelfReference.partial_family_compiler_primitive ruleSearchProgram
  have hs : Primrec₂ (fun (r : ℕ) (p : ℕ × ℕ) => compiler r p.2) :=
    hq.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact (Primrec.nat_rec (Primrec.const bottomIndex) hs).of_eq (fun r n => by
    induction n with
    | zero => rfl
    | succ n ih => simp only [iterateIndex, ih])

theorem bottom_index_eval (x : ℕ) : phi bottomIndex x = Part.none := by
  rw [bottomIndex, fragmentIndex_eval, empty_fragment.2]
  rfl

theorem iterate_index_eval (R : RuleRelation) (r : ℕ) (hr : EnumeratesRules r R)
    (hp : Positive R) (hc : Coherent R) (n x : ℕ) :
    phi (iterateIndex r n) x = iterateFromBottom (operator R) n x := by
  induction n generalizing x with
  | zero => simp only [iterateIndex, bottom_index_eval, iterateFromBottom, RicesTheorem.bottom]
  | succ n ih =>
    rw [iterateIndex, compiler_correct R r hr hp hc]
    have he : phi (iterateIndex r n) = iterateFromBottom (operator R) n := funext ih
    rw [he]
    rfl

def unionOffer (r x w : ℕ) : Option ℕ :=
  let v := boundedValue w.unpair.2 (iterateIndex r w.unpair.1) x
  if v = 0 then none else some (v - 1)

def unionSearch (r x : ℕ) : Part ℕ := Nat.rfindOpt (unionOffer r x)

theorem union_offer_primitive :
    Primrec (fun p : (ℕ × ℕ) × ℕ => unionOffer p.1.1 p.1.2 p.2) := by
  have hr : Primrec (fun p : (ℕ × ℕ) × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hx : Primrec (fun p : (ℕ × ℕ) × ℕ => p.1.2) := Primrec.snd.comp Primrec.fst
  have hu : Primrec (fun p : (ℕ × ℕ) × ℕ => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hv := boundedValue_primitive.comp
    (((Primrec.snd.comp hu).pair (iterate_index_primitive.comp hr (Primrec.fst.comp hu))).pair hx)
  exact (Primrec.ite (Primrec.eq.comp hv (Primrec.const 0)) (Primrec.const none)
    (Primrec.option_some.comp (Primrec.nat_sub.comp hv (Primrec.const 1)))).of_eq (fun _ => rfl)

theorem union_search_partial : Partrec₂ unionSearch := by
  exact Partrec.rfindOpt union_offer_primitive.to_comp.to₂

def unionSearchProgram : ℕ :=
  Classical.choose (phi_complete (Partrec₂.unpaired'.mpr union_search_partial))

def leastIndex (r : ℕ) : ℕ := specialize unionSearchProgram r

theorem union_search_program_eval (r x : ℕ) :
    phi unionSearchProgram (Nat.pair r x) = unionSearch r x := by
  have h := Classical.choose_spec (phi_complete (Partrec₂.unpaired'.mpr union_search_partial))
  simpa only [unionSearchProgram, Nat.unpaired, Nat.unpair_pair] using congrFun h (Nat.pair r x)

theorem least_index_primitive : Primrec leastIndex := by
  exact specialize_primitive.comp (Primrec.const unionSearchProgram) Primrec.id

theorem least_index_search_eval (r x : ℕ) :
    phi (leastIndex r) x = unionSearch r x := by
  rw [leastIndex, specialize_eval, union_search_program_eval]

private theorem rules_effective (R : RuleRelation) (r : ℕ)
    (hr : EnumeratesRules r R) (hp : Positive R) (hc : Coherent R) :
    IsEffective (operator R) :=
  ⟨R, hp, hc, (jointly_enumerable_iff_index R).mpr ⟨r, hr⟩, rfl⟩

private theorem union_search_sound (R : RuleRelation) (r : ℕ) (hr : EnumeratesRules r R)
    (hp : Positive R) (hc : Coherent R) (x y : ℕ) (hy : y ∈ unionSearch r x) :
    y ∈ leastFixedPoint (operator R) x := by
  obtain ⟨w, hw⟩ := Nat.rfindOpt_spec hy
  dsimp only [unionOffer] at hw
  split_ifs at hw with hz
  · simp at hw
  · have he := Option.mem_some_iff.mp hw
    have hcode : boundedValue w.unpair.2 (iterateIndex r w.unpair.1) x = y + 1 := by omega
    have hm := (phi_output (iterateIndex r w.unpair.1) x y).mpr ⟨w.unpair.2, hcode⟩
    rw [iterate_index_eval R r hr hp hc] at hm
    exact (chain_union_mem _ (bottom_iterates_increasing _ (rules_effective R r hr hp hc)) x y).mpr
      ⟨w.unpair.1, hm⟩

theorem union_search_eval (R : RuleRelation) (r : ℕ) (hr : EnumeratesRules r R)
    (hp : Positive R) (hc : Coherent R) (x : ℕ) :
    unionSearch r x = leastFixedPoint (operator R) x := by
  apply Part.ext
  intro y
  constructor
  · exact union_search_sound R r hr hp hc x y
  · intro hy
    obtain ⟨n, hn⟩ := (chain_union_mem _
      (bottom_iterates_increasing _ (rules_effective R r hr hp hc)) x y).mp hy
    rw [← iterate_index_eval R r hr hp hc n x] at hn
    obtain ⟨k, hk⟩ := (phi_output (iterateIndex r n) x y).mp hn
    have hd : (unionSearch r x).Dom := Nat.rfindOpt_dom.mpr
      ⟨Nat.pair n k, y, by simp [unionOffer, hk]⟩
    have hm := Part.get_mem hd
    have he := Part.mem_unique (union_search_sound R r hr hp hc x _ hm) hy
    simpa only [he] using hm

theorem least_index_eval (R : RuleRelation) (r : ℕ) (hr : EnumeratesRules r R)
    (hp : Positive R) (hc : Coherent R) (x : ℕ) :
    phi (leastIndex r) x = leastFixedPoint (operator R) x := by
  rw [least_index_search_eval, union_search_eval R r hr hp hc]

theorem least_fixed_point_equation (Φ : PartialFunction → PartialFunction) (hΦ : IsEffective Φ) :
    Function.IsFixedPt Φ (leastFixedPoint Φ) := by
  have hi := bottom_iterates_increasing Φ hΦ
  change Φ (chainUnion (iterateFromBottom Φ)) = chainUnion (iterateFromBottom Φ)
  rw [chain_continuity Φ hΦ _ hi]
  change chainUnion (fun n => iterateFromBottom Φ (n + 1)) = chainUnion (iterateFromBottom Φ)
  funext x
  apply Part.ext
  intro y
  rw [chain_union_mem _ (fun n => hi (n + 1)), chain_union_mem _ hi]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, hn⟩
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact (Part.notMem_none _ hn).elim
    | succ n => exact ⟨n, hn⟩

theorem least_fixed_point_least (Φ : PartialFunction → PartialFunction) (hΦ : IsEffective Φ)
    (g : PartialFunction) (hg : Function.IsFixedPt Φ g) :
    GraphInclusion (leastFixedPoint Φ) g := by
  have hall : ∀ n, GraphInclusion (iterateFromBottom Φ n) g := by
    intro n
    induction n with
    | zero => exact fun x y hy => (Part.notMem_none _ hy).elim
    | succ n ih =>
      have h := effective_monotone Φ hΦ (iterateFromBottom Φ n) g ih
      rw [hg] at h
      exact h
  exact union_below _ (bottom_iterates_increasing Φ hΦ) g hall

theorem first_recursion_theorem (Φ : PartialFunction → PartialFunction) (hΦ : IsEffective Φ) :
    IsLeastFixedPoint Φ (leastFixedPoint Φ) ∧ Nat.Partrec (leastFixedPoint Φ) := by
  refine ⟨⟨least_fixed_point_equation Φ hΦ, least_fixed_point_least Φ hΦ⟩, ?_⟩
  obtain ⟨R, hp, hc, he, rfl⟩ := hΦ
  obtain ⟨r, hr⟩ := (jointly_enumerable_iff_index R).mp he
  have hrec : Nat.Partrec (phi (leastIndex r)) := Partrec.nat_iff.mp
    (phi_recursive.comp (Computable.const (leastIndex r)) Computable.id)
  exact hrec.of_eq (least_index_eval R r hr hp hc)

theorem specified_first_recursion_theorem (R : RuleRelation) (r : ℕ)
    (hr : EnumeratesRules r R) (hp : Positive R) (hc : Coherent R) :
    phi (leastIndex r) = leastFixedPoint (operator R) ∧
      IsLeastFixedPoint (operator R) (leastFixedPoint (operator R)) := by
  exact ⟨funext (least_index_eval R r hr hp hc),
    (first_recursion_theorem (operator R) (rules_effective R r hr hp hc)).1⟩

/-- The actual least-solution program is also a semantic index fixed point. -/
theorem extensional_least_index_fixed_point (H : ℕ → ℕ) (hH : Computable H)
    (hext : IndexExtensional H) (a : ℕ) (ha : ∀ n, phi a n = Part.some (H n)) :
    phi (leastIndex (canonicalRuleIndex a)) =
      phi (H (leastIndex (canonicalRuleIndex a))) := by
  let r := canonicalRuleIndex a
  have hr : EnumeratesRules r (canonicalRules H) := canonical_rule_index_correct H a ha
  have hp := canonical_rules_positive H
  have hc := canonical_rules_coherent H hH hext
  have hl := specified_first_recursion_theorem (canonicalRules H) r hr hp hc
  have hfix : operator (canonicalRules H) (phi (leastIndex r)) = phi (leastIndex r) := by
    rw [hl.1]
    exact hl.2.1
  exact hfix.symm.trans (canonical_operator_correct H hH hext (leastIndex r))

end
end Lemmatheca.ComputabilityTheory.LeastFixedPointRecursion
