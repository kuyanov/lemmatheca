import Lemmatheca.LeastFixedPointRecursion.Iteration
import Lemmatheca.EffectiveOperators.Examples

namespace Lemmatheca.Entry.LeastFixedPointRecursion
open Lemmatheca.ComputabilityTheory
open UniversalComputation RiceShapiroTheorem
open Lemmatheca.ComputabilityTheory.EffectiveOperators
open Lemmatheca.ComputabilityTheory.LeastFixedPointRecursion
open RicesTheorem (PartialFunction)
noncomputable section
open Classical

private theorem empty_inclusion (f : PartialFunction) :
    GraphInclusion (fragment (pairListCode [])) f := by
  rw [empty_fragment.2]
  exact fun _ _ h => (Part.notMem_none _ h).elim

private theorem singleton_valid (x y : ℕ) : Valid (pairListCode [(x, y)]) := by
  simp [Valid, pairList_code, Consistent]

private theorem singleton_inclusion (f : PartialFunction) (x y : ℕ) (hy : y ∈ f x) :
    GraphInclusion (fragment (pairListCode [(x, y)])) f := by
  intro a b hab
  have h := (tableFunction_mem _ (singleton_valid x y) a b).mp hab
  rw [pairList_code] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp h)
  exact hy

private theorem mapped_fragment_output_enumerable (k l : ℕ → ℕ)
    (hk : Computable k) (hl : Computable l) :
    REPred (fun z : ℕ => l z.unpair.2.unpair.2 ∈ fragment z.unpair.1 (k z.unpair.2.unpair.1)) := by
  have hu : Computable (fun z : ℕ => z.unpair) := Computable.unpair
  have hv := Computable.unpair.comp (Computable.snd.comp hu)
  have hc := Primrec₂.natPair.to_comp.comp (Computable.fst.comp hu)
    (Primrec₂.natPair.to_comp.comp (hk.comp (Computable.fst.comp hv))
      (hl.comp (Computable.snd.comp hv)))
  apply REPred.of_eq ((output_jointly_enumerable fragmentIndex fragmentIndex_primitive.to_comp).comp hc)
  intro z
  simp only [Nat.unpair_pair, fragmentIndex_eval]

def successorRules : RuleRelation := fun d x y =>
  Valid d ∧ (if x = 0 then y = 0 else 0 < y ∧ (x - 1, y - 1) ∈ pairList d)

def successorOperator (f : PartialFunction) : PartialFunction
  | 0 => Part.some 0
  | n + 1 => (f n).map Nat.succ

theorem successor_rules : Positive successorRules ∧ Coherent successorRules ∧
    JointlyEnumerable successorRules := by
  refine ⟨fun _ _ _ h => h.1, ?_, ?_⟩
  · intro d c x y z hd hc hcompat
    by_cases hx : x = 0
    · simp only [successorRules, hx, ite_true] at hd hc
      exact hd.2.trans hc.2.symm
    · have hy : 0 < y ∧ (x - 1, y - 1) ∈ pairList d := by simpa [hx] using hd.2
      have hz : 0 < z ∧ (x - 1, z - 1) ∈ pairList c := by simpa [hx] using hc.2
      have he := hcompat.2.2 (x - 1) (y - 1) (z - 1)
        ((tableFunction_mem _ hd.1 _ _).mpr hy.2)
        ((tableFunction_mem _ hc.1 _ _).mpr hz.2)
      omega
  · have hu := Primrec.unpair
    have hv := Primrec.unpair.comp (Primrec.snd.comp hu)
    have hx := Primrec.fst.comp hv
    have hy := Primrec.snd.comp hv
    have hvalid := (valid_primitive.comp (Primrec.fst.comp hu)).computablePred.to_re
    have hzero := ((Primrec.eq.comp hx (Primrec.const 0)).and
      (Primrec.eq.comp hy (Primrec.const 0))).computablePred.to_re
    have hpos := ((Primrec.eq.comp hx (Primrec.const 0)).not.and
      (Primrec.nat_lt.comp (Primrec.const 0) hy)).computablePred.to_re
    have hpred : Computable (fun x : ℕ => x - 1) :=
      (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)).to_comp
    apply (enumerable_inter hvalid (enumerable_union hzero
      (enumerable_inter hpos (mapped_fragment_output_enumerable _ _ hpred hpred)))).of_eq
    intro z
    by_cases hx0 : z.unpair.2.unpair.1 = 0
    · simp [successorRules, hx0]
    · simp only [successorRules, hx0, ite_false, false_and, false_or, not_false_eq_true,
        true_and]
      constructor
      · rintro ⟨hd, hy, hm⟩
        exact ⟨hd, hy, (tableFunction_mem _ hd _ _).mp hm⟩
      · rintro ⟨hd, hy, hm⟩
        exact ⟨hd, hy, (tableFunction_mem _ hd _ _).mpr hm⟩

theorem successor_operator_correct : operator successorRules = successorOperator := by
  funext f x
  apply Part.ext
  intro y
  rw [operator_mem _ successor_rules.1 successor_rules.2.1]
  cases x with
  | zero =>
    change RuleOutput successorRules f 0 y ↔ y ∈ Part.some 0
    constructor
    · rintro ⟨d, _, hd⟩
      simpa [successorRules] using hd.2
    · intro hy
      have hy0 : y = 0 := Part.mem_some_iff.mp hy
      subst y
      exact ⟨pairListCode [], empty_inclusion f, empty_fragment.1, by simp⟩
  | succ x =>
    change RuleOutput successorRules f (x + 1) y ↔ y ∈ (f x).map Nat.succ
    rw [Part.mem_map_iff]
    constructor
    · rintro ⟨d, hdf, hd⟩
      have hr : 0 < y ∧ (x, y - 1) ∈ pairList d := by simpa [successorRules] using hd.2
      refine ⟨y - 1, hdf x (y - 1) ((tableFunction_mem _ hd.1 _ _).mpr hr.2), ?_⟩
      omega
    · rintro ⟨v, hv, rfl⟩
      refine ⟨pairListCode [(x, v)], singleton_inclusion f x v hv,
        singleton_valid _ _, ?_⟩
      simp [pairList_code]

theorem successor_iterates (n x y : ℕ) :
    y ∈ iterateFromBottom successorOperator n x ↔ x < n ∧ y = x := by
  induction n generalizing x y with
  | zero => simp [iterateFromBottom, RicesTheorem.bottom]
  | succ n ih =>
    cases x with
    | zero => simp [iterateFromBottom, successorOperator]
    | succ x =>
      simp only [iterateFromBottom, successorOperator, Part.mem_map_iff]
      constructor
      · rintro ⟨v, hv, he⟩
        obtain ⟨hx, rfl⟩ := (ih x v).mp hv
        exact ⟨by omega, he.symm⟩
      · rintro ⟨hx, rfl⟩
        exact ⟨x, (ih x x).mpr ⟨by omega, rfl⟩, rfl⟩

theorem successor_least_fixed_point :
    leastFixedPoint successorOperator = (fun x => Part.some x) ∧
      IsLeastFixedPoint successorOperator (fun x => Part.some x) := by
  have heff : IsEffective successorOperator :=
    ⟨successorRules, successor_rules.1, successor_rules.2.1, successor_rules.2.2,
      successor_operator_correct.symm⟩
  have he : leastFixedPoint successorOperator = (fun x => Part.some x) := by
    funext x
    apply Part.ext
    intro y
    rw [leastFixedPoint, chain_union_mem _ (bottom_iterates_increasing _ heff)]
    simp only [successor_iterates, Part.mem_some_iff]
    constructor
    · rintro ⟨n, _, hy⟩
      exact hy
    · intro hy
      exact ⟨x + 1, by omega, hy⟩
  exact ⟨he, he ▸ (first_recursion_theorem _ heff).1⟩

def shiftRules : RuleRelation := fun d x y =>
  Valid d ∧ (if x = 0 then y = 0 else (x + 1, y) ∈ pairList d)

def shiftOperator (f : PartialFunction) (x : ℕ) : Part ℕ :=
  if x = 0 then Part.some 0 else f (x + 1)

def singletonZero (x : ℕ) : Part ℕ := if x = 0 then Part.some 0 else Part.none

def constantTail (k x : ℕ) : Part ℕ := Part.some (if x = 0 then 0 else k)

theorem shift_rules : Positive shiftRules ∧ Coherent shiftRules ∧ JointlyEnumerable shiftRules := by
  refine ⟨fun _ _ _ h => h.1, ?_, ?_⟩
  · intro d c x y z hd hc hcompat
    by_cases hx : x = 0
    · have hy : y = 0 := by simpa [shiftRules, hx] using hd.2
      have hz : z = 0 := by simpa [shiftRules, hx] using hc.2
      exact hy.trans hz.symm
    · have hy : (x + 1, y) ∈ pairList d := by simpa [shiftRules, hx] using hd.2
      have hz : (x + 1, z) ∈ pairList c := by simpa [shiftRules, hx] using hc.2
      exact hcompat.2.2 (x + 1) y z
        ((tableFunction_mem _ hd.1 _ _).mpr hy)
        ((tableFunction_mem _ hc.1 _ _).mpr hz)
  · have hu := Primrec.unpair
    have hv := Primrec.unpair.comp (Primrec.snd.comp hu)
    have hx := Primrec.fst.comp hv
    have hy := Primrec.snd.comp hv
    have hvalid := (valid_primitive.comp (Primrec.fst.comp hu)).computablePred.to_re
    have hzero := ((Primrec.eq.comp hx (Primrec.const 0)).and
      (Primrec.eq.comp hy (Primrec.const 0))).computablePred.to_re
    have hnonzero := (Primrec.eq.comp hx (Primrec.const 0)).not.computablePred.to_re
    apply (enumerable_inter hvalid (enumerable_union hzero
      (enumerable_inter hnonzero (mapped_fragment_output_enumerable Nat.succ id
        Computable.succ Computable.id)))).of_eq
    intro z
    by_cases hx0 : z.unpair.2.unpair.1 = 0
    · simp [shiftRules, hx0]
    · simp only [shiftRules, hx0, ite_false, false_and, false_or, not_false_eq_true,
        true_and, id_eq]
      constructor
      · rintro ⟨hd, hm⟩
        exact ⟨hd, (tableFunction_mem _ hd _ _).mp hm⟩
      · rintro ⟨hd, hm⟩
        exact ⟨hd, (tableFunction_mem _ hd _ _).mpr hm⟩

theorem shift_operator_correct : operator shiftRules = shiftOperator := by
  funext f x
  apply Part.ext
  intro y
  rw [operator_mem _ shift_rules.1 shift_rules.2.1]
  by_cases hx : x = 0
  · subst x
    simp only [shiftOperator, ite_true]
    constructor
    · rintro ⟨d, _, hd⟩
      simpa [shiftRules] using hd.2
    · intro hy
      have hy0 : y = 0 := Part.mem_some_iff.mp hy
      subst y
      exact ⟨pairListCode [], empty_inclusion f, empty_fragment.1, by simp⟩
  · simp only [shiftOperator, hx, ite_false]
    constructor
    · rintro ⟨d, hdf, hd⟩
      have hm : (x + 1, y) ∈ pairList d := by simpa [shiftRules, hx] using hd.2
      exact hdf _ _ ((tableFunction_mem _ hd.1 _ _).mpr hm)
    · intro hy
      refine ⟨pairListCode [(x + 1, y)], singleton_inclusion f _ _ hy,
        singleton_valid _ _, ?_⟩
      simp [hx, pairList_code]

theorem shift_iterates (n : ℕ) :
    iterateFromBottom shiftOperator (n + 1) = singletonZero := by
  induction n with
  | zero => funext x; simp [iterateFromBottom, shiftOperator, singletonZero, RicesTheorem.bottom]
  | succ n ih =>
    rw [iterateFromBottom, ih]
    funext x
    by_cases hx : x = 0
    · simp [shiftOperator, singletonZero, hx]
    · simp [shiftOperator, singletonZero, hx]

theorem shift_least_fixed_point :
    leastFixedPoint shiftOperator = singletonZero ∧
      IsLeastFixedPoint shiftOperator singletonZero ∧ singletonZero 0 = Part.some 0 ∧
      (∀ x, 0 < x → singletonZero x = Part.none) := by
  have heff : IsEffective shiftOperator :=
    ⟨shiftRules, shift_rules.1, shift_rules.2.1, shift_rules.2.2,
      shift_operator_correct.symm⟩
  have he : leastFixedPoint shiftOperator = singletonZero := by
    funext x
    apply Part.ext
    intro y
    rw [leastFixedPoint, chain_union_mem _ (bottom_iterates_increasing _ heff)]
    constructor
    · rintro ⟨n, hn⟩
      cases n with
      | zero => exact (Part.notMem_none _ hn).elim
      | succ n => simpa only [shift_iterates] using hn
    · intro hy
      exact ⟨0 + 1, by rw [shift_iterates]; exact hy⟩
  exact ⟨he, he ▸ (first_recursion_theorem _ heff).1, by simp [singletonZero],
    fun x hx => by simp [singletonZero, Nat.ne_of_gt hx]⟩

theorem constant_tail_fixed_points (k : ℕ) :
    Function.IsFixedPt shiftOperator (constantTail k) ∧
      GraphInclusion singletonZero (constantTail k) ∧ singletonZero ≠ constantTail k := by
  refine ⟨?_, ?_, ?_⟩
  · funext x
    by_cases hx : x = 0 <;> simp [shiftOperator, constantTail, hx]
  · intro x y hy
    by_cases hx : x = 0
    · simpa [singletonZero, constantTail, hx] using hy
    · simp [singletonZero, hx] at hy
  · intro he
    have h := congrFun he 1
    simp [singletonZero, constantTail] at h

theorem constant_tails_distinct (k l : ℕ) (hkl : k ≠ l) :
    constantTail k ≠ constantTail l := by
  intro he
  have h := congrFun he 1
  simp only [constantTail, Nat.one_ne_zero, ite_false] at h
  exact hkl (Part.some_injective h)

theorem index_fixed_point_answer :
    IsEffective (fun f : PartialFunction => f) ∧
      IsLeastFixedPoint (fun f : PartialFunction => f) RicesTheorem.bottom ∧
      Computable (fun e : ℕ => e) ∧ (∀ e, phi e = phi ((fun n => n) e)) ∧
      (∀ x, phi (Encodable.encode (Nat.Partrec.Code.const 0)) x = Part.some 0) ∧
      phi (Encodable.encode (Nat.Partrec.Code.const 0)) ≠ RicesTheorem.bottom := by
  have hp := Lemmatheca.Entry.EffectiveOperators.precomposition_rules id Computable.id
  have heff : IsEffective (fun f : PartialFunction => f) := by
    refine ⟨Lemmatheca.Entry.EffectiveOperators.precompositionRules id,
      hp.1, hp.2.1, hp.2.2, ?_⟩
    funext f x
    exact (Lemmatheca.Entry.EffectiveOperators.precomposition_operator id f x).symm
  refine ⟨heff, ⟨rfl, fun _ _ x y hy => (Part.notMem_none _ hy).elim⟩,
    Computable.id, fun _ => rfl, ?_, ?_⟩
  · intro x
    simp [phi, Nat.Partrec.Code.eval_const]
  · intro he
    have h := congrFun he 0
    simp [phi, RicesTheorem.bottom, Nat.Partrec.Code.eval_const] at h

end
end Lemmatheca.Entry.LeastFixedPointRecursion
