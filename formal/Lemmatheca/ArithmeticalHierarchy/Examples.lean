import Lemmatheca.ArithmeticalHierarchy.Arithmetic
import Lemmatheca.EffectiveEnumerations.Stages

/-! Membership upper bounds and the three worked quantifier questions. -/
namespace Lemmatheca.Entry.ArithmeticalHierarchy

open Lemmatheca.ComputabilityTheory
open ArithmeticalHierarchy

set_option backward.isDefEq.respectTransparency false

def Totality : Set ℕ := {e | ∀ x, (UniversalComputation.phi e x).Dom}
def Finiteness : Set ℕ := {e | (EffectiveEnumerations.indexSet e).Finite}

def finiteStageMatrix (e a s : ℕ) : Prop :=
  ∀ x < s, x ∈ EffectiveEnumerations.stage e s → x < a

theorem totality_normal_form (e : ℕ) :
    e ∈ Totality ↔ ∀ x, ∃ k, 0 < UniversalComputation.boundedValue k e x := by
  exact forall_congr' (fun x => UniversalComputation.phi_domain e x)

theorem totality_pi_two : Pi ∅ 2 (fun e => e ∈ Totality) := by
  have hm : PrimrecPred (fun v : Tuple 3 => 0 < UniversalComputation.boundedValue (v 2) (v 0) (v 1)) :=
    Primrec.nat_lt.comp (Primrec.const 0)
      (UniversalComputation.boundedValue_primitive.comp
        (((Primrec.fin_app.comp Primrec.id (Primrec.const 2)).pair
          (Primrec.fin_app.comp Primrec.id (Primrec.const 0))).pair
          (Primrec.fin_app.comp Primrec.id (Primrec.const 1))))
  apply (unary_finite_bridge ∅ 2 false _).mp
  apply (finite_matrix_normal_form ∅ 2 false _).mpr
  refine ⟨fun v => 0 < UniversalComputation.boundedValue (v 2) (v 0) (v 1),
    (finite_decidable_empty_iff _).mpr hm.computablePred, ?_⟩
  intro x
  simpa [quantify, appendTuple, Fin.append, Fin.addCases] using totality_normal_form (x 0)

theorem finite_stage_matrix_primitive :
    PrimrecPred (fun v : Tuple 3 => finiteStageMatrix (v 0) (v 1) (v 2)) := by
  have h0 : Primrec (fun p : Tuple 3 × ℕ => p.1 0) :=
    Primrec.fin_app.comp Primrec.fst (Primrec.const 0)
  have h1 : Primrec (fun p : Tuple 3 × ℕ => p.1 1) :=
    Primrec.fin_app.comp Primrec.fst (Primrec.const 1)
  have h2 : Primrec (fun p : Tuple 3 × ℕ => p.1 2) :=
    Primrec.fin_app.comp Primrec.fst (Primrec.const 2)
  have hs : PrimrecRel (fun v : Tuple 3 => fun x => x ∈ EffectiveEnumerations.stage (v 0) (v 2)) :=
    EffectiveEnumerations.stage_predicate_primitive.comp ((h0.pair h2).pair Primrec.snd)
  have hor : PrimrecPred (fun p : Tuple 3 × ℕ =>
      p.2 ∉ EffectiveEnumerations.stage (p.1 0) (p.1 2) ∨ p.2 < p.1 1) :=
    hs.not.or (Primrec.nat_lt.comp Primrec.snd h1)
  have hi : PrimrecRel (fun v : Tuple 3 => fun x => x ∈ EffectiveEnumerations.stage (v 0) (v 2) → x < v 1) :=
    PrimrecPred.of_eq hor (fun p => by tauto)
  exact (PrimitiveRecursion.bounded_forall_primrec hi).comp Primrec.id
    (Primrec.fin_app.comp Primrec.id (Primrec.const 2))

theorem finiteness_normal_form (e : ℕ) :
    e ∈ Finiteness ↔ ∃ a, ∀ s, finiteStageMatrix e a s := by
  constructor
  · intro h
    obtain ⟨a,ha⟩ := Set.Finite.bddAbove h
    refine ⟨a+1, fun s x _ hx => ?_⟩
    have hx' := (EffectiveEnumerations.stage_union e x).mpr ⟨s,hx⟩
    exact Nat.lt_succ_of_le (ha hx')
  · rintro ⟨a,ha⟩
    apply (Set.finite_Iio a).subset
    intro x hx
    obtain ⟨s,hs⟩ := (EffectiveEnumerations.stage_union e x).mp hx
    exact ha s x hs.1 hs

theorem finiteness_sigma_two : Sigma ∅ 2 (fun e => e ∈ Finiteness) := by
  apply (unary_finite_bridge ∅ 2 true _).mp
  apply (finite_matrix_normal_form ∅ 2 true _).mpr
  refine ⟨fun v => finiteStageMatrix (v 0) (v 1) (v 2),
    (finite_decidable_empty_iff _).mpr finite_stage_matrix_primitive.computablePred, ?_⟩
  intro x
  simpa [quantify, appendTuple, Fin.append, Fin.addCases] using finiteness_normal_form (x 0)

def successorWitnessCode (m : ℕ) : ℕ := tupleCode (fun i : Fin m => i.val + 1)

theorem successor_witness_entries (m i : ℕ) (hi : i < m) :
    FSC.entry (successorWitnessCode m) i = i + 1 := by
  exact congrFun (tuple_decode_code (fun i : Fin m => i.val+1)) ⟨i,hi⟩

theorem empty_bound_answer :
    successorWitnessCode 0 = 0 ∧ (∀ i < 0, ∃ u : ℕ, u = i + 1) ∧
      ¬∃ i < 0, ∃ u : ℕ, u = i + 1 := by
  simp [successorWitnessCode, tupleCode]

def EvenRelation (x : ℕ) : Prop := x % 2 = 0

def displayedEven (x : ℕ) : Prop := ∀ u : ℕ, ∃ v : ℕ, v = u ∧ EvenRelation x

theorem displayed_even_equivalence (x : ℕ) : displayedEven x ↔ EvenRelation x := by
  exact ⟨fun h => (h 0).choose_spec.2, fun h u => ⟨u,rfl,h⟩⟩

theorem displayed_even_matrix_decidable :
    FiniteDecidable ∅ (fun v : Tuple 3 => v 2 = v 1 ∧ EvenRelation (v 0)) := by
  apply (finite_decidable_empty_iff _).mpr
  apply PrimrecPred.computablePred
  exact (Primrec.eq.comp
    (Primrec.fin_app.comp Primrec.id (Primrec.const 2))
    (Primrec.fin_app.comp Primrec.id (Primrec.const 1))).and
    (Primrec.eq.comp (Primrec.nat_mod.comp
      (Primrec.fin_app.comp Primrec.id (Primrec.const 0)) (Primrec.const 2)) (Primrec.const 0))

theorem even_at_level_zero : Delta ∅ 0 EvenRelation := by
  have hd : FiniteDecidable ∅ (fun v : Tuple 1 => EvenRelation (v 0)) := by
    apply (finite_decidable_empty_iff _).mpr
    apply PrimrecPred.computablePred
    exact Primrec.eq.comp (Primrec.nat_mod.comp
      (Primrec.fin_app.comp Primrec.id (Primrec.const 0)) (Primrec.const 2)) (Primrec.const 0)
  exact ⟨(unary_finite_bridge ∅ 0 true _).mp ((finite_level_zero_iff ∅ true _).mpr hd),
    (unary_finite_bridge ∅ 0 false _).mp ((finite_level_zero_iff ∅ false _).mpr hd)⟩

theorem even_pi_two : Pi ∅ 2 EvenRelation := by
  exact level_padding ∅ 1 false false EvenRelation
    (level_padding ∅ 0 true false EvenRelation even_at_level_zero.1)

theorem quantifier_order_answer :
    (∀ u : ℕ, u + 1 > u) ∧ ¬∃ v : ℕ, ∀ u : ℕ, v > u := by
  constructor
  · intro u
    omega
  · rintro ⟨v,hv⟩
    have := hv v
    omega

end Lemmatheca.Entry.ArithmeticalHierarchy
