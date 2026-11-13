import Lemmatheca.NiceNamesAndCohenContinuum.Names
import Lemmatheca.ContinuumFunction.ContinuumFunction
import Mathlib.SetTheory.Cardinal.Finsupp

namespace Lemmatheca.SetTheory.NiceNamesAndCohenContinuum
open Set Order Cardinal
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.ForcingChainConditions
open Lemmatheca.SetTheory.ForcingNames
open Lemmatheca.SetTheory.ForcingTheorem
open Lemmatheca.SetTheory.NaturalNumbersAsSets
open scoped ZFSet
universe u
noncomputable section
local instance niceCountingPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {Q : Type u}

def sequenceRange (s : ℕ → Option Q) : Set Q := {p | ∃ k, s k = some p}

theorem countable_sequence_representation (B : Set Q) (hB : B.Countable) :
    ∃ s : ℕ → Option Q, sequenceRange s = B := by
  by_cases hne : B.Nonempty
  · obtain ⟨f,hf⟩ := hB.exists_eq_range hne
    refine ⟨fun n => some (f n),?_⟩
    ext p
    simp only [sequenceRange,Set.mem_ofPred_eq,Option.some.injEq,hf,Set.mem_range]
  · refine ⟨fun _ => none,?_⟩
    rw [Set.not_nonempty_iff_eq_empty.mp hne]
    ext p
    simp [sequenceRange]

def rowEnumeration (B : Set Q) (hB : B.Countable) : ℕ → Option Q :=
  (countable_sequence_representation B hB).choose

def CountableRows (Q : Type u) := {B : ℕ → Set Q // ∀ n, (B n).Countable}

def familyEncoding (B : CountableRows Q) : ℕ → ℕ → Option Q :=
  fun n => rowEnumeration (B.val n) (B.property n)

theorem family_encoding_recovers (B : CountableRows Q) :
    (fun n => sequenceRange (familyEncoding B n)) = B.val := by
  funext n
  exact (countable_sequence_representation (B.val n) (B.property n)).choose_spec

theorem family_encoding_injective : Function.Injective (familyEncoding (Q := Q)) := by
  intro B D he
  apply Subtype.ext
  rw [← family_encoding_recovers B,← family_encoding_recovers D,he]

theorem countable_rows_cardinality (hQ : ℵ₀ ≤ #Q) :
    #(CountableRows Q) ≤ #Q ^ ℵ₀ := by
  calc
    #(CountableRows Q) ≤ #(ℕ → ℕ → Option Q) := mk_le_of_injective family_encoding_injective
    _ = ((#Q + 1) ^ ℵ₀) ^ ℵ₀ := by
      simp only [mk_arrow,mk_nat,mk_option,lift_aleph0,lift_id']
    _ = #Q ^ ℵ₀ := by
      rw [Cardinal.add_eq_left hQ (one_le_aleph0.trans hQ),← power_mul,mul_eq_self le_rfl]

/-- An explicit retraction of an injection, with a fixed fallback value. -/
def coverEnumeration {K : Type u} {A : Type u} (i : A → K) (a₀ : A) : K → A :=
  fun k => if h : ∃ a, i a = k then h.choose else a₀

theorem cover_enumeration_right_inverse {K A : Type u} (i : A → K)
    (hi : Function.Injective i) (a₀ : A) :
    ∀ a, coverEnumeration i a₀ (i a) = a := by
  intro a
  unfold coverEnumeration
  rw [dite_eq_left (show ∃ b, i b = i a from ⟨a,rfl⟩)]
  apply hi
  exact (show ∃ b, i b = i a from ⟨a,rfl⟩).choose_spec

theorem cover_enumeration_surjective {K A : Type u} (i : A → K)
    (hi : Function.Injective i) (a₀ : A) :
    Function.Surjective (coverEnumeration i a₀) := by
  intro a
  exact ⟨i a,cover_enumeration_right_inverse i hi a₀ a⟩

section NativeCodes
variable [PartialOrder Q] [OrderTop Q]

omit [OrderTop Q] in
theorem ground_codes_injective (C : Context.{u,u} Q) :
    Function.Injective (fun b : codeSet C => codeRow C b.val) := by
  intro b c he
  apply Subtype.ext
  change codeRow C b.val = codeRow C c.val at he
  rw [← row_code_inverse C b.val ((code_set_members C _).mp b.property).1,
    ← row_code_inverse C c.val ((code_set_members C _).mp c.property).1,he]

omit [OrderTop Q] in
theorem ground_codes_cardinality (C : Context.{u,u} Q) (hccc : CCC Q)
    (hQ : ℵ₀ ≤ #Q) : #(codeSet C) ≤ Cardinal.lift.{u+1} (#Q ^ ℵ₀) := by
  let f : codeSet C → CountableRows Q := fun b =>
    ⟨codeRow C b.val,fun n => hccc _ (((code_set_members C _).mp b.property).2.2 n)⟩
  have hi : Function.Injective f := by
    intro b c he
    exact ground_codes_injective C (congrArg Subtype.val he)
  calc
    #(codeSet C) ≤ Cardinal.lift.{u+1} #(CountableRows Q) := by
      have hh := Cardinal.lift_mk_le_lift_mk_of_injective hi
      have hl : Cardinal.lift.{u} #(codeSet C) = #(codeSet C) :=
        Cardinal.lift_id'.{u,u+1} _
      rw [hl] at hh
      exact hh
    _ ≤ Cardinal.lift.{u+1} (#Q ^ ℵ₀) := Cardinal.lift_le.mpr (countable_rows_cardinality hQ)

/-- The name of the composite evaluation map for a supplied ground enumeration. -/
def enumeratedEvaluationName (C : Context.{u,u} Q) (K : ZFSet.{u})
    (e : K → codeSet C) : ZFSet.{u} :=
  Lemmatheca.SetTheory.ManyCohenReals.indexedFamilyName K (C.code ⊤).val
    (fun k => codeName C (e k).val)

def enumeratedEvaluationGraph (C : Context.{u,u} Q) (K : ZFSet.{u})
    (e : K → codeSet C) (H : PFilter Q) : ZFSet.{u} :=
  ZFSet.range (fun k : K =>
    ZFSet.pair k.val (evaluation (C.filterCode H) (codeName C (e k).val)))

theorem enumerated_evaluation_valid (C : Context.{u,u} Q) (K : ZFSet.{u})
    (e : K → codeSet C) : IsName C.conditions (enumeratedEvaluationName C K e) := by
  exact Lemmatheca.SetTheory.ManyCohenReals.indexedFamilyName_isName
    C.conditions K _ _ (C.code ⊤).property (fun _ => nice_name_valid C _)

theorem enumerated_evaluation_value (C : Context.{u,u} Q) (K : ZFSet.{u})
    (e : K → codeSet C) (H : PFilter Q) :
    evaluation (C.filterCode H) (enumeratedEvaluationName C K e) =
      enumeratedEvaluationGraph C K e H := by
  exact Lemmatheca.SetTheory.ManyCohenReals.indexedFamilyName_value K _ _ _
    ((filterSet_mem C.conditions C.code H _).mpr ⟨⊤,PFilter.top_mem,rfl⟩)

theorem enumerated_evaluation_in_extension (C : Context.{u,u} Q) (K : ZFSet.{u})
    (e : K → codeSet C) (H : PFilter Q)
    (hname : enumeratedEvaluationName C K e ∈ C.ground) :
    enumeratedEvaluationGraph C K e H ∈ C.valueDomain H := by
  exact (extension_mem _ _ _ _).mpr
    ⟨enumeratedEvaluationName C K e,hname,enumerated_evaluation_valid C K e,
      enumerated_evaluation_value C K e H⟩

theorem enumerated_evaluation_surjective (C : Context.{u,u} Q)
    (A : C.Name → ℕ → Set Q)
    (hA : ∀ τ n, A τ n ⊆ deciding C τ n ∧ MaximalAntichain (A τ n))
    (hground : ∀ τ n, downwardClosure (A τ n) ∈ C.groundFamily)
    (hcodes : ∀ τ, rowCode C (positiveRows C τ (A τ)) ∈ C.ground)
    (K : ZFSet.{u}) (e : K → codeSet C) (he : Function.Surjective e)
    (H : PFilter Q) (hH : GenericFor H C.groundFamily) :
    ∀ x ∈ C.valueDomain H, x ⊆ ZFSet.omega →
      ∃ k : K, ZFSet.pair k.val x ∈ enumeratedEvaluationGraph C K e H := by
  intro x hx hxω
  obtain ⟨b,hb,hbx⟩ := evaluation_graph_surjective C A hA hground hcodes H hH x hx hxω
  obtain ⟨k,hk⟩ := he ⟨b,hb⟩
  have hvalue := ((evaluation_graph_members C H b x).mp hbx).2
  refine ⟨k,ZFSet.mem_range.mpr ⟨k,?_⟩⟩
  rw [hk,hvalue]


theorem enumerated_evaluation_function (C : Context.{u,u} Q) (K : ZFSet.{u})
    (e : K → codeSet C) (H : PFilter Q)
    (hnames : ∀ b ∈ codeSet C, codeName C b ∈ C.ground) :
    (∀ k ∈ K, ∃! x, ZFSet.pair k x ∈ enumeratedEvaluationGraph C K e H) ∧
      ∀ k x, ZFSet.pair k x ∈ enumeratedEvaluationGraph C K e H →
        k ∈ K ∧ x ∈ C.valueDomain H ∧ x ⊆ ZFSet.omega := by
  have hmem (k x : ZFSet.{u}) :
      ZFSet.pair k x ∈ enumeratedEvaluationGraph C K e H ↔
        ∃ a : K, a.val = k ∧ x = evaluation (C.filterCode H) (codeName C (e a).val) := by
    rw [enumeratedEvaluationGraph,ZFSet.mem_range]
    constructor
    · rintro ⟨a,ha⟩
      obtain ⟨hak,hax⟩ := ZFSet.pair_inj.mp ha
      exact ⟨a,hak,hax.symm⟩
    · rintro ⟨a,rfl,rfl⟩
      exact ⟨a,rfl⟩
  constructor
  · intro k hk
    refine ⟨evaluation (C.filterCode H) (codeName C (e ⟨k,hk⟩).val),
      (hmem _ _).mpr ⟨⟨k,hk⟩,rfl,rfl⟩,?_⟩
    intro x hx
    obtain ⟨a,ha,hax⟩ := (hmem _ _).mp hx
    have heq : a = (⟨k,hk⟩ : K) := Subtype.ext ha
    exact hax.trans (congrArg (fun a : K => evaluation (C.filterCode H) (codeName C (e a).val)) heq)
  · intro k x hx
    obtain ⟨a,rfl,rfl⟩ := (hmem _ _).mp hx
    exact ⟨a.property,(extension_mem _ _ _ _).mpr
      ⟨codeName C (e a).val,hnames _ (e a).property,nice_name_valid C _,rfl⟩,
      nice_name_subset_omega C _ H⟩

theorem extension_real_cardinality_bound (C : Context.{u,u} Q)
    (A : C.Name → ℕ → Set Q)
    (hA : ∀ τ n, A τ n ⊆ deciding C τ n ∧ MaximalAntichain (A τ n))
    (hground : ∀ τ n, downwardClosure (A τ n) ∈ C.groundFamily)
    (hcodes : ∀ τ, rowCode C (positiveRows C τ (A τ)) ∈ C.ground)
    (K : ZFSet.{u}) (e : K → codeSet C) (he : Function.Surjective e)
    (H : PFilter Q) (hH : GenericFor H C.groundFamily) :
    #{x : ZFSet.{u} // x ∈ C.valueDomain H ∧ x ⊆ ZFSet.omega} ≤ #K := by
  let R := {x : ZFSet.{u} // x ∈ C.valueDomain H ∧ x ⊆ ZFSet.omega}
  have hpre (x : R) : ∃ k : K,
      evaluation (C.filterCode H) (codeName C (e k).val) = x.val := by
    obtain ⟨k,hk⟩ := enumerated_evaluation_surjective C A hA hground hcodes K e he H hH
      x.val x.property.1 x.property.2
    obtain ⟨a,ha⟩ := ZFSet.mem_range.mp hk
    obtain ⟨hak,hax⟩ := ZFSet.pair_inj.mp ha
    exact ⟨a,hax⟩
  let code : R → K := fun x => (hpre x).choose
  have hi : Function.Injective code := by
    intro x y hxy
    apply Subtype.ext
    exact (hpre x).choose_spec.symm.trans
      ((congrArg (fun k : K => evaluation (C.filterCode H) (codeName C (e k).val)) hxy).trans
        (hpre y).choose_spec)
  exact Cardinal.mk_le_of_injective hi

end NativeCodes


/-- The actual finite Cohen order has the size of its infinite column set. -/
theorem cohen_conditions_cardinality (I : Type u) (hI : ℵ₀ ≤ #I) :
    #(Lemmatheca.SetTheory.ManyCohenReals.Conditions I) = #I := by
  classical
  let : Infinite I := Cardinal.infinite_iff.mpr hI
  let α := ℕ × I
  have hα : #(α × Bool) = #I := by
    simp only [α,mk_prod,mk_nat,mk_bool,lift_id',lift_aleph0,lift_two]
    rw [Cardinal.mul_eq_right hI hI Cardinal.aleph0_ne_zero]
    exact Cardinal.mul_eq_left hI (show (2 : Cardinal.{u}) ≤ #I from
      Cardinal.natCast_le_aleph0.trans hI) (by norm_num)
  have hsigma : #(Sigma (fun _ : α => Bool)) = #I :=
    (Cardinal.mk_congr (Equiv.sigmaEquivProd α Bool)).trans hα
  have hinf : Infinite (Sigma (fun _ : α => Bool)) := Cardinal.infinite_iff.mpr (hsigma.symm ▸ hI)
  let := hinf
  apply le_antisymm
  · calc
      #(Lemmatheca.SetTheory.ManyCohenReals.Conditions I) ≤ #(Multiset (Sigma (fun _ : α => Bool))) :=
        Cardinal.mk_le_of_injective (show Function.Injective
          (fun p : Lemmatheca.SetTheory.ManyCohenReals.Conditions I => p.entries) from
          fun _ _ h => Finmap.ext h)
      _ = #I := (Cardinal.mk_multiset_of_infinite _).trans hsigma
  · apply Cardinal.mk_le_of_injective (f := fun i : I =>
      (Finmap.singleton (0,i) false : Lemmatheca.SetTheory.ManyCohenReals.Conditions I))
    intro i j he
    have hk := congrArg Finmap.keys he
    simp only [Finmap.keys_singleton] at hk
    have heq : (0,i) = (0,j) := by simpa only [Finset.singleton_inj] using hk
    exact congrArg Prod.snd heq

/-- The CH special case, with no GCH hypothesis. -/
theorem ch_aleph_two_countable_power (hCH : 2 ^ (ℵ₀ : Cardinal.{u}) = Cardinal.aleph 1) :
    (Cardinal.aleph 2 : Cardinal.{u}) ^ ℵ₀ = Cardinal.aleph 2 := by
  have hone : (Cardinal.aleph 1 : Cardinal.{u}) ^ ℵ₀ = Cardinal.aleph 1 :=
    Lemmatheca.SetTheory.ContinuumFunction.aleph_one_countable_power.trans hCH
  have hsucc : Order.succ (Cardinal.aleph 1 : Cardinal.{u}) = Cardinal.aleph 2 := by
    convert Cardinal.succ_aleph (1 : Ordinal.{u}) using 1
    norm_num
  rw [← hsucc,Lemmatheca.SetTheory.ContinuumFunction.hausdorff_formula _ _
    (Cardinal.aleph0_le_aleph 1) le_rfl,hone]
  exact Cardinal.mul_eq_right (Cardinal.aleph0_le_aleph 1 |>.trans (Order.le_succ _))
    (Order.le_succ _) (Cardinal.aleph0_pos.trans_le (Cardinal.aleph0_le_aleph 1)).ne'

end
end Lemmatheca.SetTheory.NiceNamesAndCohenContinuum
