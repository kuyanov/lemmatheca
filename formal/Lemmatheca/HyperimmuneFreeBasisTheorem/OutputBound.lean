import Lemmatheca.HyperimmuneFreeBasisTheorem.Basic
import Lemmatheca.PaDegrees.TreeRace
import Lemmatheca.PrimitiveRecursion.PrimitiveRecursiveAutomation

set_option autoImplicit false
namespace Lemmatheca.ComputabilityTheory.HyperimmuneFreeBasisTheorem
open ComputableTreesAndPaths IncomparableTuringDegrees UniversalComputation
open LowBasisTheorem HyperimmuneDegrees PaDegrees
noncomputable section
local instance hfbOutputBoundPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Evaluate the supplied ordinary tree index on every word of one finite level. -/
def indexedLevelInfo (t e x m : ℕ) : Part (Bool × ℕ) :=
  ((binaryLevel m).mapM (phi t)).map fun values =>
    let words := (binaryLevel m).zip values
    (words.all (fun vb => !(vb.2 == 1) ||
      decide (0 < certificateValue vb.1 (TuringJump.freeze e x) (TuringJump.freeze e x))),
      (words.map (fun vb => if vb.2 = 1 then
        certificateValue vb.1 (TuringJump.freeze e x) (TuringJump.freeze e x) - 1
        else 0)).foldl max 0)

def levelMaximum (S : Set ℕ) (e x m : ℕ) : ℕ :=
  ((binaryLevel m).map (fun u => if u ∈ S then
    certificateValue u (TuringJump.freeze e x) (TuringJump.freeze e x) - 1
    else 0)).foldl max 0

def outputBoundSearch (t e x : ℕ) : Part ℕ := do
  let m ← Nat.rfind fun m => (indexedLevelInfo t e x m).map Prod.fst
  (indexedLevelInfo t e x m).map Prod.snd

section
attribute [local irreducible] binaryLevel TuringJump.freeze certificateValue
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem indexed_level_partial :
    Partrec (fun z : (ℕ × ℕ) × (ℕ × ℕ) =>
      indexedLevelInfo z.1.1 z.1.2 z.2.1 z.2.2) := by
  have hnodes : Primrec (fun z : (ℕ × ℕ) × (ℕ × ℕ) => binaryLevel z.2.2) :=
    binary_level_primitive.comp (Primrec.snd.comp Primrec.snd)
  have hvalues : Partrec (fun z : (ℕ × ℕ) × (ℕ × ℕ) =>
      (binaryLevel z.2.2).mapM (phi z.1.1)) :=
    phi_list_comp (fun z : (ℕ × ℕ) × (ℕ × ℕ) => z.1.1)
      (fun z : (ℕ × ℕ) × (ℕ × ℕ) => binaryLevel z.2.2)
      (Computable.fst.comp Computable.fst) hnodes.to_comp
  have hzip : Primrec (fun z : ((ℕ × ℕ) × (ℕ × ℕ)) × List ℕ =>
      (binaryLevel z.1.2.2).zip z.2) :=
    PrimitiveRecursiveAutomation.listZip (hnodes.comp Primrec.fst) Primrec.snd
  have he : Primrec (fun z : (((ℕ × ℕ) × (ℕ × ℕ)) × List ℕ) × (ℕ × ℕ) =>
      TuringJump.freeze z.1.1.1.2 z.1.1.2.1) :=
    TuringJump.freeze_primitive.comp
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hv : Primrec (fun z : (((ℕ × ℕ) × (ℕ × ℕ)) × List ℕ) × (ℕ × ℕ) =>
      certificateValue z.2.1 (TuringJump.freeze z.1.1.1.2 z.1.1.2.1)
        (TuringJump.freeze z.1.1.1.2 z.1.1.2.1)) :=
    certificate_primitive.comp (((Primrec.fst.comp Primrec.snd).pair he).pair he)
  have hb : Primrec (fun z : (((ℕ × ℕ) × (ℕ × ℕ)) × List ℕ) × (ℕ × ℕ) =>
      decide (z.2.2 = 1)) :=
    (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1)).decide
  have htest : Primrec (fun z : (((ℕ × ℕ) × (ℕ × ℕ)) × List ℕ) × (ℕ × ℕ) =>
      !(z.2.2 == 1) || decide (0 < certificateValue z.2.1
        (TuringJump.freeze z.1.1.1.2 z.1.1.2.1) (TuringJump.freeze z.1.1.1.2 z.1.1.2.1))) := by
    simpa only [Bool.beq_eq_decide_eq] using (Primrec.dom_bool₂ Bool.or).comp
      (Primrec.not.comp hb) (Primrec.nat_lt.comp (Primrec.const 0) hv).decide
  have hall : Primrec (fun z : ((ℕ × ℕ) × (ℕ × ℕ)) × List ℕ =>
      ((binaryLevel z.1.2.2).zip z.2).all (fun vb => !(vb.2 == 1) ||
        decide (0 < certificateValue vb.1 (TuringJump.freeze z.1.1.2 z.1.2.1)
          (TuringJump.freeze z.1.1.2 z.1.2.1)))) :=
    PrimitiveRecursiveAutomation.listAll hzip htest
  have hcell : Primrec (fun z : (((ℕ × ℕ) × (ℕ × ℕ)) × List ℕ) × (ℕ × ℕ) =>
      if z.2.2 = 1 then certificateValue z.2.1
        (TuringJump.freeze z.1.1.1.2 z.1.1.2.1) (TuringJump.freeze z.1.1.1.2 z.1.1.2.1) - 1
        else 0) :=
by
    apply (Primrec.cond hb (Primrec.nat_sub.comp hv (Primrec.const 1)) (Primrec.const 0)).of_eq
    intro z
    by_cases h : z.2.2 = 1 <;> simp [h]

  have hmap : Primrec (fun z : ((ℕ × ℕ) × (ℕ × ℕ)) × List ℕ =>
      ((binaryLevel z.1.2.2).zip z.2).map (fun vb => if vb.2 = 1 then
        certificateValue vb.1 (TuringJump.freeze z.1.1.2 z.1.2.1)
          (TuringJump.freeze z.1.1.2 z.1.2.1) - 1 else 0)) :=
    PrimitiveRecursiveAutomation.listMap
      (g := fun (z : ((ℕ × ℕ) × (ℕ × ℕ)) × List ℕ) (vb : ℕ × ℕ) =>
        if vb.2 = 1 then certificateValue vb.1 (TuringJump.freeze z.1.1.2 z.1.2.1)
          (TuringJump.freeze z.1.1.2 z.1.2.1) - 1 else 0) hzip hcell
  have hmax : Primrec (fun z : ((ℕ × ℕ) × (ℕ × ℕ)) × List ℕ =>
      (((binaryLevel z.1.2.2).zip z.2).map (fun vb => if vb.2 = 1 then
        certificateValue vb.1 (TuringJump.freeze z.1.1.2 z.1.2.1)
          (TuringJump.freeze z.1.1.2 z.1.2.1) - 1 else 0)).foldl max 0) :=
    PrimitiveRecursiveAutomation.listFold hmap (Primrec.const 0)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  unfold indexedLevelInfo
  exact hvalues.map (hall.pair hmax).to_comp.to₂
end

private theorem decider_level_test (S : Set ℕ) (e x : ℕ) (L : List ℕ) :
    (L.zip (L.map (indicator (fun u => u ∈ S)))).all (fun vb =>
      !(vb.2 == 1) || decide (0 < certificateValue vb.1
        (TuringJump.freeze e x) (TuringJump.freeze e x))) =
      decide (∀ u ∈ L, u ∈ S →
        0 < certificateValue u (TuringJump.freeze e x) (TuringJump.freeze e x)) := by
  induction L with
  | nil => simp
  | cons u L ih =>
    by_cases hu : u ∈ S <;> simp [indicator, hu, ih, Bool.decide_and]

private theorem decider_level_values (S : Set ℕ) (e x : ℕ) (L : List ℕ) :
    (L.zip (L.map (indicator (fun u => u ∈ S)))).map (fun vb =>
      if vb.2 = 1 then certificateValue vb.1
        (TuringJump.freeze e x) (TuringJump.freeze e x) - 1 else 0) =
      L.map (fun u => if u ∈ S then
        certificateValue u (TuringJump.freeze e x) (TuringJump.freeze e x) - 1 else 0) := by
  induction L with
  | nil => simp
  | cons u L ih =>
    by_cases hu : u ∈ S <;> simp [indicator, hu, ih]

theorem indexed_level_eval (S : Set ℕ) (t : ℕ) (ht : TreeDeciderIndex t S) (e x m : ℕ) :
    indexedLevelInfo t e x m = Part.some (successTest S e x m, levelMaximum S e x m) := by
  unfold indexedLevelInfo
  change ∀ u, phi t u = Part.some (indicator (fun v => v ∈ S) u) at ht
  rw [funext ht]
  have hm := (List.mapM_pure (m := Part) (l := binaryLevel m)
    (f := indicator (fun u => u ∈ S)))
  simp only [Part.pure_eq_some] at hm
  rw [hm, Part.map_some]
  apply congrArg Part.some
  dsimp only
  apply Prod.ext
  · rw [decider_level_test]
    apply Bool.eq_iff_iff.mpr
    simp [successTest, SuccessfulLevel]
    constructor
    · intro h
      exact @decide_eq_true (SuccessfulLevel S e x m) (Classical.propDecidable _) h
    · intro h
      exact @of_decide_eq_true (SuccessfulLevel S e x m) (Classical.propDecidable _) h
  · rw [decider_level_values]
    rfl

attribute [local irreducible] indexedLevelInfo

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem output_bound_search_partial :
    Nat.Partrec (fun z => outputBoundSearch z.unpair.1.unpair.1
      z.unpair.1.unpair.2 z.unpair.2) := by
  have hinput : Computable (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      (z.1.1, (z.1.2, z.2))) :=
    (Computable.fst.comp Computable.fst).pair
      ((Computable.snd.comp Computable.fst).pair Computable.snd)
  have hi : Partrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      indexedLevelInfo z.1.1.1 z.1.1.2 z.1.2 z.2) := indexed_level_partial.comp hinput
  have htest : Partrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      (indexedLevelInfo z.1.1.1 z.1.1.2 z.1.2 z.2).map Prod.fst) :=
    hi.map (Computable.fst.comp Computable.snd).to₂
  have hout : Partrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      (indexedLevelInfo z.1.1.1 z.1.1.2 z.1.2 z.2).map Prod.snd) :=
    hi.map (Computable.snd.comp Computable.snd).to₂
  have hb : Partrec (fun p : (ℕ × ℕ) × ℕ =>
      (Nat.rfind (fun m => (indexedLevelInfo p.1.1 p.1.2 p.2 m).map Prod.fst)).bind
        (fun m => (indexedLevelInfo p.1.1 p.1.2 p.2 m).map Prod.snd)) :=
    (Partrec.rfind htest.to₂).bind hout.to₂
  have hd : Computable (fun z : ℕ => (z.unpair.1.unpair, z.unpair.2)) :=
    (Computable.unpair.comp (Computable.fst.comp Computable.unpair)).pair
      (Computable.snd.comp Computable.unpair)
  have hp : Partrec (fun z : ℕ => outputBoundSearch z.unpair.1.unpair.1
      z.unpair.1.unpair.2 z.unpair.2) := (hb.comp hd).of_eq (fun _ => rfl)
  exact Partrec.nat_iff.mp hp

theorem bound_master_exists :
    ∃ v, ∀ t e x, phi v (Nat.pair (Nat.pair t e) x) = outputBoundSearch t e x := by
  obtain ⟨v, hv⟩ := phi_complete output_bound_search_partial
  refine ⟨v, fun t e x => ?_⟩
  have h := congrFun hv (Nat.pair (Nat.pair t e) x)
  simpa only [Nat.unpair_pair] using h

def boundMaster : ℕ := Classical.choose bound_master_exists

def boundIndex (t e : ℕ) : ℕ := specialize boundMaster (Nat.pair t e)

theorem bound_index_primitive : Primrec₂ boundIndex := by
  exact (specialize_primitive.comp (Primrec.const boundMaster) Primrec₂.natPair).to₂

theorem bound_index_eval (t e x : ℕ) :
    phi (boundIndex t e) x = outputBoundSearch t e x := by
  rw [boundIndex, specialize_eval]
  exact Classical.choose_spec bound_master_exists t e x

theorem output_bound_search_value (S : Set ℕ) (t : ℕ) (ht : TreeDeciderIndex t S)
    (e x m : ℕ) (hm : SuccessfulLevel S e x m)
    (hfirst : ∀ k < m, ¬ SuccessfulLevel S e x k) :
    outputBoundSearch t e x = Part.some (levelMaximum S e x m) := by
  have hr : m ∈ Nat.rfind (fun k => (indexedLevelInfo t e x k).map Prod.fst) := by
    apply Nat.mem_rfind.mpr
    constructor
    · rw [indexed_level_eval S t ht, Part.map_some]
      simp [successTest, hm]
    · intro k hk
      rw [indexed_level_eval S t ht, Part.map_some]
      simp [successTest, hfirst k hk]
  change (Nat.rfind (fun k => (indexedLevelInfo t e x k).map Prod.fst)).bind
    (fun k => (indexedLevelInfo t e x k).map Prod.snd) = _
  rw [Part.eq_some_iff.mpr hr, Part.bind_some, indexed_level_eval S t ht, Part.map_some]

theorem output_bound_search_domain (S : Set ℕ) (t : ℕ) (ht : TreeDeciderIndex t S)
    (e x : ℕ) : (outputBoundSearch t e x).Dom ↔ ∃ m, SuccessfulLevel S e x m := by
  constructor
  · intro hd
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
    change y ∈ (Nat.rfind (fun k => (indexedLevelInfo t e x k).map Prod.fst)).bind
      (fun k => (indexedLevelInfo t e x k).map Prod.snd) at hy
    obtain ⟨m, hm, _⟩ := Part.mem_bind_iff.mp hy
    have hs := Nat.rfind_spec hm
    rw [indexed_level_eval S t ht, Part.map_some] at hs
    change true ∈ Part.some (successTest S e x m) at hs
    have hb : successTest S e x m = true := (Part.mem_some_iff.mp hs).symm
    exact ⟨m, by simpa only [successTest, decide_eq_true_eq] using hb⟩
  · intro h
    rw [output_bound_search_value S t ht e x (Nat.find h) (Nat.find_spec h)
      (fun k hk => Nat.find_min h hk)]
    trivial

private theorem member_le_max_fold (L : List ℕ) (a y : ℕ) (hy : y ∈ L) :
    y ≤ L.foldl max a := by
  have hbound : ∀ (L : List ℕ) (a : ℕ), a ≤ L.foldl max a ∧
      ∀ y ∈ L, y ≤ L.foldl max a := by
    intro L
    induction L with
    | nil => intro a; simp
    | cons b L ih =>
      intro a
      obtain ⟨hb, hm⟩ := ih (max a b)
      refine ⟨(le_max_left a b).trans hb, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact (le_max_right a y).trans hb
      · exact hm y hy
  exact (hbound L a).2 y hy

theorem successful_level_output_bound (S : Set ℕ) (e x m : ℕ)
    (hm : SuccessfulLevel S e x m) (A : Set ℕ) (hA : Path S A) (y : ℕ)
    (hy : y ∈ OracleProgramNumberings.phi A e x) : y ≤ levelMaximum S e x m := by
  let u := PostsTheorem.prefixCode A m
  have hu : u ∈ binaryLevel m :=
    (binary_level_spec m u).mpr ⟨prefix_code_valid A m, (PostsTheorem.prefixCode_spec A m).1⟩
  have huS : u ∈ S := hA m
  have hr : Realizes u A := by
    intro q hq
    apply (PostsTheorem.prefixCode_spec A m).2 q
    simpa only [((binary_level_spec m u).mp hu).2] using hq
  have hp := hm u hu huS
  let v := certificateValue u (TuringJump.freeze e x) (TuringJump.freeze e x) - 1
  have hv : certificateValue u (TuringJump.freeze e x) (TuringJump.freeze e x) = v + 1 := by
    dsimp only [v]
    omega
  have hout := certificate_sound A u (TuringJump.freeze e x) (TuringJump.freeze e x) v hr hv
  rw [TuringJump.freeze_eval] at hout
  have heq : v = y := Part.mem_unique hout hy
  have hmem : v ∈ (binaryLevel m).map (fun u => if u ∈ S then
      certificateValue u (TuringJump.freeze e x) (TuringJump.freeze e x) - 1 else 0) := by
    apply List.mem_map.mpr
    exact ⟨u, hu, by rw [ite_eq_left huS]⟩
  have hbound := member_le_max_fold _ 0 v hmem
  change v ≤ levelMaximum S e x m at hbound
  exact heq ▸ hbound


/-- The same specified compiled program supplies a bound for the whole class. -/
def ClassBound (S : Set ℕ) (t e : ℕ) : Prop :=
  ∃ h : ℕ → ℕ, Computable h ∧
    (∀ x, phi (boundIndex t e) x = Part.some (h x)) ∧
    ∀ A, Path S A → ∀ x y, y ∈ OracleProgramNumberings.phi A e x → y ≤ h x

theorem uniform_output_bound (S : Set ℕ) (hS : IsBinaryTree S)
    (t : ℕ) (ht : TreeDeciderIndex t S) (e : ℕ)
    (hall : ∀ A, Path S A → ∀ x, (OracleProgramNumberings.phi A e x).Dom) :
    ClassBound S t e := by
  have he : ∀ x, ∃ m, SuccessfulLevel S e x m :=
    fun x => successful_level_exists S hS e x (fun A hA => hall A hA x)
  let h : ℕ → ℕ := fun x => levelMaximum S e x (Nat.find (he x))
  have hv : ∀ x, phi (boundIndex t e) x = Part.some (h x) := by
    intro x
    rw [bound_index_eval]
    exact output_bound_search_value S t ht e x (Nat.find (he x)) (Nat.find_spec (he x))
      (fun k hk => Nat.find_min (he x) hk)
  have hp : Partrec (fun x => phi (boundIndex t e) x) :=
    phi_recursive.comp (Computable.const _) Computable.id
  refine ⟨h, hp.of_eq_tot (fun x => Part.eq_some_iff.mp (hv x)), hv, ?_⟩
  intro A hA x y hy
  exact successful_level_output_bound S e x (Nat.find (he x))
    (Nat.find_spec (he x)) A hA y hy

end
end Lemmatheca.ComputabilityTheory.HyperimmuneFreeBasisTheorem
