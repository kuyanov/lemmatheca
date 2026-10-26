import Lemmatheca.TuringComputationAndRecursion.Native

namespace Lemmatheca.Entry.TuringComputationAndRecursion

open Lemmatheca.ComputabilityTheory
open CounterPrograms PartialRecursiveFunctions RecursiveTapeCompiler

def constantRoutine (c : ℕ) : Routine 0 where
  work := 0
  body := {
    Label := Fin c
    finite := inferInstance
    entry := if h : c = 0 then none else some ⟨0, by omega⟩
    code := fun j => .inc (outputPort 0 0)
      (if h : j.val + 1 < c then some ⟨j.val + 1, h⟩ else none) }

def undefinedRoutine (n : ℕ) : Routine n :=
  ⟨0, ⟨Unit, inferInstance, some (), fun _ => .inc (workPort n 0 0) (some ())⟩⟩

def addTwoStep : Routine 2 :=
  ⟨0, sequence (workPort 2 0 0)
    [copyFragment (inputPort 2 0 1) (outputPort 2 0) (workPort 2 0 0),
      incrementFragment (outputPort 2 0), incrementFragment (outputPort 2 0)]⟩

def exampleRecursion : Routine 1 := primitiveRecursionRoutine (constantRoutine 2) addTwoStep

set_option backward.isDefEq.respectTransparency false

private theorem exec_unique {k : ℕ} (B : Fragment k) (R S T : Registers k)
    (hS : Exec B R S) (hT : Exec B R T) : S = T := by
  obtain ⟨j, hj⟩ := (reaches_iff_run _ _ _).mp hS
  obtain ⟨t, ht⟩ := (reaches_iff_run _ _ _).mp hT
  funext r
  apply outputFrom_unique B.program ⟨B.entry, R⟩ r (S r) (T r)
  · exact ⟨j, by rw [hj]; rfl, by rw [hj]⟩
  · exact ⟨t, by rw [ht]; rfl, by rw [ht]⟩

private def constantState (c j : ℕ) : Option (Fin c) :=
  if h : j < c then some ⟨j, h⟩ else none

private theorem constant_prefix (c j : ℕ) (R : Registers 2) (hj : j ≤ c) :
    run (constantRoutine c).body.program ⟨(constantRoutine c).body.entry, R⟩ j =
      ⟨constantState c j, updateRegister R (outputPort 0 0) (R (outputPort 0 0) + j)⟩ := by
  induction j with
  | zero =>
      apply Config.ext
      · by_cases hc : c = 0 <;> simp [run, constantRoutine, constantState, hc]
      · simp [run, updateRegister]
  | succ j ih =>
      have hjc : j < c := by omega
      rw [run, ih (by omega)]
      simp [constantState, hjc, advance, step, Fragment.program, constantRoutine,
        updateRegister, Nat.add_assoc]

private theorem constant_returns (c : ℕ) (R : Registers 2) :
    Exec (constantRoutine c).body R
      (updateRegister R (outputPort 0 0) (R (outputPort 0 0) + c)) := by
  apply (reaches_iff_run _ _ _).mpr
  exact ⟨c, by simpa [constantState] using constant_prefix c c R le_rfl⟩

private theorem increment_returns {k : ℕ} (r : Fin k) (R : Registers k) :
    Exec (incrementFragment r) R (updateRegister R r (R r + 1)) := by
  apply (reaches_iff_run _ _ _).mpr
  exact ⟨1, by simp [run, advance, step, Fragment.program, incrementFragment]⟩

theorem copy_offset_answers :
    let R₁ : Registers 3 := fun i => if i = 0 then 3 else if i = 1 then 2 else 0
    let R₂ : Registers 3 := fun i => if i = 0 then 3 else if i = 1 then 0 else 1
    run (copyFragment (0 : Fin 3) 1 2).program ⟨some (0 : Fin 5), R₁⟩ 17 =
      ⟨none, fun i => if i = 0 then 3 else if i = 1 then 5 else 0⟩ ∧
    run (copyFragment (0 : Fin 3) 1 2).program ⟨some (0 : Fin 5), R₂⟩ 19 =
      ⟨none, fun i => if i = 0 then 4 else if i = 1 then 3 else 0⟩ := by
  dsimp only
  constructor <;> apply Config.ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl
  · funext i; fin_cases i <;> rfl


theorem constant_clean (c : ℕ) : Clean (constantRoutine c) (fun _ => Part.some c) := by
  refine ⟨?_, fun x S => ?_⟩
  · intro p
    simp [constantRoutine]
  · have hc := constant_returns c (initialFile 0 x)
    have hz : initialFile 0 x (outputPort 0 0) = 0 := by simp [initialFile, outputPort]
    simp only [hz, Nat.zero_add] at hc
    simp only [Part.mem_some_iff, exists_eq_left]
    constructor
    · intro h
      exact exec_unique _ _ _ _ h hc
    · rintro rfl
      exact hc


theorem constant_exact_steps (c : ℕ) :
    run (constantRoutine c).body.program
      ⟨(constantRoutine c).body.entry, initialFile 0 (List.Vector.nil : Args 0)⟩ c =
      ⟨none, resultFile 0 List.Vector.nil c⟩ ∧
    ∀ j < c, ¬ Halted (constantRoutine c).body.program
      (run (constantRoutine c).body.program
        ⟨(constantRoutine c).body.entry, initialFile 0 (List.Vector.nil : Args 0)⟩ j) := by
  constructor
  · have h := constant_prefix c c (initialFile 0 (List.Vector.nil : Args 0)) le_rfl
    simpa [constantState, resultFile, initialFile, outputPort] using h
  · intro j hj
    rw [constant_prefix c j _ (Nat.le_of_lt hj)]
    simp [Halted, Fragment.program, constantRoutine, constantState, hj]


theorem undefined_run (n j : ℕ) (x : Args n) :
    run (undefinedRoutine n).body.program ⟨some (), initialFile 0 x⟩ j =
      ⟨some (), updateRegister (initialFile 0 x) (workPort n 0 0) j⟩ ∧
      ¬ Halted (undefinedRoutine n).body.program
        (run (undefinedRoutine n).body.program ⟨some (), initialFile 0 x⟩ j) := by
  have hzero : initialFile 0 x (workPort n 0 0) = 0 :=
    (canonical_ports 0 x 0).2.2.1 0
  have hr : run (undefinedRoutine n).body.program ⟨some (), initialFile 0 x⟩ j =
      ⟨some (), updateRegister (initialFile 0 x) (workPort n 0 0) j⟩ := by
    induction j with
    | zero => simp [run, updateRegister, ← hzero]
    | succ j ih =>
        rw [run, ih]
        simp [advance, step, Fragment.program, undefinedRoutine, updateRegister]
  refine ⟨hr, ?_⟩
  rw [hr]
  simp [Halted, Fragment.program, undefinedRoutine]


theorem undefined_clean (n : ℕ) : Clean (undefinedRoutine n) (fun _ => Part.none) := by
  refine ⟨?_, fun x S => ?_⟩
  · intro p
    simp [undefinedRoutine]
  · simp only [Part.notMem_none, false_and, exists_false, iff_false]
    intro h
    obtain ⟨j, hj⟩ := (reaches_iff_run _ _ _).mp h
    have hn := (undefined_run n j x).2
    apply hn
    change Halted _ (run _ ⟨some (), initialFile 0 x⟩ j)
    rw [show run (undefinedRoutine n).body.program ⟨some (), initialFile 0 x⟩ j = ⟨none, S⟩ from hj]
    rfl


theorem add_two_clean : Clean addTwoStep (fun x => Part.some (x.get 1 + 2)) := by
  refine ⟨?_, fun x S => ?_⟩
  · apply sequence_no_internal_halt
    intro B hB
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl | rfl
    · exact (elementary_no_internal_halt (inputPort 2 0 1) (outputPort 2 0) (workPort 2 0 0)).2.2.2.2.2
    · exact (elementary_no_internal_halt (outputPort 2 0) (outputPort 2 0) (workPort 2 0 0)).2.1
    · exact (elementary_no_internal_halt (outputPort 2 0) (outputPort 2 0) (workPort 2 0 0)).2.1
  · let R := initialFile 0 x
    let o := outputPort 2 0
    let i := inputPort 2 0 1
    let z := workPort 2 0 0
    let U := updateRegister R o (R i)
    let V := updateRegister U o (U o + 1)
    let W := updateRegister V o (V o + 1)
    have hcopy : Exec (copyFragment i o z) R U := by
      apply (reaches_iff_run _ _ _).mpr
      exact ⟨5 * R i + 2, (copy_exact i o z (by decide) (by decide) (by decide) R
        (canonical_ports 0 x 0).2.1 ((canonical_ports 0 x 0).2.2.1 0)).1⟩
    have hseq : Exec addTwoStep.body R W :=
      (sequence_exec z _ R W).mpr (.cons hcopy
        (.cons (increment_returns o U) (.cons (increment_returns o V) (.nil W))))
    have hW : W = resultFile 0 x (x.get 1 + 2) := by
      simp only [W, V, U, resultFile, updateRegister, Function.update_self,
        Function.update_idem]
      have hi : R i = x.get 1 := (canonical_ports 0 x 0).1 1
      rw [hi]
    rw [hW] at hseq
    simp only [Part.mem_some_iff, exists_eq_left]
    constructor
    · intro h
      exact exec_unique _ _ _ _ h hseq
    · rintro rfl
      exact hseq


theorem recursion_trace :
    Exec (recursionInit (constantRoutine 2) addTwoStep)
      (initialFile _ (snoc List.Vector.nil 3))
      (recursionBoundary (constantRoutine 2) addTwoStep List.Vector.nil 3 0 2) ∧
    (∀ j < 3, Exec (recursionBody (constantRoutine 2) addTwoStep)
      (updateRegister
        (recursionBoundary (constantRoutine 2) addTwoStep List.Vector.nil 3 j (2 + 2 * j))
        (recursionD (constantRoutine 2) addTwoStep) (2 - j))
      (recursionBoundary (constantRoutine 2) addTwoStep List.Vector.nil 3 (j + 1) (4 + 2 * j))) ∧
    Exec exampleRecursion.body (initialFile _ (snoc List.Vector.nil 3))
      (resultFile _ (snoc List.Vector.nil 3) 8) ∧
    (List.ofFn fun j : Fin 4 =>
      let R := recursionBoundary (constantRoutine 2) addTwoStep List.Vector.nil 3 j.val (2 + 2 * j.val)
      (R (recursionD (constantRoutine 2) addTwoStep), R (recursionJ (constantRoutine 2) addTwoStep),
        R (outputPort 1 exampleRecursion.work), R (recursionV (constantRoutine 2) addTwoStep))) =
      [(3, 0, 2, 0), (2, 1, 4, 0), (1, 2, 6, 0), (0, 3, 8, 0)] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (recursion_initial_exec (constantRoutine 2) addTwoStep (fun _ => Part.some 2)
      (constant_clean 2) List.Vector.nil 3 _).mpr
    exact ⟨2, by simp, rfl⟩
  · intro j hj
    have hsub : 3 - j - 1 = 2 - j := by omega
    rw [← hsub]
    apply (recursion_body_exec (constantRoutine 2) addTwoStep
      (fun x => Part.some (x.get 1 + 2)) add_two_clean List.Vector.nil 3 j (2 + 2 * j) hj _).mpr
    refine ⟨4 + 2 * j, ?_, rfl⟩
    change 4 + 2 * j ∈ Part.some ((2 + 2 * j) + 2)
    simp only [Part.mem_some_iff]
    omega
  · apply (primitive_recursion_clean (constantRoutine 2) addTwoStep (fun _ => Part.some 2)
      (fun x => Part.some (x.get 1 + 2)) (constant_clean 2) add_two_clean).2
        (snoc List.Vector.nil 3) _ |>.mpr
    refine ⟨8, ?_, rfl⟩
    change 8 ∈ recValue (fun _ => Part.some 2)
      (fun x => Part.some (x.get 1 + 2)) List.Vector.nil 3
    norm_num [recValue, snoc]
    rfl
  · rfl


theorem undefined_base_at_zero :
    ∀ j, ¬ Halted (primitiveRecursionRoutine (undefinedRoutine 0) addTwoStep).body.program
      (run (primitiveRecursionRoutine (undefinedRoutine 0) addTwoStep).body.program
        ⟨(primitiveRecursionRoutine (undefinedRoutine 0) addTwoStep).body.entry,
          initialFile _ (snoc List.Vector.nil 0)⟩ j) := by
  have h := primitive_recursion_clean (undefinedRoutine 0) addTwoStep
    (fun _ => Part.none) (fun x => Part.some (x.get 1 + 2)) (undefined_clean 0) add_two_clean
  apply clean_undefined _ _ h (snoc List.Vector.nil 0)
  simp [partialRec, recValue]


theorem empty_composition {n : ℕ} (H : Routine 0) (h : PFunction 0) (hH : Clean H h)
    (G : Fin 0 → Routine n) (x : Args n) :
    routineEval (compositionRoutine H G) x = h List.Vector.nil := by
  have hc := composition_clean H G h (fun _ _ => Part.none) hH
    (fun i => Fin.elim0 i)
  rw [congrFun (clean_eval _ _ hc) x]
  exact strictComp_zero h (fun _ _ => Part.none) x


end Lemmatheca.Entry.TuringComputationAndRecursion
