import Lemmatheca.TuringComputationAndRecursion.Fragments
import Lemmatheca.PartialRecursiveFunctions.PartialRecursiveFunctions

/-! Actual placements and finite-table constructors for the finite-arity rules. -/
namespace Lemmatheca.ComputabilityTheory.RecursiveTapeCompiler

open CounterPrograms PartialRecursiveFunctions

structure Routine (n : ℕ) where
  work : ℕ
  body : Fragment (n + 2 + work)

def port (n w v : ℕ) : Fin (n + 2 + w) :=
  ⟨v % (n + 2 + w), Nat.mod_lt _ (by omega)⟩

def outputPort (n w : ℕ) : Fin (n + 2 + w) := ⟨0, by omega⟩
def inputPort (n w : ℕ) (i : Fin n) : Fin (n + 2 + w) := ⟨i.val + 1, by omega⟩
def workPort (n w : ℕ) (i : Fin (w + 1)) : Fin (n + 2 + w) := ⟨n + 1 + i.val, by omega⟩

def initialFile {n : ℕ} (w : ℕ) (x : Args n) : Registers (n + 2 + w) := fun r =>
  if h : 1 ≤ r.val ∧ r.val ≤ n then x.get ⟨r.val - 1, by omega⟩ else 0

def resultFile {n : ℕ} (w : ℕ) (x : Args n) (b : ℕ) : Registers (n + 2 + w) :=
  updateRegister (initialFile w x) (outputPort n w) b

def Clean {n : ℕ} (A : Routine n) (f : PFunction n) : Prop :=
  NoInternalHalt A.body ∧ ∀ x S,
    Exec A.body (initialFile A.work x) S ↔ ∃ b, b ∈ f x ∧ S = resultFile A.work x b

noncomputable def routineEval {n : ℕ} (A : Routine n) (x : Args n) : Part ℕ :=
  evalFrom A.body.program ⟨A.body.entry, initialFile A.work x⟩ (outputPort n A.work)

def placementMap {n w K : ℕ} (out : Fin K) (inp : Fin n → Fin K)
    (wrk : Fin (w + 1) → Fin K) (r : Fin (n + 2 + w)) : Fin K :=
  if h0 : r.val = 0 then out else if hi : r.val ≤ n then inp ⟨r.val - 1, by omega⟩
  else wrk ⟨r.val - (n + 1), by omega⟩

def place {n K : ℕ} (A : Routine n) (out : Fin K) (inp : Fin n → Fin K)
    (wrk : Fin (A.work + 1) → Fin K) : Fragment K :=
  renameFragment (placementMap out inp wrk) A.body

def zeroRoutine (n : ℕ) : Routine n := ⟨0, doneFragment (n + 2)⟩

def successorRoutine : Routine 1 :=
  ⟨0, seqFragment (workPort 1 0 0)
    (copyFragment (inputPort 1 0 0) (outputPort 1 0) (workPort 1 0 0))
    (incrementFragment (outputPort 1 0))⟩

def projectionRoutine {n : ℕ} (i : Fin n) : Routine n :=
  ⟨0, copyFragment (inputPort n 0 i) (outputPort n 0) (workPort n 0 0)⟩

def compositionPool {m n : ℕ} (H : Routine m) (G : Fin m → Routine n) : ℕ :=
  max H.work (Finset.univ.sup fun i => (G i).work)

def compositionTemp {m n : ℕ} (H : Routine m) (G : Fin m → Routine n) (i : Fin m) :
    Fin (n + 2 + (m + compositionPool H G)) :=
  port n (m + compositionPool H G) (n + 1 + i.val)

def compositionWork {m n : ℕ} (H : Routine m) (G : Fin m → Routine n) (j : ℕ) :
    Fin (n + 2 + (m + compositionPool H G)) :=
  port n (m + compositionPool H G) (n + m + 1 + j)

def compositionInner {m n : ℕ} (H : Routine m) (G : Fin m → Routine n) (i : Fin m) :
    Fragment (n + 2 + (m + compositionPool H G)) :=
  place (G i) (compositionTemp H G i) (inputPort n (m + compositionPool H G))
    (fun j => compositionWork H G j.val)

def compositionOuter {m n : ℕ} (H : Routine m) (G : Fin m → Routine n) :
    Fragment (n + 2 + (m + compositionPool H G)) :=
  place H (outputPort n (m + compositionPool H G)) (compositionTemp H G)
    (fun j => compositionWork H G j.val)

def compositionCalls {m n : ℕ} (H : Routine m) (G : Fin m → Routine n) :
    List (Fragment (n + 2 + (m + compositionPool H G))) :=
  List.ofFn (compositionInner H G)

def compositionFinish {m n : ℕ} (H : Routine m) (G : Fin m → Routine n) :
    Fragment (n + 2 + (m + compositionPool H G)) :=
  sequence (compositionWork H G 0)
    (compositionOuter H G :: List.ofFn (fun i => clearFragment (compositionTemp H G i)))

def compositionRoutine {m n : ℕ} (H : Routine m) (G : Fin m → Routine n) : Routine n :=
  ⟨m + compositionPool H G,
    seqFragment (compositionWork H G 0)
      (sequence (compositionWork H G 0) (compositionCalls H G)) (compositionFinish H G)⟩

def compositionBoundary {m n : ℕ} (H : Routine m) (G : Fin m → Routine n)
    (x : Args n) (a : Args m) (j : ℕ) : Registers (n + 2 + (m + compositionPool H G)) := fun r =>
  if hi : 1 ≤ r.val ∧ r.val ≤ n then x.get ⟨r.val - 1, by omega⟩
  else if ht : n + 1 ≤ r.val ∧ r.val < n + 1 + m then
    if r.val - (n + 1) < j then a.get ⟨r.val - (n + 1), by omega⟩ else 0
  else 0

def recursionPool {n : ℕ} (G : Routine n) (H : Routine (n + 2)) : ℕ := max G.work H.work

def recursionPort {n : ℕ} (G : Routine n) (H : Routine (n + 2)) (v : ℕ) :
    Fin ((n + 1) + 2 + (4 + recursionPool G H)) :=
  port (n + 1) (4 + recursionPool G H) v

def recursionD {n : ℕ} (G : Routine n) (H : Routine (n + 2)) := recursionPort G H (n + 2)
def recursionJ {n : ℕ} (G : Routine n) (H : Routine (n + 2)) := recursionPort G H (n + 3)
def recursionV {n : ℕ} (G : Routine n) (H : Routine (n + 2)) := recursionPort G H (n + 4)
def recursionCopyScratch {n : ℕ} (G : Routine n) (H : Routine (n + 2)) := recursionPort G H (n + 5)
def recursionWork {n : ℕ} (G : Routine n) (H : Routine (n + 2)) (j : ℕ) :=
  recursionPort G H (n + 6 + j)

def recursionBase {n : ℕ} (G : Routine n) (H : Routine (n + 2)) :
    Fragment ((n + 1) + 2 + (4 + recursionPool G H)) :=
  place G (outputPort (n + 1) (4 + recursionPool G H))
    (fun i => recursionPort G H (i.val + 1)) (fun j => recursionWork G H j.val)

def recursionStepInputs {n : ℕ} (G : Routine n) (H : Routine (n + 2)) (i : Fin (n + 2)) :
    Fin ((n + 1) + 2 + (4 + recursionPool G H)) :=
  if i.val < n then recursionPort G H (i.val + 1)
  else if i.val = n then recursionJ G H else outputPort (n + 1) (4 + recursionPool G H)

def recursionStep {n : ℕ} (G : Routine n) (H : Routine (n + 2)) :
    Fragment ((n + 1) + 2 + (4 + recursionPool G H)) :=
  place H (recursionV G H) (recursionStepInputs G H) (fun j => recursionWork G H j.val)

def recursionInit {n : ℕ} (G : Routine n) (H : Routine (n + 2)) :
    Fragment ((n + 1) + 2 + (4 + recursionPool G H)) :=
  seqFragment (recursionWork G H 0)
    (copyFragment (inputPort (n + 1) (4 + recursionPool G H) (Fin.last n))
      (recursionD G H) (recursionCopyScratch G H)) (recursionBase G H)

def recursionBody {n : ℕ} (G : Routine n) (H : Routine (n + 2)) :
    Fragment ((n + 1) + 2 + (4 + recursionPool G H)) :=
  sequence (recursionWork G H 0)
    [recursionStep G H, clearFragment (outputPort (n + 1) (4 + recursionPool G H)),
      transferFragment (recursionV G H) (outputPort (n + 1) (4 + recursionPool G H)),
      incrementFragment (recursionJ G H)]

def primitiveRecursionRoutine {n : ℕ} (G : Routine n) (H : Routine (n + 2)) : Routine (n + 1) :=
  ⟨4 + recursionPool G H, sequence (recursionWork G H 0)
    [recursionInit G H, repeatFragment (recursionD G H) (recursionWork G H 0) (recursionBody G H),
      clearFragment (recursionJ G H)]⟩

def recursionBoundary {n : ℕ} (G : Routine n) (H : Routine (n + 2))
    (x : Args n) (N j a : ℕ) : Registers ((n + 1) + 2 + (4 + recursionPool G H)) :=
  updateRegister (updateRegister
    (resultFile (4 + recursionPool G H) (snoc x N) a) (recursionD G H) (N - j)) (recursionJ G H) j

def minimizationPort {n : ℕ} (F : Routine (n + 1)) (v : ℕ) : Fin (n + 2 + (3 + F.work)) :=
  port n (3 + F.work) v

def minimizationJ {n : ℕ} (F : Routine (n + 1)) := minimizationPort F (n + 1)
def minimizationV {n : ℕ} (F : Routine (n + 1)) := minimizationPort F (n + 2)
def minimizationCopyScratch {n : ℕ} (F : Routine (n + 1)) := minimizationPort F (n + 3)
def minimizationWork {n : ℕ} (F : Routine (n + 1)) (j : ℕ) := minimizationPort F (n + 4 + j)

def minimizationInputs {n : ℕ} (F : Routine (n + 1)) (i : Fin (n + 1)) : Fin (n + 2 + (3 + F.work)) :=
  if i.val < n then minimizationPort F (i.val + 1) else minimizationJ F

def minimizationTest {n : ℕ} (F : Routine (n + 1)) : Fragment (n + 2 + (3 + F.work)) :=
  place F (minimizationV F) (minimizationInputs F) (fun j => minimizationWork F j.val)

def minimizationPositive {n : ℕ} (F : Routine (n + 1)) : Fragment (n + 2 + (3 + F.work)) :=
  seqFragment (minimizationWork F 0) (clearFragment (minimizationV F))
    (incrementFragment (minimizationJ F))

def minimizationZero {n : ℕ} (F : Routine (n + 1)) : Fragment (n + 2 + (3 + F.work)) :=
  seqFragment (minimizationWork F 0)
    (copyFragment (minimizationJ F) (outputPort n (3 + F.work)) (minimizationCopyScratch F))
    (clearFragment (minimizationJ F))

def minimizationRoutine {n : ℕ} (F : Routine (n + 1)) : Routine n :=
  ⟨3 + F.work, searchFragment (minimizationV F) (minimizationWork F 0)
    (minimizationTest F) (minimizationPositive F) (minimizationZero F)⟩

def minimizationBoundary {n : ℕ} (F : Routine (n + 1)) (x : Args n) (j : ℕ) :
    Registers (n + 2 + (3 + F.work)) :=
  updateRegister (initialFile (3 + F.work) x) (minimizationJ F) j


private theorem exec_unique {k : ℕ} (B : Fragment k) (R S T : Registers k)
    (hS : Exec B R S) (hT : Exec B R T) : S=T := by
  obtain ⟨j,hj⟩ := (reaches_iff_run _ _ _).mp hS
  obtain ⟨t,ht⟩ := (reaches_iff_run _ _ _).mp hT
  funext r
  apply outputFrom_unique B.program ⟨B.entry,R⟩ r _ _
  · exact ⟨j,by rw [hj];rfl,by rw [hj]⟩
  · exact ⟨t,by rw [ht];rfl,by rw [ht]⟩

private theorem initial_agrees {n K : ℕ} (A : Routine n)
    (out : Fin K) (inp : Fin n → Fin K) (wrk : Fin (A.work+1) → Fin K)
    (x : Args n) (U : Registers K) (hout : U out=0)
    (hin : ∀ i,U (inp i)=x.get i) (hw : ∀ j,U (wrk j)=0) :
    FrameAgrees (placementMap out inp wrk) (initialFile A.work x) U := by
  intro r
  by_cases h0 : r.val=0
  · simp [placementMap,h0,initialFile,hout]
  · by_cases hi : r.val≤n
    · have h1 : 1≤r.val := by omega
      simpa [placementMap,h0,hi,initialFile,h1] using hin ⟨r.val-1,by omega⟩
    · simpa [placementMap,h0,hi,initialFile] using hw ⟨r.val-(n+1),by omega⟩

private theorem result_agrees {n K : ℕ} (A : Routine n)
    (out : Fin K) (inp : Fin n → Fin K) (wrk : Fin (A.work+1) → Fin K)
    (hmap : Function.Injective (placementMap out inp wrk))
    (x : Args n) (U : Registers K)
    (hU : FrameAgrees (placementMap out inp wrk) (initialFile A.work x) U) (b : ℕ) :
    FrameAgrees (placementMap out inp wrk) (resultFile A.work x b) (updateRegister U out b) ∧
    ExternalFrame (placementMap out inp wrk) U (updateRegister U out b) := by
  have ho : placementMap out inp wrk (outputPort n A.work)=out := by simp [placementMap,outputPort]
  constructor
  · intro r
    by_cases hr : r=outputPort n A.work
    · subst r;simp [ho,resultFile,updateRegister]
    · have hn : placementMap out inp wrk r≠out := by
        intro h
        exact hr (hmap (h.trans ho.symm))
      simp [resultFile,updateRegister,hr,hn,hU r]
  · intro r hr
    have hn : r≠out := by
      intro h
      exact hr ⟨outputPort n A.work,ho.trans h.symm⟩
    simp [updateRegister,hn]

private theorem ambient_unique {k K : ℕ} (ρ : Fin k → Fin K)
    (R : Registers k) (U V W : Registers K)
    (hV : FrameAgrees ρ R V) (hW : FrameAgrees ρ R W)
    (hfV : ExternalFrame ρ U V) (hfW : ExternalFrame ρ U W) : V=W := by
  funext r
  by_cases hr : r∈Set.range ρ
  · obtain ⟨t,rfl⟩ := hr
    exact (hV t).trans (hW t).symm
  · exact (hfV r hr).trans (hfW r hr).symm

theorem canonical_ports {n : ℕ} (w : ℕ) (x : Args n) (b : ℕ) :
    (∀ i, initialFile w x (inputPort n w i) = x.get i) ∧
    initialFile w x (outputPort n w) = 0 ∧
    (∀ j, initialFile w x (workPort n w j) = 0) ∧
    resultFile w x b (outputPort n w) = b ∧
    (∀ i, resultFile w x b (inputPort n w i) = x.get i) ∧
    ∀ j, resultFile w x b (workPort n w j) = 0 := by
  classical
  have hin : ∀ i, initialFile w x (inputPort n w i) = x.get i := by
    intro i
    rw [initialFile, dite_eq_left (by dsimp [inputPort]; omega)]
    congr 1
  have hout : initialFile w x (outputPort n w) = 0 := by simp [initialFile, outputPort]
  have hw : ∀ j, initialFile w x (workPort n w j) = 0 := by
    intro j
    rw [initialFile, dite_eq_right (by dsimp [workPort]; omega)]
  refine ⟨hin, hout, hw, ?_, ?_, ?_⟩
  · simp [resultFile, updateRegister]
  · intro i
    have hn : inputPort n w i ≠ outputPort n w := by
      intro h
      have := congrArg Fin.val h
      dsimp [inputPort, outputPort] at this
      omega
    simpa only [resultFile, updateRegister, Function.update_of_ne hn] using hin i
  · intro j
    have hn : workPort n w j ≠ outputPort n w := by
      intro h
      have := congrArg Fin.val h
      dsimp [workPort, outputPort] at this
      omega
    simpa only [resultFile, updateRegister, Function.update_of_ne hn] using hw j

theorem placement_injective {n w K : ℕ} (out : Fin K) (inp : Fin n → Fin K)
    (wrk : Fin (w + 1) → Fin K) (hi : Function.Injective inp) (hw : Function.Injective wrk)
    (hoi : out ∉ Set.range inp) (how : out ∉ Set.range wrk)
    (hiw : Disjoint (Set.range inp) (Set.range wrk)) :
    Function.Injective (placementMap out inp wrk) := by
  intro a b hab
  unfold placementMap at hab
  split_ifs at hab
  all_goals first
  | (apply Fin.ext; omega)
  | (have h := congrArg Fin.val (hi hab); apply Fin.ext; dsimp at h; omega)
  | (have h := congrArg Fin.val (hw hab); apply Fin.ext; dsimp at h; omega)
  | exact False.elim (hoi ⟨_, hab⟩)
  | exact False.elim (hoi ⟨_, hab.symm⟩)
  | exact False.elim (how ⟨_, hab⟩)
  | exact False.elim (how ⟨_, hab.symm⟩)
  | exact False.elim ((Set.disjoint_left.mp hiw) ⟨_, rfl⟩ ⟨_, hab⟩)
  | exact False.elim ((Set.disjoint_left.mp hiw) ⟨_, rfl⟩ ⟨_, hab.symm⟩)

theorem placed_clean_exec {n K : ℕ} (A : Routine n) (f : PFunction n) (hA : Clean A f)
    (out : Fin K) (inp : Fin n → Fin K) (wrk : Fin (A.work + 1) → Fin K)
    (hmap : Function.Injective (placementMap out inp wrk))
    (x : Args n) (U V : Registers K) (hout : U out = 0)
    (hin : ∀ i, U (inp i) = x.get i) (hw : ∀ j, U (wrk j) = 0) :
    Exec (place A out inp wrk) U V ↔ ∃ b, b ∈ f x ∧ V = updateRegister U out b := by
  have hU := initial_agrees A out inp wrk x U hout hin hw
  change Exec (renameFragment (placementMap out inp wrk) A.body) U V ↔ _
  rw [rename_exec _ hmap A.body (initialFile A.work x) U V hU]
  constructor
  · rintro ⟨S,hS,hV,hfV⟩
    obtain ⟨b,hb,rfl⟩ := (hA.2 x S).mp hS
    obtain ⟨hW,hfW⟩ := result_agrees A out inp wrk hmap x U hU b
    exact ⟨b,hb,ambient_unique _ _ U V _ hV hW hfV hfW⟩
  · rintro ⟨b,hb,rfl⟩
    obtain ⟨hW,hfW⟩ := result_agrees A out inp wrk hmap x U hU b
    exact ⟨resultFile A.work x b,(hA.2 x _).mpr ⟨b,hb,rfl⟩,hW,hfW⟩

theorem clean_eval {n : ℕ} (A : Routine n) (f : PFunction n) (hA : Clean A f) :
    routineEval A = f := by
  funext x
  apply Part.ext
  intro b
  change b∈evalFrom A.body.program ⟨A.body.entry,initialFile A.work x⟩ (outputPort n A.work) ↔ _
  rw [evalFrom_spec]
  constructor
  · rintro ⟨j,hj,hb⟩
    have hp := (fragment_halt_iff A.body hA.1 _).mp hj
    have he : run A.body.program ⟨A.body.entry,initialFile A.work x⟩ j =
        ⟨none,(run A.body.program ⟨A.body.entry,initialFile A.work x⟩ j).regs⟩ :=
      Config.ext hp rfl
    have hx := (hA.2 x _).mp ((reaches_iff_run _ _ _).mpr ⟨j,he⟩)
    obtain ⟨c,hc,hfile⟩ := hx
    have hbc : b=c := hb.symm.trans (by rw [hfile];simp [resultFile,updateRegister])
    simpa [hbc] using hc
  · intro hb
    obtain ⟨j,hj⟩ := (reaches_iff_run _ _ _).mp ((hA.2 x _).mpr ⟨b,hb,rfl⟩)
    exact ⟨j,by rw [hj];rfl,by rw [hj];simp [resultFile,updateRegister]⟩

theorem clean_undefined {n : ℕ} (A : Routine n) (f : PFunction n) (hA : Clean A f)
    (x : Args n) (hx : ¬ (f x).Dom) :
    ∀ j, ¬ Halted A.body.program
      (run A.body.program ⟨A.body.entry, initialFile A.work x⟩ j) := by
  intro j hj
  have hm : (run A.body.program ⟨A.body.entry,initialFile A.work x⟩ j).regs (outputPort n A.work) ∈
      routineEval A x := (evalFrom_spec _ _ _ _).mpr ⟨j,hj,rfl⟩
  rw [clean_eval A f hA] at hm
  obtain ⟨hdom,_⟩ := hm
  exact hx hdom


private theorem exec_iff_eq {k : ℕ} (B : Fragment k) (R T : Registers k)
    (hT : Exec B R T) (S : Registers k) : Exec B R S ↔ S=T := by
  exact ⟨fun hS => exec_unique B R S T hS hT,fun h => h.symm ▸ hT⟩

private theorem copy_exec_eq {k : ℕ} (x y z : Fin k) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z)
    (R : Registers k) (hy : R y=0) (hz : R z=0) (S : Registers k) :
    Exec (copyFragment x y z) R S ↔ S=updateRegister R y (R x) := by
  exact exec_iff_eq _ _ _ ((reaches_iff_run _ _ _).mpr
    ⟨5*R x+2,(copy_exact x y z hxy hxz hyz R hy hz).1⟩) S

private theorem increment_exec_eq {k : ℕ} (r : Fin k) (R S : Registers k) :
    Exec (incrementFragment r) R S ↔ S=updateRegister R r (R r+1) := by
  apply exec_iff_eq _ _ _ ?_ S
  apply (reaches_iff_run _ _ _).mpr
  exact ⟨1,rfl⟩

private theorem clear_exec_eq {k : ℕ} (r : Fin k) (R S : Registers k) :
    Exec (clearFragment r) R S ↔ S=updateRegister R r 0 := by
  exact exec_iff_eq _ _ _ ((reaches_iff_run _ _ _).mpr ⟨R r+1,(clear_exact r R).1⟩) S

private theorem transfer_exec_eq {k : ℕ} (r t : Fin k) (hrt : r≠t) (R S : Registers k) :
    Exec (transferFragment r t) R S ↔ S=updateRegister (updateRegister R r 0) t (R t+R r) := by
  exact exec_iff_eq _ _ _ ((reaches_iff_run _ _ _).mpr ⟨2*R r+1,(transfer_exact r t hrt R).1⟩) S

private theorem initial_copy_exec {n : ℕ} (i : Fin n) (x : Args n) (S : Registers (n+2)) :
    Exec (copyFragment (inputPort n 0 i) (outputPort n 0) (workPort n 0 0))
      (initialFile 0 x) S ↔ S=resultFile 0 x (x.get i) := by
  have hio : inputPort n 0 i ≠ outputPort n 0 := by
    intro h;have hv := congrArg Fin.val h;dsimp [inputPort,outputPort] at hv;omega
  have hiw : inputPort n 0 i ≠ workPort n 0 0 := by
    intro h;have hv := congrArg Fin.val h;dsimp [inputPort,workPort] at hv;omega
  have how : outputPort n 0 ≠ workPort n 0 0 := by
    intro h;have hv := congrArg Fin.val h;dsimp [outputPort,workPort] at hv;omega
  have hc := canonical_ports 0 x 0
  simpa only [hc.1 i,resultFile] using
    copy_exec_eq _ _ _ hio hiw how (initialFile 0 x) hc.2.1 (hc.2.2.1 0) S

theorem zero_clean (n : ℕ) : Clean (zeroRoutine n) (fun _ => Part.some 0) := by
  dsimp only [Clean,zeroRoutine]
  constructor
  · intro p;exact Empty.elim p
  · intro x S
    have hz : resultFile 0 x 0=initialFile 0 x := by
      funext r
      by_cases hr : r=outputPort n 0
      · subst r;simp [resultFile,updateRegister,(canonical_ports 0 x 0).2.1]
      · simp [resultFile,updateRegister,hr]
    change Reaches (doneFragment (n+2)).program ⟨none,initialFile 0 x⟩ ⟨none,S⟩ ↔ _
    have he : Reaches (doneFragment (n+2)).program ⟨none,initialFile 0 x⟩ ⟨none,S⟩ ↔ S=initialFile 0 x := by
      apply exec_iff_eq (doneFragment (n+2)) _ _ .refl S
    rw [he]
    simp [Part.mem_some_iff,hz]
theorem successor_clean : Clean successorRoutine (fun x => Part.some (x.get 0 + 1)) := by
  dsimp only [Clean,successorRoutine]
  constructor
  · apply seq_no_internal_halt
    · exact (elementary_no_internal_halt (inputPort 1 0 0) (outputPort 1 0) (workPort 1 0 0)).2.2.2.2.2
    · exact (elementary_no_internal_halt (outputPort 1 0) (outputPort 1 0) (outputPort 1 0)).2.1
  · intro x S
    rw [seq_exec]
    simp only [initial_copy_exec]
    simp only [exists_eq_left]
    rw [increment_exec_eq]
    simp [resultFile,updateRegister,Part.mem_some_iff]
theorem projection_clean {n : ℕ} (i : Fin n) :
    Clean (projectionRoutine i) (fun x => Part.some (x.get i)) := by
  dsimp only [Clean,projectionRoutine]
  constructor
  · exact (elementary_no_internal_halt (inputPort n 0 i) (outputPort n 0) (workPort n 0 0)).2.2.2.2.2
  · intro x S
    change Exec (copyFragment (inputPort n 0 i) (outputPort n 0) (workPort n 0 0)) (initialFile 0 x) S ↔ _
    rw [initial_copy_exec]
    simp [Part.mem_some_iff]

theorem composition_placements {m n : ℕ} (H : Routine m) (G : Fin m → Routine n) :
    (∀ i, Function.Injective (placementMap (compositionTemp H G i)
      (inputPort n (m + compositionPool H G)) (fun j : Fin ((G i).work + 1) => compositionWork H G j.val))) ∧
    Function.Injective (placementMap (outputPort n (m + compositionPool H G))
      (compositionTemp H G) (fun j : Fin (H.work + 1) => compositionWork H G j.val)) ∧
    (∀ i, (compositionTemp H G i).val = n + 1 + i.val) ∧
    ∀ j, j ≤ compositionPool H G → (compositionWork H G j).val = n + m + 1 + j := by
  have hg : ∀ i, (G i).work ≤ compositionPool H G := by
    intro i
    exact le_trans (Finset.le_sup (f := fun i => (G i).work) (Finset.mem_univ i)) (le_max_right _ _)
  have hh : H.work ≤ compositionPool H G := le_max_left _ _
  have ht : ∀ i, (compositionTemp H G i).val = n + 1 + i.val := by
    intro i
    apply Nat.mod_eq_of_lt
    have := i.isLt
    omega
  have hw : ∀ j, j ≤ compositionPool H G → (compositionWork H G j).val = n + m + 1 + j := by
    intro j hj
    apply Nat.mod_eq_of_lt
    omega
  have hin : ∀ i, (inputPort n (m + compositionPool H G) i).val = i.val + 1 := fun _ => rfl
  have hwi : ∀ i (j : Fin ((G i).work + 1)),
      (compositionWork H G j.val).val = n + m + 1 + j.val := by
    intro i j
    exact hw j.val (by have := j.isLt; have := hg i; omega)
  have hwh : ∀ j : Fin (H.work + 1),
      (compositionWork H G j.val).val = n + m + 1 + j.val := by
    intro j
    exact hw j.val (by have := j.isLt; omega)
  refine ⟨?_, ?_, ht, hw⟩
  · intro i
    apply placement_injective
    · intro a b h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa only [hin, Nat.add_right_cancel_iff] using hv
    · intro a b h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa only [hwi, Nat.add_left_cancel_iff] using hv
    · rintro ⟨a, h⟩
      have hv := congrArg Fin.val h
      rw [hin, ht] at hv
      have := a.isLt
      omega
    · rintro ⟨a, h⟩
      have hv := congrArg Fin.val h
      rw [hwi, ht] at hv
      have := i.isLt
      omega
    · apply Set.disjoint_left.mpr
      rintro a ⟨b, rfl⟩ ⟨c, h⟩
      have hv := congrArg Fin.val h
      rw [hwi, hin] at hv
      have := b.isLt
      omega
  · apply placement_injective
    · intro a b h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa only [ht, Nat.add_left_cancel_iff] using hv
    · intro a b h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa only [hwh, Nat.add_left_cancel_iff] using hv
    · rintro ⟨a, h⟩
      have hv := congrArg Fin.val h
      rw [ht] at hv
      change n + 1 + a.val = 0 at hv
      omega
    · rintro ⟨a, h⟩
      have hv := congrArg Fin.val h
      rw [hwh] at hv
      change n + m + 1 + a.val = 0 at hv
      omega
    · apply Set.disjoint_left.mpr
      rintro a ⟨b, rfl⟩ ⟨c, h⟩
      have hv := congrArg Fin.val h
      rw [hwh, ht] at hv
      have := b.isLt
      omega


private theorem co_temp_val {m n : ℕ} (H : Routine m) (G : Fin m → Routine n) (i : Fin m) :
    (compositionTemp H G i).val=n+1+i.val := (composition_placements H G).2.2.1 i
private theorem co_work_val {m n : ℕ} (H : Routine m) (G : Fin m → Routine n) (j : ℕ)
    (hj : j ≤ compositionPool H G) :
    (compositionWork H G j).val=n+m+1+j := (composition_placements H G).2.2.2 j hj

private theorem co_boundary_input {m n : ℕ} (H : Routine m) (G : Fin m → Routine n)
    (x : Args n) (a : Args m) (j : ℕ) (i : Fin n) :
    compositionBoundary H G x a j (inputPort n (m+compositionPool H G) i)=x.get i := by
  have hi : 1 ≤ i.val+1 ∧ i.val+1 ≤ n := by have := i.isLt;omega
  simp [compositionBoundary,inputPort,hi]

private theorem co_boundary_temp {m n : ℕ} (H : Routine m) (G : Fin m → Routine n)
    (x : Args n) (a : Args m) (j : ℕ) (i : Fin m) :
    compositionBoundary H G x a j (compositionTemp H G i)=if i.val < j then a.get i else 0 := by
  have hn : ¬(1 ≤ (compositionTemp H G i).val ∧ (compositionTemp H G i).val ≤ n) := by
    rw [co_temp_val];omega
  have ht : n+1 ≤ (compositionTemp H G i).val ∧ (compositionTemp H G i).val < n+1+m := by
    rw [co_temp_val];have := i.isLt;omega
  simp only [compositionBoundary,dite_eq_right hn,dite_eq_left ht]
  simp [co_temp_val]

private theorem co_boundary_work {m n : ℕ} (H : Routine m) (G : Fin m → Routine n)
    (x : Args n) (a : Args m) (j t : ℕ) (ht : t ≤ compositionPool H G) :
    compositionBoundary H G x a j (compositionWork H G t)=0 := by
  have hn : ¬(1 ≤ (compositionWork H G t).val ∧ (compositionWork H G t).val ≤ n) := by
    rw [co_work_val H G t ht];omega
  have hp : ¬(n+1 ≤ (compositionWork H G t).val ∧ (compositionWork H G t).val < n+1+m) := by
    rw [co_work_val H G t ht];omega
  simp only [compositionBoundary,dite_eq_right hn,dite_eq_right hp]

private theorem co_boundary_zero {m n : ℕ} (H : Routine m) (G : Fin m → Routine n)
    (x : Args n) (a : Args m) : compositionBoundary H G x a 0=initialFile _ x := by
  funext r
  simp [compositionBoundary,initialFile]

private def co_extend {m : ℕ} (a : Args m) (i : Fin m) (b : ℕ) : Args m :=
  List.Vector.ofFn (fun t => if t=i then b else a.get t)

private theorem co_extend_self {m : ℕ} (a : Args m) (i : Fin m) : co_extend a i (a.get i)=a := by
  apply List.Vector.ext
  intro t
  by_cases ht : t=i <;> simp [co_extend,ht]

private theorem co_boundary_update {m n : ℕ} (H : Routine m) (G : Fin m → Routine n)
    (x : Args n) (a : Args m) (i : Fin m) (b : ℕ) :
    updateRegister (compositionBoundary H G x a i.val) (compositionTemp H G i) b=
      compositionBoundary H G x (co_extend a i b) (i.val+1) := by
  funext r
  by_cases hin : 1 ≤ r.val ∧ r.val ≤ n
  · have hne : r ≠ compositionTemp H G i := by
      intro h;have hh := congrArg Fin.val h;rw [co_temp_val] at hh;omega
    simp only [updateRegister,Function.update_of_ne hne,compositionBoundary,dite_eq_left hin]
  · by_cases ht : n+1 ≤ r.val ∧ r.val < n+1+m
    · let t : Fin m := ⟨r.val-(n+1),by omega⟩
      have hr : r=compositionTemp H G t := by
        apply Fin.ext
        rw [co_temp_val]
        dsimp [t]
        omega
      rw [hr]
      by_cases he : t=i
      · rw [he]
        simp [updateRegister,co_boundary_temp,co_extend]
      · have hports : compositionTemp H G t ≠ compositionTemp H G i := by
          intro h
          apply he
          apply Fin.ext
          have hh := congrArg Fin.val h
          rw [co_temp_val,co_temp_val] at hh
          omega
        have hval : t.val ≠ i.val := fun h => he (Fin.ext h)
        by_cases hlt : t.val < i.val
        · have hlt' : t.val < i.val+1 := by omega
          simp [updateRegister,hports,co_boundary_temp,co_extend,he,hlt,hlt']
        · have hlt' : ¬t.val < i.val+1 := by omega
          simp [updateRegister,hports,co_boundary_temp,co_extend,hlt,hlt']
    · have hne : r ≠ compositionTemp H G i := by
        intro h
        apply ht
        rw [h,co_temp_val]
        have := i.isLt
        omega
      simp only [updateRegister,Function.update_of_ne hne,compositionBoundary,dite_eq_right hin,dite_eq_right ht]

private theorem co_inner_exec {m n : ℕ} (H : Routine m) (G : Fin m → Routine n)
    (g : Fin m → PFunction n) (hG : ∀ i,Clean (G i) (g i))
    (x : Args n) (a : Args m) (i : Fin m)
    (S : Registers (n+2+(m+compositionPool H G))) :
    Exec (compositionInner H G i) (compositionBoundary H G x a i.val) S ↔
      ∃ b,b∈g i x ∧ S=updateRegister (compositionBoundary H G x a i.val) (compositionTemp H G i) b := by
  apply placed_clean_exec (G i) (g i) (hG i) _ _ _ ((composition_placements H G).1 i) x _ S
    (by simp [co_boundary_temp]) (co_boundary_input H G x a i.val)
  intro t
  apply co_boundary_work
  have hbound : (G i).work ≤ compositionPool H G :=
    le_trans (Finset.le_sup (f := fun i => (G i).work) (Finset.mem_univ i)) (le_max_right _ _)
  have := t.isLt
  omega

private theorem sequence_append_exec {k : ℕ} (z : Fin k) (as bs : List (Fragment k))
    (R S : Registers k) : Exec (sequence z (as++bs)) R S ↔
      ∃ U,Exec (sequence z as) R U ∧ Exec (sequence z bs) U S := by
  induction as generalizing R with
  | nil =>
      constructor
      · intro h;exact ⟨R,.refl,h⟩
      · rintro ⟨U,hU,hrest⟩
        have he := (exec_iff_eq (doneFragment k) R R .refl U).mp hU
        subst U
        exact hrest
  | cons B as ih =>
      constructor
      · intro h
        obtain ⟨V,hB,hrest⟩ := (seq_exec z B (sequence z (as++bs)) R S).mp h
        obtain ⟨U,htail,hbs⟩ := (ih V).mp hrest
        exact ⟨U,(seq_exec z B (sequence z as) R U).mpr ⟨V,hB,htail⟩,hbs⟩
      · rintro ⟨U,hU,hbs⟩
        obtain ⟨V,hB,htail⟩ := (seq_exec z B (sequence z as) R U).mp hU
        exact (seq_exec z B (sequence z (as++bs)) R S).mpr ⟨V,hB,(ih V).mpr ⟨U,htail,hbs⟩⟩

private theorem sequence_single_exec {k : ℕ} (z : Fin k) (B : Fragment k) (R S : Registers k) :
    Exec (sequence z [B]) R S ↔ Exec B R S := by
  constructor
  · intro h
    obtain ⟨U,hB,hU⟩ := (seq_exec z B (doneFragment k) R S).mp h
    have he := (exec_iff_eq (doneFragment k) U U .refl S).mp hU
    simpa only [he] using hB
  · intro h
    exact (seq_exec z B (doneFragment k) R S).mpr ⟨S,h,.refl⟩

theorem composition_prefix {m n : ℕ} (H : Routine m) (G : Fin m → Routine n)
    (g : Fin m → PFunction n) (hG : ∀ i, Clean (G i) (g i)) (x : Args n)
    (j : ℕ) (hj : j ≤ m) (R : Registers (n + 2 + (m + compositionPool H G))) :
    Exec (sequence (compositionWork H G 0) ((compositionCalls H G).take j)) (initialFile _ x) R ↔
      ∃ a : Args m, (∀ i, i.val < j → a.get i ∈ g i x) ∧ R = compositionBoundary H G x a j := by
  induction j generalizing R with
  | zero =>
      simp only [List.take_zero]
      constructor
      · intro h
        have hr := (exec_iff_eq (doneFragment _) _ _ .refl R).mp h
        refine ⟨List.Vector.ofFn (fun _ => 0),by intro i hi;omega,?_⟩
        exact hr.trans (co_boundary_zero H G x _).symm
      · rintro ⟨a,_,hr⟩
        rw [co_boundary_zero] at hr
        subst R
        exact .refl
  | succ j ih =>
      have hjm : j<m := by omega
      let i : Fin m := ⟨j,hjm⟩
      have hl : (compositionCalls H G).take (j+1)=
          (compositionCalls H G).take j ++ [compositionInner H G i] := by
        rw [List.take_succ_eq_append_getElem (by simp [compositionCalls];omega)]
        simp [compositionCalls,i]
      rw [hl,sequence_append_exec]
      simp only [sequence_single_exec]
      constructor
      · rintro ⟨U,hU,hcall⟩
        obtain ⟨a,ha,rfl⟩ := (ih (by omega) U).mp hU
        obtain ⟨b,hb,hR⟩ := (co_inner_exec H G g hG x a i R).mp hcall
        refine ⟨co_extend a i b,?_,?_⟩
        · intro t ht
          by_cases he : t=i
          · subst t;simpa [co_extend] using hb
          · have hval : t.val≠j := fun h => he (Fin.ext h)
            have ht' : t.val<j := by omega
            simpa [co_extend,he] using ha t ht'
        · exact hR.trans (co_boundary_update H G x a i b)
      · rintro ⟨a,ha,hR⟩
        refine ⟨compositionBoundary H G x a j,(ih (by omega) _).mpr ⟨a,fun t ht => ha t (by omega),rfl⟩,?_⟩
        apply (co_inner_exec H G g hG x a i R).mpr
        refine ⟨a.get i,ha i (by dsimp [i];omega),?_⟩
        have he := co_boundary_update H G x a i (a.get i)
        rw [co_extend_self] at he
        exact hR.trans he.symm

private theorem rcf_clear_sequence {k : ℕ} (z : Fin k) (ps : List (Fin k)) (R S : Registers k) :
    Exec (sequence z (ps.map clearFragment)) R S ↔
      S = ps.foldl (fun U p => updateRegister U p 0) R := by
  induction ps generalizing R with
  | nil => exact exec_iff_eq (doneFragment k) R R .refl S
  | cons p ps ih =>
      rw [List.map_cons, sequence, seq_exec]
      simp only [clear_exec_eq, exists_eq_left, ih, List.foldl_cons]

private theorem rcf_fold_clear {k : ℕ} (ps : List (Fin k)) (R : Registers k) (r : Fin k) :
    (ps.foldl (fun U p => updateRegister U p 0) R) r = if r ∈ ps then 0 else R r := by
  induction ps generalizing R with
  | nil => simp
  | cons p ps ih =>
      rw [List.foldl_cons, ih]
      by_cases hp : r = p <;> by_cases hs : r ∈ ps <;> simp [hp, hs, updateRegister]

private theorem rcf_temp_mem {m n : ℕ} (H : Routine m) (G : Fin m → Routine n)
    (r : Fin (n + 2 + (m + compositionPool H G))) :
    r ∈ List.ofFn (compositionTemp H G) ↔ n + 1 ≤ r.val ∧ r.val < n + 1 + m := by
  rw [List.mem_ofFn]
  have ht := (composition_placements H G).2.2.1
  constructor
  · rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    rw [ht] at hv
    have := i.isLt
    omega
  · intro hr
    refine ⟨⟨r.val - (n + 1), by omega⟩, ?_⟩
    apply Fin.ext
    rw [ht]
    change n + 1 + (r.val - (n + 1)) = r.val
    omega

set_option backward.isDefEq.respectTransparency false in
theorem composition_finish {m n : ℕ} (H : Routine m) (G : Fin m → Routine n)
    (h : PFunction m) (hH : Clean H h) (x : Args n) (a : Args m)
    (S : Registers (n + 2 + (m + compositionPool H G))) :
    Exec (compositionFinish H G) (compositionBoundary H G x a m) S ↔
      ∃ b, b ∈ h a ∧ S = resultFile (m + compositionPool H G) x b := by
  classical
  let R := compositionBoundary H G x a m
  let o := outputPort n (m + compositionPool H G)
  have ht := (composition_placements H G).2.2.1
  have hw := (composition_placements H G).2.2.2
  have hout : R o = 0 := by simp [R, o, compositionBoundary, outputPort]
  have hin : ∀ i, R (compositionTemp H G i) = a.get i := by
    intro i
    have hiv := ht i
    have hir : n + 1 ≤ (compositionTemp H G i).val ∧
        (compositionTemp H G i).val < n + 1 + m := by have := i.isLt; omega
    have hni : ¬ (1 ≤ (compositionTemp H G i).val ∧ (compositionTemp H G i).val ≤ n) := by omega
    simp only [R, compositionBoundary, dite_eq_right hni, dite_eq_left hir]
    rw [ite_eq_left (by rw [hiv]; have := i.isLt; omega)]
    congr 1
    apply Fin.ext
    simp only [hiv]
    omega
  have hwork : ∀ j : Fin (H.work + 1), R (compositionWork H G j.val) = 0 := by
    intro j
    have hj : j.val ≤ compositionPool H G := by
      have := j.isLt
      have hh : H.work ≤ compositionPool H G := le_max_left _ _
      omega
    have hjv := hw j.val hj
    have hni : ¬ (1 ≤ (compositionWork H G j.val).val ∧
      (compositionWork H G j.val).val ≤ n) := by omega
    have hnt : ¬ (n + 1 ≤ (compositionWork H G j.val).val ∧
      (compositionWork H G j.val).val < n + 1 + m) := by omega
    simp only [R, compositionBoundary, dite_eq_right hni, dite_eq_right hnt]
  have houter : ∀ U, Exec (compositionOuter H G) R U ↔
      ∃ b, b ∈ h a ∧ U = updateRegister R o b := by
    intro U
    exact placed_clean_exec H h hH o (compositionTemp H G)
      (fun j => compositionWork H G j.val) (composition_placements H G).2.1
      a R U hout hin hwork
  have hfinal : ∀ b,
      (List.ofFn (compositionTemp H G)).foldl (fun U p => updateRegister U p 0)
        (updateRegister R o b) = resultFile (m + compositionPool H G) x b := by
    intro b
    funext r
    simp only [rcf_fold_clear, rcf_temp_mem]
    by_cases hro : r = o
    · subst r
      simp [o, outputPort, resultFile, updateRegister]
    · have hrv : r.val ≠ 0 := by
        intro hv
        apply hro
        apply Fin.ext
        exact hv
      have hnot : r ≠ outputPort n (m + compositionPool H G) := hro
      simp only [resultFile, updateRegister, Function.update_of_ne hro, Function.update_of_ne hnot]
      by_cases hri : 1 ≤ r.val ∧ r.val ≤ n
      · have htemp : ¬ (n + 1 ≤ r.val ∧ r.val < n + 1 + m) := by omega
        simp [R, compositionBoundary, initialFile, hri]
      · by_cases hrt : n + 1 ≤ r.val ∧ r.val < n + 1 + m
        · have hbase : ¬ (1 ≤ r.val ∧ r.val ≤ n) := hri
          simp [hrt, initialFile, hbase]
        · rw [ite_eq_right hrt]
          change compositionBoundary H G x a m r = initialFile (m + compositionPool H G) x r
          rw [compositionBoundary, dite_eq_right hri, dite_eq_right hrt, initialFile, dite_eq_right hri]
  change Exec (sequence (compositionWork H G 0)
    (compositionOuter H G :: List.ofFn (fun i => clearFragment (compositionTemp H G i)))) R S ↔ _
  rw [sequence, seq_exec]
  simp only [houter]
  have hlist : List.ofFn (fun i => clearFragment (compositionTemp H G i)) =
      (List.ofFn (compositionTemp H G)).map clearFragment := by simp only [List.map_ofFn, Function.comp_def]
  rw [hlist]
  simp only [rcf_clear_sequence]
  constructor
  · rintro ⟨U, ⟨b, hb, rfl⟩, hS⟩
    exact ⟨b, hb, hS.trans (hfinal b)⟩
  · rintro ⟨b, hb, hS⟩
    exact ⟨updateRegister R o b, ⟨b, hb, rfl⟩, hS.trans (hfinal b).symm⟩


set_option backward.isDefEq.respectTransparency false in
theorem composition_clean {m n : ℕ} (H : Routine m) (G : Fin m → Routine n)
    (h : PFunction m) (g : Fin m → PFunction n) (hH : Clean H h) (hG : ∀ i, Clean (G i) (g i)) :
    Clean (compositionRoutine H G) (strictComp h g) := by
  dsimp only [Clean,compositionRoutine]
  constructor
  · apply seq_no_internal_halt
    · apply sequence_no_internal_halt
      intro B hB
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hB
      subst B
      exact rename_no_internal_halt _ (G i).body (hG i).1
    · apply sequence_no_internal_halt
      intro B hB
      rcases List.mem_cons.mp hB with he | hrest
      · subst B
        exact rename_no_internal_halt _ H.body hH.1
      · obtain ⟨i,hi⟩ := List.mem_ofFn.mp hrest
        subst B
        exact (elementary_no_internal_halt (compositionTemp H G i) (compositionTemp H G i)
          (compositionTemp H G i)).2.2.2.1
  · intro x S
    have htake : (compositionCalls H G).take m=compositionCalls H G := by
      apply List.take_of_length_le
      simp [compositionCalls]
    have hp (R) := composition_prefix H G g hG x m le_rfl R
    simp only [htake] at hp
    rw [seq_exec]
    constructor
    · rintro ⟨U,hU,hfinish⟩
      obtain ⟨a,ha,rfl⟩ := (hp U).mp hU
      obtain ⟨b,hb,hS⟩ := (composition_finish H G h hH x a S).mp hfinish
      exact ⟨b,(strictComp_spec h g x b).mpr ⟨a,fun i => ha i i.isLt,hb⟩,hS⟩
    · rintro ⟨b,hb,hS⟩
      obtain ⟨a,ha,houter⟩ := (strictComp_spec h g x b).mp hb
      exact ⟨compositionBoundary H G x a m,
        (hp _).mpr ⟨a,fun i _ => ha i,rfl⟩,
        (composition_finish H G h hH x a S).mpr ⟨b,houter,hS⟩⟩

theorem recursion_placements {n : ℕ} (G : Routine n) (H : Routine (n + 2)) :
    Function.Injective (placementMap (outputPort (n + 1) (4 + recursionPool G H))
      (fun i : Fin n => recursionPort G H (i.val + 1))
      (fun j : Fin (G.work + 1) => recursionWork G H j.val)) ∧
    Function.Injective (placementMap (recursionV G H) (recursionStepInputs G H)
      (fun j : Fin (H.work + 1) => recursionWork G H j.val)) ∧
    (recursionD G H).val = n + 2 ∧ (recursionJ G H).val = n + 3 ∧
    (recursionV G H).val = n + 4 ∧ (recursionCopyScratch G H).val = n + 5 ∧
    ∀ j, j ≤ recursionPool G H → (recursionWork G H j).val = n + 6 + j := by
  have hp : ∀ v, v < (n + 1) + 2 + (4 + recursionPool G H) →
      (recursionPort G H v).val = v := by
    intro v hv
    exact Nat.mod_eq_of_lt hv
  have hd : (recursionD G H).val = n + 2 := hp _ (by omega)
  have hj : (recursionJ G H).val = n + 3 := hp _ (by omega)
  have hv : (recursionV G H).val = n + 4 := hp _ (by omega)
  have hc : (recursionCopyScratch G H).val = n + 5 := hp _ (by omega)
  have hw : ∀ j, j ≤ recursionPool G H → (recursionWork G H j).val = n + 6 + j := by
    intro j h
    exact hp _ (by omega)
  have hgi : G.work ≤ recursionPool G H := le_max_left _ _
  have hhi : H.work ≤ recursionPool G H := le_max_right _ _
  have hwg : ∀ j : Fin (G.work + 1), (recursionWork G H j.val).val = n + 6 + j.val := by
    intro j
    exact hw _ (by have := j.isLt; omega)
  have hwh : ∀ j : Fin (H.work + 1), (recursionWork G H j.val).val = n + 6 + j.val := by
    intro j
    exact hw _ (by have := j.isLt; omega)
  have hinput : ∀ i : Fin n, (recursionPort G H (i.val + 1)).val = i.val + 1 := by
    intro i
    exact hp _ (by have := i.isLt; omega)
  have hstep : ∀ i : Fin (n + 2), (recursionStepInputs G H i).val =
      if i.val < n then i.val + 1 else if i.val = n then n + 3 else 0 := by
    intro i
    unfold recursionStepInputs
    split_ifs
    · exact hp _ (by have := i.isLt; omega)
    · exact hj
    · rfl
  refine ⟨?_, ?_, hd, hj, hv, hc, hw⟩
  · apply placement_injective
    · intro a b h
      apply Fin.ext
      have hval := congrArg Fin.val h
      simpa only [hinput, Nat.add_right_cancel_iff] using hval
    · intro a b h
      apply Fin.ext
      have hval := congrArg Fin.val h
      simpa only [hwg, Nat.add_left_cancel_iff] using hval
    · rintro ⟨a, h⟩
      have hval := congrArg Fin.val h
      rw [hinput] at hval
      change a.val + 1 = 0 at hval
      omega
    · rintro ⟨a, h⟩
      have hval := congrArg Fin.val h
      rw [hwg] at hval
      change n + 6 + a.val = 0 at hval
      omega
    · apply Set.disjoint_left.mpr
      rintro a ⟨b, rfl⟩ ⟨c, h⟩
      have hval := congrArg Fin.val h
      rw [hwg, hinput] at hval
      have := b.isLt
      omega
  · apply placement_injective
    · intro a b h
      apply Fin.ext
      have hval := congrArg Fin.val h
      simp only [hstep] at hval
      have ha := a.isLt
      have hb := b.isLt
      split_ifs at hval <;> omega
    · intro a b h
      apply Fin.ext
      have hval := congrArg Fin.val h
      simpa only [hwh, Nat.add_left_cancel_iff] using hval
    · rintro ⟨a, h⟩
      have hval := congrArg Fin.val h
      simp only [hstep, hv] at hval
      split_ifs at hval <;> omega
    · rintro ⟨a, h⟩
      have hval := congrArg Fin.val h
      rw [hwh, hv] at hval
      omega
    · apply Set.disjoint_left.mpr
      rintro a ⟨b, rfl⟩ ⟨c, h⟩
      have hval := congrArg Fin.val h
      simp only [hwh, hstep] at hval
      split_ifs at hval <;> omega

private theorem pr_d_val {n : ℕ} (G : Routine n) (H : Routine (n+2)) :
    (recursionD G H).val=n+2 := (recursion_placements G H).2.2.1
private theorem pr_j_val {n : ℕ} (G : Routine n) (H : Routine (n+2)) :
    (recursionJ G H).val=n+3 := (recursion_placements G H).2.2.2.1
private theorem pr_v_val {n : ℕ} (G : Routine n) (H : Routine (n+2)) :
    (recursionV G H).val=n+4 := (recursion_placements G H).2.2.2.2.1
private theorem pr_s_val {n : ℕ} (G : Routine n) (H : Routine (n+2)) :
    (recursionCopyScratch G H).val=n+5 := (recursion_placements G H).2.2.2.2.2.1
private theorem pr_w_val {n : ℕ} (G : Routine n) (H : Routine (n+2)) (t : ℕ)
    (ht : t≤recursionPool G H) :
    (recursionWork G H t).val=n+6+t := (recursion_placements G H).2.2.2.2.2.2 t ht
private theorem pr_initial_above {n : ℕ} (w : ℕ) (x : Args n) (r : Fin (n+2+w))
    (hr : n<r.val) : initialFile w x r=0 := by
  rw [initialFile,dite_eq_right (by omega)]
private theorem pr_input_eq {n : ℕ} (G : Routine n) (H : Routine (n+2)) (i : Fin n) :
    recursionPort G H (i.val+1)=inputPort (n+1) (4+recursionPool G H) i.castSucc := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
private theorem pr_input_initial {n : ℕ} (G : Routine n) (H : Routine (n+2))
    (x : Args n) (N : ℕ) (i : Fin n) :
    initialFile (4+recursionPool G H) (snoc x N) (recursionPort G H (i.val+1))=x.get i := by
  rw [pr_input_eq,(canonical_ports _ (snoc x N) 0).1]
  simp
private theorem pr_initial_copy {n : ℕ} (G : Routine n) (H : Routine (n+2))
    (x : Args n) (N : ℕ) (S : Registers ((n+1)+2+(4+recursionPool G H))) :
    Exec (copyFragment (inputPort (n+1) (4+recursionPool G H) (Fin.last n))
      (recursionD G H) (recursionCopyScratch G H)) (initialFile _ (snoc x N)) S ↔
      S=updateRegister (initialFile _ (snoc x N)) (recursionD G H) N := by
  have hxd : inputPort (n+1) (4+recursionPool G H) (Fin.last n)≠recursionD G H := by
    intro he;have hv := congrArg Fin.val he
    simp only [inputPort,Fin.val_last,pr_d_val] at hv
    omega
  have hxs : inputPort (n+1) (4+recursionPool G H) (Fin.last n)≠recursionCopyScratch G H := by
    intro he;have hv := congrArg Fin.val he
    simp only [inputPort,Fin.val_last,pr_s_val] at hv
    omega
  have hds : recursionD G H≠recursionCopyScratch G H := by
    intro he;have hv := congrArg Fin.val he
    rw [pr_d_val,pr_s_val] at hv
    omega
  have hd := pr_initial_above _ (snoc x N) (recursionD G H) (by rw [pr_d_val];omega)
  have hs := pr_initial_above _ (snoc x N) (recursionCopyScratch G H) (by rw [pr_s_val];omega)
  simpa only [(canonical_ports _ (snoc x N) 0).1,get_snoc_last] using
    copy_exec_eq _ _ _ hxd hxs hds (initialFile _ (snoc x N)) hd hs S

private theorem pr_boundary_out {n : ℕ} (G : Routine n) (H : Routine (n+2))
    (x : Args n) (N j a : ℕ) :
    recursionBoundary G H x N j a (outputPort (n+1) (4+recursionPool G H))=a := by
  simp [recursionBoundary,resultFile,updateRegister,Fin.ext_iff,pr_d_val,pr_j_val,outputPort]
private theorem pr_boundary_d {n : ℕ} (G : Routine n) (H : Routine (n+2))
    (x : Args n) (N j a : ℕ) : recursionBoundary G H x N j a (recursionD G H)=N-j := by
  simp [recursionBoundary,updateRegister,Fin.ext_iff,pr_d_val,pr_j_val]
private theorem pr_boundary_j {n : ℕ} (G : Routine n) (H : Routine (n+2))
    (x : Args n) (N j a : ℕ) : recursionBoundary G H x N j a (recursionJ G H)=j := by
  simp [recursionBoundary,updateRegister]
private theorem pr_boundary_external {n : ℕ} (G : Routine n) (H : Routine (n+2))
    (x : Args n) (N j a : ℕ) (r : Fin ((n+1)+2+(4+recursionPool G H)))
    (hd : r.val≠n+2) (hj : r.val≠n+3) (ho : r.val≠0) :
    recursionBoundary G H x N j a r=initialFile (4+recursionPool G H) (snoc x N) r := by
  simp [recursionBoundary,resultFile,updateRegister,Fin.ext_iff,pr_d_val,pr_j_val,outputPort,hd,hj,ho]
private theorem pr_boundary_above {n : ℕ} (G : Routine n) (H : Routine (n+2))
    (x : Args n) (N j a : ℕ) (r : Fin ((n+1)+2+(4+recursionPool G H)))
    (hr : n+4≤r.val) : recursionBoundary G H x N j a r=0 := by
  rw [pr_boundary_external G H x N j a r (by omega) (by omega) (by omega)]
  exact pr_initial_above _ _ _ (by omega)
private theorem pr_boundary_input {n : ℕ} (G : Routine n) (H : Routine (n+2))
    (x : Args n) (N j a : ℕ) (i : Fin n) :
    recursionBoundary G H x N j a (recursionPort G H (i.val+1))=x.get i := by
  have hi : (recursionPort G H (i.val+1)).val=i.val+1 := by
    rw [pr_input_eq]
    rfl
  rw [pr_boundary_external G H x N j a _ (by rw [hi];have := i.isLt;omega)
    (by rw [hi];have := i.isLt;omega) (by rw [hi];omega)]
  exact pr_input_initial G H x N i

theorem recursion_initial_exec {n : ℕ} (G : Routine n) (H : Routine (n + 2))
    (g : PFunction n) (hG : Clean G g) (x : Args n) (N : ℕ)
    (S : Registers ((n + 1) + 2 + (4 + recursionPool G H))) :
    Exec (recursionInit G H) (initialFile _ (snoc x N)) S ↔
      ∃ a, a ∈ g x ∧ S = recursionBoundary G H x N 0 a := by
  let U := updateRegister (initialFile (4+recursionPool G H) (snoc x N)) (recursionD G H) N
  have hdo : recursionD G H≠outputPort (n+1) (4+recursionPool G H) := by
    intro he;have hv := congrArg Fin.val he
    rw [pr_d_val] at hv
    dsimp [outputPort] at hv
    omega
  have hjo : recursionJ G H≠outputPort (n+1) (4+recursionPool G H) := by
    intro he;have hv := congrArg Fin.val he
    rw [pr_j_val] at hv
    dsimp [outputPort] at hv
    omega
  have hjd : recursionJ G H≠recursionD G H := by
    intro he;have hv := congrArg Fin.val he
    rw [pr_j_val,pr_d_val] at hv
    omega
  have hout : U (outputPort (n+1) (4+recursionPool G H))=0 := by
    simp only [U,updateRegister,Function.update_of_ne hdo.symm]
    exact (canonical_ports _ (snoc x N) 0).2.1
  have hin : ∀ i : Fin n, U (recursionPort G H (i.val+1))=x.get i := by
    intro i
    have hn : recursionPort G H (i.val+1)≠recursionD G H := by
      intro he;have hv := congrArg Fin.val he
      rw [pr_input_eq,pr_d_val] at hv
      dsimp [inputPort] at hv
      have := i.isLt
      omega
    simpa only [U,updateRegister,Function.update_of_ne hn] using pr_input_initial G H x N i
  have hw : ∀ t : Fin (G.work+1), U (recursionWork G H t.val)=0 := by
    intro t
    have ht : t.val≤recursionPool G H := by
      have := t.isLt
      have := le_max_left G.work H.work
      dsimp [recursionPool]
      omega
    have hn : recursionWork G H t.val≠recursionD G H := by
      intro he;have hv := congrArg Fin.val he
      rw [pr_w_val G H _ ht,pr_d_val] at hv
      omega
    simp only [U,updateRegister,Function.update_of_ne hn]
    exact pr_initial_above _ (snoc x N) _ (by rw [pr_w_val G H _ ht];omega)
  have heq (a : ℕ) : updateRegister U (outputPort (n+1) (4+recursionPool G H)) a=
      recursionBoundary G H x N 0 a := by
    have hiJ := pr_initial_above _ (snoc x N) (recursionJ G H) (by rw [pr_j_val];omega)
    funext r
    by_cases hrj : r=recursionJ G H
    · subst r
      simp [U,recursionBoundary,resultFile,updateRegister,hjd,hjo,hiJ]
    · by_cases hrd : r=recursionD G H
      · subst r
        simp [U,recursionBoundary,resultFile,updateRegister,hrj,hdo]
      · by_cases hro : r=outputPort (n+1) (4+recursionPool G H)
        · subst r
          simp [U,recursionBoundary,resultFile,updateRegister,hrj,hrd]
        · simp [U,recursionBoundary,resultFile,updateRegister,hrj,hrd,hro]
  unfold recursionInit
  rw [seq_exec]
  simp only [pr_initial_copy,exists_eq_left]
  change Exec (place G (outputPort (n+1) (4+recursionPool G H))
    (fun i => recursionPort G H (i.val+1)) (fun t => recursionWork G H t.val)) U S ↔ _
  rw [placed_clean_exec G g hG _ _ _ (recursion_placements G H).1 x U S hout hin hw]
  simp only [heq]

theorem recursion_body_exec {n : ℕ} (G : Routine n) (H : Routine (n + 2))
    (h : PFunction (n + 2)) (hH : Clean H h) (x : Args n) (N j a : ℕ) (hj : j < N)
    (S : Registers ((n + 1) + 2 + (4 + recursionPool G H))) :
    Exec (recursionBody G H)
      (updateRegister (recursionBoundary G H x N j a) (recursionD G H) (N - j - 1)) S ↔
      ∃ b, b ∈ h (snoc (snoc x j) a) ∧ S = recursionBoundary G H x N (j + 1) b := by
  have hpositive := Nat.sub_pos_of_lt hj
  let U := updateRegister (recursionBoundary G H x N j a) (recursionD G H) (N-j-1)
  have hu (r : Fin ((n+1)+2+(4+recursionPool G H))) (hr : r.val≠n+2) :
      U r=recursionBoundary G H x N j a r := by
    simp [U,updateRegister,Fin.ext_iff,pr_d_val,hr]
  have hout : U (recursionV G H)=0 := by
    rw [hu _ (by rw [pr_v_val];omega)]
    exact pr_boundary_above G H x N j a _ (by rw [pr_v_val])
  have hin : ∀ i : Fin (n+2), U (recursionStepInputs G H i)=(snoc (snoc x j) a).get i := by
    intro i
    refine Fin.lastCases ?_ (fun i => Fin.lastCases ?_ (fun t => ?_) i) i
    · have he : recursionStepInputs G H (Fin.last (n+1))=outputPort (n+1) (4+recursionPool G H) := by
        simp [recursionStepInputs]
      rw [he,hu _ (by dsimp [outputPort];omega),pr_boundary_out]
      simp
    · have he : recursionStepInputs G H (Fin.last n).castSucc=recursionJ G H := by
        simp [recursionStepInputs]
      rw [he,hu _ (by rw [pr_j_val];omega),pr_boundary_j]
      simp
    · have he : recursionStepInputs G H t.castSucc.castSucc=recursionPort G H (t.val+1) := by
        simp [recursionStepInputs,t.isLt]
      rw [he,hu _ (by rw [pr_input_eq];dsimp [inputPort];have := t.isLt;omega),pr_boundary_input]
      simp
  have hw : ∀ t : Fin (H.work+1), U (recursionWork G H t.val)=0 := by
    intro t
    have ht : t.val≤recursionPool G H := by
      have := t.isLt
      have := le_max_right G.work H.work
      dsimp [recursionPool]
      omega
    rw [hu _ (by rw [pr_w_val G H _ ht];omega)]
    exact pr_boundary_above G H x N j a _ (by rw [pr_w_val G H _ ht];omega)
  have hvo : recursionV G H≠outputPort (n+1) (4+recursionPool G H) := by
    intro he;have hv := congrArg Fin.val he
    rw [pr_v_val] at hv
    dsimp [outputPort] at hv
    omega
  let T (b : ℕ) := updateRegister U (recursionV G H) b
  let C (b : ℕ) := updateRegister (T b) (outputPort (n+1) (4+recursionPool G H)) 0
  let V (b : ℕ) := updateRegister (updateRegister (C b) (recursionV G H) 0)
    (outputPort (n+1) (4+recursionPool G H))
      (C b (outputPort (n+1) (4+recursionPool G H))+C b (recursionV G H))
  have hc0 (b : ℕ) : C b (outputPort (n+1) (4+recursionPool G H))=0 := by simp [C,updateRegister]
  have hcv (b : ℕ) : C b (recursionV G H)=b := by simp [C,T,updateRegister,hvo]
  have hvj (b : ℕ) : V b (recursionJ G H)=j := by
    simp [V,C,T,U,updateRegister,Fin.ext_iff,pr_j_val,pr_v_val,pr_d_val,outputPort,pr_boundary_j]
  have heq (b : ℕ) : updateRegister (V b) (recursionJ G H) (V b (recursionJ G H)+1)=
      recursionBoundary G H x N (j+1) b := by
    rw [hvj]
    have hiV := pr_initial_above _ (snoc x N) (recursionV G H) (by rw [pr_v_val];omega)
    funext r
    by_cases hrj : r=recursionJ G H
    · subst r
      simp [recursionBoundary,updateRegister]
    · by_cases hrd : r=recursionD G H
      · subst r
        simp [V,C,T,U,recursionBoundary,resultFile,updateRegister,hrj,Fin.ext_iff,
          pr_d_val,pr_v_val,outputPort,Nat.sub_sub]
      · by_cases hro : r=outputPort (n+1) (4+recursionPool G H)
        · subst r
          simp [V,C,T,U,recursionBoundary,resultFile,updateRegister,hrj,hrd,hvo]
        · by_cases hrv : r=recursionV G H
          · subst r
            simp [V,C,T,U,recursionBoundary,resultFile,updateRegister,hrj,hrd,hro,hiV]
          · simp [V,C,T,U,recursionBoundary,resultFile,updateRegister,hrj,hrd,hro,hrv]
  have hd (R S : Registers ((n+1)+2+(4+recursionPool G H))) :
      Exec (doneFragment _) R S ↔ S=R := exec_iff_eq (doneFragment _) R R .refl S
  have hs (R : Registers ((n+1)+2+(4+recursionPool G H))) :
      Exec (recursionStep G H) U R ↔ ∃ b, b ∈ h (snoc (snoc x j) a) ∧ R=T b :=
    placed_clean_exec H h hH _ _ _ (recursion_placements G H).2.1 (snoc (snoc x j) a) U R hout hin hw
  unfold recursionBody
  change Exec (sequence (recursionWork G H 0) _) U S ↔ _
  simp only [sequence,seq_exec,hd,hs,clear_exec_eq,transfer_exec_eq _ _ hvo,increment_exec_eq]
  constructor
  · rintro ⟨_,⟨b,hb,rfl⟩,_,rfl,_,rfl,_,rfl,rfl⟩
    exact ⟨b,hb,heq b⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨T b,⟨b,hb,rfl⟩,C b,rfl,V b,rfl,_,rfl,(heq b).symm⟩

private theorem pr_finish {n : ℕ} (G : Routine n) (H : Routine (n+2))
    (x : Args n) (N b : ℕ) :
    updateRegister (recursionBoundary G H x N N b) (recursionJ G H) 0=
      resultFile (4+recursionPool G H) (snoc x N) b := by
  have hiD := pr_initial_above _ (snoc x N) (recursionD G H) (by rw [pr_d_val];omega)
  have hiJ := pr_initial_above _ (snoc x N) (recursionJ G H) (by rw [pr_j_val];omega)
  funext r
  by_cases hrj : r=recursionJ G H
  · subst r
    simp [recursionBoundary,resultFile,updateRegister,Fin.ext_iff,pr_j_val,outputPort,hiJ]
  · by_cases hrd : r=recursionD G H
    · subst r
      simp [recursionBoundary,resultFile,updateRegister,hrj,Fin.ext_iff,pr_d_val,outputPort,hiD]
    · simp [recursionBoundary,resultFile,updateRegister,hrj,hrd]

private theorem pr_repeat_sound {n : ℕ} (G : Routine n) (H : Routine (n+2))
    (g : PFunction n) (h : PFunction (n+2)) (hH : Clean H h) (x : Args n) (N : ℕ)
    {R S : Registers ((n+1)+2+(4+recursionPool G H))}
    (hr : RepeatReturns (recursionD G H) (recursionBody G H) R S) :
    ∀ j a, R=recursionBoundary G H x N j a → j≤N → a ∈ recValue g h x j →
      ∃ b, b ∈ recValue g h x N ∧ S=recursionBoundary G H x N N b := by
  induction hr with
  | zero R hz =>
      intro j a he hj ha
      subst R
      rw [pr_boundary_d] at hz
      have he : j=N := by omega
      subst j
      exact ⟨a,ha,rfl⟩
  | @positive R U S hp hbody hrest ih =>
      intro j a he hj ha
      subst R
      rw [pr_boundary_d] at hp
      have hjlt : j<N := by omega
      obtain ⟨b,hb,he⟩ := (recursion_body_exec G H h hH x N j a hjlt U).mp
        (by simpa only [pr_boundary_d] using hbody)
      apply ih (j+1) b he (by omega)
      exact Part.mem_bind ha hb

private theorem pr_repeat_chain {n : ℕ} (G : Routine n) (H : Routine (n+2))
    (h : PFunction (n+2)) (hH : Clean H h) (x : Args n) (N : ℕ)
    (values : Fin (N+1) → ℕ)
    (hs : ∀ i : Fin N, values i.succ ∈ h (snoc (snoc x i.val) (values i.castSucc))) :
    RepeatReturns (recursionD G H) (recursionBody G H)
      (recursionBoundary G H x N 0 (values 0))
      (recursionBoundary G H x N N (values (Fin.last N))) := by
  have go : ∀ d j (he : j+d=N),
      RepeatReturns (recursionD G H) (recursionBody G H)
        (recursionBoundary G H x N j (values ⟨j,by omega⟩))
        (recursionBoundary G H x N N (values (Fin.last N))) := by
    intro d
    induction d with
    | zero =>
        intro j he
        have hj : j=N := by omega
        subst j
        exact .zero _ (by simp [pr_boundary_d])
    | succ d ih =>
        intro j he
        have hj : j<N := by omega
        refine .positive (U := recursionBoundary G H x N (j+1) (values ⟨j+1,by omega⟩))
          (by rw [pr_boundary_d];omega) ?_ (ih (j+1) (by omega))
        rw [pr_boundary_d]
        apply (recursion_body_exec G H h hH x N j _ hj _).mpr
        exact ⟨_,hs ⟨j,hj⟩,rfl⟩
  exact go N 0 (by omega)

theorem primitive_recursion_clean {n : ℕ} (G : Routine n) (H : Routine (n + 2))
    (g : PFunction n) (h : PFunction (n + 2)) (hG : Clean G g) (hH : Clean H h) :
    Clean (primitiveRecursionRoutine G H) (partialRec g h) := by
  have hb : NoInternalHalt (recursionBody G H) := by
    change NoInternalHalt (sequence (recursionWork G H 0)
      [recursionStep G H,clearFragment (outputPort (n+1) (4+recursionPool G H)),
       transferFragment (recursionV G H) (outputPort (n+1) (4+recursionPool G H)),incrementFragment (recursionJ G H)])
    apply sequence_no_internal_halt
    intro B hB
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hB
    rcases hB with rfl | rfl | rfl | rfl
    · exact rename_no_internal_halt _ H.body hH.1
    · exact (elementary_no_internal_halt _ (outputPort (n+1) (4+recursionPool G H)) (recursionWork G H 0)).2.2.2.1
    · exact (elementary_no_internal_halt (recursionV G H) (outputPort (n+1) (4+recursionPool G H)) (recursionWork G H 0)).2.2.2.2.1
    · exact (elementary_no_internal_halt (recursionJ G H) (recursionJ G H) (recursionJ G H)).2.1
  have hi : NoInternalHalt (recursionInit G H) := by
    change NoInternalHalt (seqFragment (recursionWork G H 0)
      (copyFragment (inputPort (n+1) (4+recursionPool G H) (Fin.last n)) (recursionD G H) (recursionCopyScratch G H))
      (recursionBase G H))
    apply seq_no_internal_halt
    · exact (elementary_no_internal_halt _ _ _).2.2.2.2.2
    · exact rename_no_internal_halt _ G.body hG.1
  have hc : NoInternalHalt (clearFragment (recursionJ G H)) :=
    (elementary_no_internal_halt (recursionJ G H) (recursionJ G H) (recursionJ G H)).2.2.2.1
  have hn : NoInternalHalt (primitiveRecursionRoutine G H).body := by
    change NoInternalHalt (sequence (recursionWork G H 0)
      [recursionInit G H,repeatFragment (recursionD G H) (recursionWork G H 0) (recursionBody G H),clearFragment (recursionJ G H)])
    apply sequence_no_internal_halt
    intro B hB
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hB
    rcases hB with rfl | rfl | rfl
    · exact hi
    · exact repeat_no_internal_halt _ _ _ hb
    · exact hc
  refine ⟨hn,?_⟩
  have he (x : Args n) (N : ℕ) (S : Registers ((n+1)+2+(4+recursionPool G H))) :
      Exec (primitiveRecursionRoutine G H).body (initialFile _ (snoc x N)) S ↔
        ∃ b, b ∈ partialRec g h (snoc x N) ∧ S=resultFile _ (snoc x N) b := by
    have hd (R T : Registers ((n+1)+2+(4+recursionPool G H))) :
        Exec (doneFragment _) R T ↔ T=R := exec_iff_eq (doneFragment _) R R .refl T
    have hinit (R : Registers ((n+1)+2+(4+recursionPool G H))) := recursion_initial_exec G H g hG x N R
    change Exec (sequence (recursionWork G H 0)
      [recursionInit G H,repeatFragment (recursionD G H) (recursionWork G H 0) (recursionBody G H),clearFragment (recursionJ G H)])
      (initialFile (4+recursionPool G H) (snoc x N)) S ↔ _
    simp only [sequence,seq_exec,hd,hinit,repeat_exec,clear_exec_eq]
    constructor
    · rintro ⟨_,⟨a,ha,rfl⟩,T,hrep,_,rfl,rfl⟩
      obtain ⟨b,hb,rfl⟩ := pr_repeat_sound G H g h hH x N hrep 0 a rfl (by omega) ha
      exact ⟨b,by simpa only [partialRec_snoc] using hb,pr_finish G H x N b⟩
    · rintro ⟨b,hb,rfl⟩
      obtain ⟨values,h0,hb,hs⟩ := (recursion_chain_iff g h x N b).mp hb
      have hrep := pr_repeat_chain G H h hH x N values hs
      rw [hb] at hrep
      exact ⟨_,⟨values 0,h0,rfl⟩,_,hrep,_,rfl,(pr_finish G H x N b).symm⟩
  intro v S
  change Exec (primitiveRecursionRoutine G H).body (initialFile (4+recursionPool G H) v) S ↔
    ∃ b, b ∈ partialRec g h v ∧ S=resultFile (4+recursionPool G H) v b
  simpa only [primitiveRecursionRoutine,snoc_init_last] using he (init v) (last v) S

theorem recursion_zero_exec {n : ℕ} (G : Routine n) (H : Routine (n + 2))
    (g : PFunction n) (h : PFunction (n + 2)) (hG : Clean G g) (hH : Clean H h)
    (x : Args n) (S : Registers ((n + 1) + 2 + (4 + recursionPool G H))) :
    Exec (primitiveRecursionRoutine G H).body (initialFile _ (snoc x 0)) S ↔
      ∃ a, a ∈ g x ∧ S = resultFile _ (snoc x 0) a := by
  simpa only [(recursion_equations g h x 0).1,primitiveRecursionRoutine] using
    (primitive_recursion_clean G H g h hG hH).2 (snoc x 0) S

theorem minimization_placement {n : ℕ} (F : Routine (n + 1)) :
    Function.Injective (placementMap (minimizationV F) (minimizationInputs F)
      (fun j : Fin (F.work + 1) => minimizationWork F j.val)) ∧
    (minimizationJ F).val = n + 1 ∧ (minimizationV F).val = n + 2 ∧
    (minimizationCopyScratch F).val = n + 3 ∧
    ∀ j, j ≤ F.work → (minimizationWork F j).val = n + 4 + j := by
  have hp : ∀ v, v < n + 2 + (3 + F.work) → (minimizationPort F v).val = v := by
    intro v hv
    exact Nat.mod_eq_of_lt hv
  have hj : (minimizationJ F).val = n + 1 := hp _ (by omega)
  have hv : (minimizationV F).val = n + 2 := hp _ (by omega)
  have hc : (minimizationCopyScratch F).val = n + 3 := hp _ (by omega)
  have hw : ∀ j, j ≤ F.work → (minimizationWork F j).val = n + 4 + j := by
    intro j h
    exact hp _ (by omega)
  have hwi : ∀ j : Fin (F.work + 1), (minimizationWork F j.val).val = n + 4 + j.val := by
    intro j
    exact hw _ (by have := j.isLt; omega)
  have hin : ∀ i : Fin (n + 1), (minimizationInputs F i).val =
      if i.val < n then i.val + 1 else n + 1 := by
    intro i
    unfold minimizationInputs
    split_ifs
    · exact hp _ (by have := i.isLt; omega)
    · exact hj
  refine ⟨?_, hj, hv, hc, hw⟩
  apply placement_injective
  · intro a b h
    apply Fin.ext
    have hval := congrArg Fin.val h
    simp only [hin] at hval
    have ha := a.isLt
    have hb := b.isLt
    split_ifs at hval <;> omega
  · intro a b h
    apply Fin.ext
    have hval := congrArg Fin.val h
    simpa only [hwi, Nat.add_left_cancel_iff] using hval
  · rintro ⟨a, h⟩
    have hval := congrArg Fin.val h
    simp only [hin, hv] at hval
    split_ifs at hval <;> omega
  · rintro ⟨a, h⟩
    have hval := congrArg Fin.val h
    rw [hwi, hv] at hval
    omega
  · apply Set.disjoint_left.mpr
    rintro a ⟨b, rfl⟩ ⟨c, h⟩
    have hval := congrArg Fin.val h
    simp only [hwi, hin] at hval
    split_ifs at hval <;> omega


private theorem initial_above {n : ℕ} (w : ℕ) (x : Args n) (r : Fin (n+2+w))
    (hr : n<r.val) : initialFile w x r=0 := by
  simp [initialFile,not_le.mpr hr]

private theorem min_j_val {n : ℕ} (F : Routine (n+1)) :
    (minimizationJ F).val=n+1 := (minimization_placement F).2.1
private theorem min_v_val {n : ℕ} (F : Routine (n+1)) :
    (minimizationV F).val=n+2 := (minimization_placement F).2.2.1
private theorem min_s_val {n : ℕ} (F : Routine (n+1)) :
    (minimizationCopyScratch F).val=n+3 := (minimization_placement F).2.2.2.1
private theorem min_w_val {n : ℕ} (F : Routine (n+1)) (t : ℕ) (ht : t≤F.work) :
    (minimizationWork F t).val=n+4+t := (minimization_placement F).2.2.2.2 t ht

private theorem min_ne_j {n : ℕ} (F : Routine (n+1)) (r : Fin (n+2+(3+F.work)))
    (hr : r.val≠n+1) : r≠minimizationJ F := by
  intro h
  exact hr ((congrArg Fin.val h).trans (min_j_val F))

private theorem min_boundary_at_j {n : ℕ} (F : Routine (n+1)) (x : Args n) (j : ℕ) :
    minimizationBoundary F x j (minimizationJ F)=j := by
  simp [minimizationBoundary,updateRegister]

private theorem min_boundary_at_v {n : ℕ} (F : Routine (n+1)) (x : Args n) (j : ℕ) :
    minimizationBoundary F x j (minimizationV F)=0 := by
  have hn := min_ne_j F (minimizationV F) (by rw [min_v_val];omega)
  simp only [minimizationBoundary,updateRegister,Function.update_of_ne hn]
  exact initial_above _ x _ (by rw [min_v_val];omega)

private theorem min_boundary_at_s {n : ℕ} (F : Routine (n+1)) (x : Args n) (j : ℕ) :
    minimizationBoundary F x j (minimizationCopyScratch F)=0 := by
  have hn := min_ne_j F (minimizationCopyScratch F) (by rw [min_s_val];omega)
  simp only [minimizationBoundary,updateRegister,Function.update_of_ne hn]
  exact initial_above _ x _ (by rw [min_s_val];omega)

private theorem min_boundary_at_out {n : ℕ} (F : Routine (n+1)) (x : Args n) (j : ℕ) :
    minimizationBoundary F x j (outputPort n (3+F.work))=0 := by
  have hn := min_ne_j F (outputPort n (3+F.work)) (by simp [outputPort])
  simp only [minimizationBoundary,updateRegister,Function.update_of_ne hn]
  exact (canonical_ports _ x 0).2.1

private theorem min_boundary_at_work {n : ℕ} (F : Routine (n+1)) (x : Args n) (j t : ℕ)
    (ht : t≤F.work) : minimizationBoundary F x j (minimizationWork F t)=0 := by
  have hn := min_ne_j F (minimizationWork F t) (by rw [min_w_val F t ht];omega)
  simp only [minimizationBoundary,updateRegister,Function.update_of_ne hn]
  exact initial_above _ x _ (by rw [min_w_val F t ht];omega)

private theorem min_boundary_at_input {n : ℕ} (F : Routine (n+1)) (x : Args n) (j : ℕ) (i : Fin n) :
    minimizationBoundary F x j (inputPort n (3+F.work) i)=x.get i := by
  have hn := min_ne_j F (inputPort n (3+F.work) i) (by dsimp [inputPort];omega)
  simp only [minimizationBoundary,updateRegister,Function.update_of_ne hn]
  exact (canonical_ports _ x 0).1 i

private theorem min_test_inputs {n : ℕ} (F : Routine (n+1)) (x : Args n) (j : ℕ) (i : Fin (n+1)) :
    minimizationBoundary F x j (minimizationInputs F i)=(snoc x j).get i := by
  refine Fin.lastCases ?_ (fun t => ?_) i
  · simpa [minimizationInputs] using min_boundary_at_j F x j
  · have hp : minimizationInputs F t.castSucc=inputPort n (3+F.work) t := by
      apply Fin.ext
      simp [minimizationInputs,t.isLt,minimizationPort,port,inputPort,Nat.mod_eq_of_lt (by omega : t.val+1<n+2+(3+F.work))]
    simpa only [hp,get_snoc_castSucc] using min_boundary_at_input F x j t

private theorem min_update_zero {n : ℕ} (F : Routine (n+1)) (x : Args n) (j : ℕ) :
    updateRegister (minimizationBoundary F x j) (minimizationV F) 0=minimizationBoundary F x j := by
  funext r
  by_cases hr : r=minimizationV F
  · subst r;simp [updateRegister,min_boundary_at_v]
  · simp [updateRegister,hr]

private theorem min_increment_candidate {n : ℕ} (F : Routine (n+1)) (x : Args n) (j : ℕ) :
    updateRegister (minimizationBoundary F x j) (minimizationJ F)
      (minimizationBoundary F x j (minimizationJ F)+1)=minimizationBoundary F x (j+1) := by
  simp [minimizationBoundary,updateRegister]

theorem minimization_test_exec {n : ℕ} (F : Routine (n + 1))
    (f : PFunction (n + 1)) (hF : Clean F f) (x : Args n) (j : ℕ)
    (S : Registers (n + 2 + (3 + F.work))) :
    Exec (minimizationTest F) (minimizationBoundary F x j) S ↔
      ∃ v, v ∈ f (snoc x j) ∧ S = updateRegister (minimizationBoundary F x j) (minimizationV F) v := by
  exact placed_clean_exec F f hF _ _ _ (minimization_placement F).1 (snoc x j) _ S
    (min_boundary_at_v F x j) (min_test_inputs F x j)
    (fun t => min_boundary_at_work F x j t.val (by omega))

theorem minimization_positive_exec {n : ℕ} (F : Routine (n + 1))
    (x : Args n) (j v : ℕ) (hv : 0 < v) (S : Registers (n + 2 + (3 + F.work))) :
    Exec (minimizationPositive F)
      (updateRegister (minimizationBoundary F x j) (minimizationV F) (v - 1)) S ↔
      S = minimizationBoundary F x (j + 1) := by
  by_cases hv0 : v=0
  · exact False.elim ((Nat.ne_of_gt hv) hv0)
  unfold minimizationPositive
  rw [seq_exec]
  simp only [clear_exec_eq]
  simp only [exists_eq_left]
  have he : updateRegister (updateRegister (minimizationBoundary F x j) (minimizationV F) (v-1))
      (minimizationV F) 0=minimizationBoundary F x j := by
    simpa [updateRegister] using min_update_zero F x j
  rw [he,increment_exec_eq,min_increment_candidate]

theorem minimization_zero_exec {n : ℕ} (F : Routine (n + 1))
    (x : Args n) (j : ℕ) (S : Registers (n + 2 + (3 + F.work))) :
    Exec (minimizationZero F) (minimizationBoundary F x j) S ↔ S = resultFile _ x j := by
  have hjo : minimizationJ F≠outputPort n (3+F.work) := by
    intro h;have hh := congrArg Fin.val h;rw [min_j_val] at hh;dsimp [outputPort] at hh;omega
  have hjs : minimizationJ F≠minimizationCopyScratch F := by
    intro h;have hh := congrArg Fin.val h;rw [min_j_val,min_s_val] at hh;omega
  have hos : outputPort n (3+F.work)≠minimizationCopyScratch F := by
    intro h;have hh := congrArg Fin.val h;rw [min_s_val] at hh;dsimp [outputPort] at hh;omega
  have hiJ : initialFile (3+F.work) x (minimizationJ F)=0 :=
    initial_above _ x _ (by rw [min_j_val F];omega)
  unfold minimizationZero
  rw [seq_exec]
  simp only [copy_exec_eq _ _ _ hjo hjs hos _ (min_boundary_at_out F x j) (min_boundary_at_s F x j),exists_eq_left]
  rw [clear_exec_eq]
  suffices he : updateRegister (updateRegister (minimizationBoundary F x j)
      (outputPort n (3+F.work)) j) (minimizationJ F) 0=resultFile (3+F.work) x j by
    simp only [min_boundary_at_j,he]
  funext r
  by_cases hrj : r=minimizationJ F
  · subst r
    simp [updateRegister,resultFile,minimizationBoundary,hjo,hiJ]
  · by_cases hro : r=outputPort n (3+F.work)
    · subst r;simp [updateRegister,resultFile,minimizationBoundary,hrj]
    · simp [updateRegister,resultFile,minimizationBoundary,hrj,hro]


private inductive MinChain {n : ℕ} (f : PFunction (n+1)) (x : Args n) : ℕ → ℕ → Prop
  | zero (j : ℕ) (hz : 0∈f (snoc x j)) : MinChain f x j j
  | positive {j t a : ℕ} (ha : 0<a) (hf : a∈f (snoc x j))
      (hrest : MinChain f x (j+1) t) : MinChain f x j t

private theorem min_chain_spec {n : ℕ} (f : PFunction (n+1)) (x : Args n) (j t : ℕ) :
    MinChain f x j t ↔ j≤t ∧ 0∈f (snoc x t) ∧
      ∀ i, j ≤ i → i < t → ∃ a, 0 < a ∧ a ∈ f (snoc x i) := by
  constructor
  · intro h
    induction h with
    | zero j hz => exact ⟨le_rfl,hz,by omega⟩
    | @positive j t a ha hf hrest ih =>
        refine ⟨by omega,ih.2.1,?_⟩
        intro i hji hit
        by_cases he : i=j
        · subst i;exact ⟨a,ha,hf⟩
        · exact ih.2.2 i (by omega) hit
  · rintro ⟨hjt,hzero,hbefore⟩
    have build : ∀ d j,0∈f (snoc x (j+d)) →
        (∀ i, j ≤ i → i < j+d → ∃ a, 0 < a ∧ a ∈ f (snoc x i)) → MinChain f x j (j+d) := by
      intro d
      induction d with
      | zero => intro j hz _;exact .zero j hz
      | succ d ih =>
          intro j hz hb
          obtain ⟨a,ha,hf⟩ := hb j le_rfl (by omega)
          have hs := ih (j+1) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hz)
            (by intro i hi hit;exact hb i (by omega) (by omega))
          exact .positive ha hf (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs)
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hjt
    exact build d j hzero hbefore

private theorem min_search_forward {n : ℕ} (F : Routine (n+1)) (f : PFunction (n+1))
    (hF : Clean F f) (x : Args n) {R S : Registers (n+2+(3+F.work))}
    (h : SearchReturns (minimizationV F) (minimizationTest F) (minimizationPositive F)
      (minimizationZero F) R S) :
    ∀ j,R=minimizationBoundary F x j → ∃ t,MinChain f x j t ∧ S=resultFile _ x t := by
  induction h with
  | @zero R U S htest hzero hfinish =>
      intro j hR
      subst R
      obtain ⟨v,hv,hU⟩ := (minimization_test_exec F f hF x j U).mp htest
      have hv0 : v=0 := by simpa [hU,updateRegister] using hzero
      subst v
      rw [min_update_zero] at hU
      subst U
      exact ⟨j,.zero j hv,(minimization_zero_exec F x j S).mp hfinish⟩
  | @positive R U V S htest hpos hnext hrest ih =>
      intro j hR
      subst R
      obtain ⟨v,hv,rfl⟩ := (minimization_test_exec F f hF x j U).mp htest
      have hvpos : 0<v := by simpa [updateRegister] using hpos
      have hstep : Exec (minimizationPositive F)
          (updateRegister (minimizationBoundary F x j) (minimizationV F) (v-1)) V := by
        simpa [updateRegister] using hnext
      have hV := (minimization_positive_exec F x j v hvpos V).mp hstep
      obtain ⟨t,ht,hS⟩ := ih (j+1) hV
      exact ⟨t,.positive hvpos hv ht,hS⟩

private theorem min_search_reverse {n : ℕ} (F : Routine (n+1)) (f : PFunction (n+1))
    (hF : Clean F f) (x : Args n) {j t : ℕ} (h : MinChain f x j t) :
    SearchReturns (minimizationV F) (minimizationTest F) (minimizationPositive F)
      (minimizationZero F) (minimizationBoundary F x j) (resultFile _ x t) := by
  induction h with
  | zero j hz =>
      apply SearchReturns.zero
      · apply (minimization_test_exec F f hF x j _).mpr
        exact ⟨0,hz,(min_update_zero F x j).symm⟩
      · exact min_boundary_at_v F x j
      · exact (minimization_zero_exec F x j _).mpr rfl
  | @positive j t a ha hf hrest ih =>
      apply SearchReturns.positive
      · exact (minimization_test_exec F f hF x j _).mpr ⟨a,hf,rfl⟩
      · simpa [updateRegister] using ha
      · simpa [updateRegister] using
          (minimization_positive_exec F x j a ha (minimizationBoundary F x (j+1))).mpr rfl
      · exact ih

private theorem min_boundary_zero {n : ℕ} (F : Routine (n+1)) (x : Args n) :
    minimizationBoundary F x 0=initialFile (3+F.work) x := by
  have hz : initialFile (3+F.work) x (minimizationJ F)=0 :=
    initial_above _ x _ (by rw [min_j_val];omega)
  funext r
  by_cases hr : r=minimizationJ F
  · subst r;simp [minimizationBoundary,updateRegister,hz]
  · simp [minimizationBoundary,updateRegister,hr]

theorem minimization_clean {n : ℕ} (F : Routine (n + 1))
    (f : PFunction (n + 1)) (hF : Clean F f) : Clean (minimizationRoutine F) (minimize f) := by
  dsimp only [Clean,minimizationRoutine]
  constructor
  · apply search_no_internal_halt
    · exact rename_no_internal_halt _ F.body hF.1
    · apply seq_no_internal_halt
      · exact (elementary_no_internal_halt (minimizationV F) (minimizationV F) (minimizationV F)).2.2.2.1
      · exact (elementary_no_internal_halt (minimizationJ F) (minimizationJ F) (minimizationJ F)).2.1
    · apply seq_no_internal_halt
      · exact (elementary_no_internal_halt (minimizationJ F) (outputPort n (3+F.work))
          (minimizationCopyScratch F)).2.2.2.2.2
      · exact (elementary_no_internal_halt (minimizationJ F) (minimizationJ F) (minimizationJ F)).2.2.2.1
  · intro x S
    rw [←min_boundary_zero F x,search_exec]
    constructor
    · intro h
      obtain ⟨t,ht,hS⟩ := min_search_forward F f hF x h 0 rfl
      obtain ⟨_,hz,hbefore⟩ := (min_chain_spec f x 0 t).mp ht
      exact ⟨t,(minimize_spec f x t).mpr ⟨hz,fun i hi => hbefore i (Nat.zero_le _) hi⟩,hS⟩
    · rintro ⟨t,ht,rfl⟩
      obtain ⟨hz,hbefore⟩ := (minimize_spec f x t).mp ht
      exact min_search_reverse F f hF x ((min_chain_spec f x 0 t).mpr
        ⟨Nat.zero_le _,hz,fun i _ hi => hbefore i hi⟩)

end Lemmatheca.ComputabilityTheory.RecursiveTapeCompiler
