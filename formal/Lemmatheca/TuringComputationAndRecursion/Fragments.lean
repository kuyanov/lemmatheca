import Lemmatheca.CounterProgramsOnTape.CounterPrograms

/-! Finite counter fragments with an explicit exit. All control constructors
below expand to the existing increment/decrement/halt instruction datatype. -/
namespace Lemmatheca.ComputabilityTheory.RecursiveTapeCompiler

open CounterPrograms

structure Fragment (k : ℕ) where
  Label : Type
  finite : Fintype Label
  entry : Option Label
  code : Label → Instr k (Option Label)

attribute [instance] Fragment.finite

def Fragment.program {k : ℕ} (B : Fragment k) : Program k (Option B.Label) where
  initial := B.entry
  code
    | none => .halt
    | some p => B.code p

def NoInternalHalt {k : ℕ} (B : Fragment k) : Prop := ∀ p, B.code p ≠ .halt

def Reaches {k : ℕ} {L : Type*} (P : Program k L) (S U : Config k L) : Prop :=
  Relation.ReflTransGen (Step P) S U

def Exec {k : ℕ} (B : Fragment k) (R S : Registers k) : Prop :=
  Reaches B.program ⟨B.entry, R⟩ ⟨none, S⟩

def renameInstr {k K : ℕ} {L M : Type*} (ρ : Fin k → Fin K) (τ : L → M) :
    Instr k L → Instr K M
  | .inc r q => .inc (ρ r) (τ q)
  | .dec r qp qz => .dec (ρ r) (τ qp) (τ qz)
  | .halt => .halt

def renameProgram {k K : ℕ} {L : Type*} (ρ : Fin k → Fin K) (P : Program k L) : Program K L :=
  ⟨P.initial, fun p => renameInstr ρ id (P.code p)⟩

def renameFragment {k K : ℕ} (ρ : Fin k → Fin K) (B : Fragment k) : Fragment K :=
  ⟨B.Label, B.finite, B.entry, fun p => renameInstr ρ id (B.code p)⟩

def FrameAgrees {k K : ℕ} (ρ : Fin k → Fin K) (R : Registers k) (U : Registers K) : Prop :=
  ∀ r, U (ρ r) = R r

def ExternalFrame {k K : ℕ} (ρ : Fin k → Fin K) (U V : Registers K) : Prop :=
  ∀ r, r ∉ Set.range ρ → V r = U r

def doneFragment (k : ℕ) : Fragment k :=
  ⟨Empty, inferInstance, none, Empty.elim⟩

def incrementFragment {k : ℕ} (r : Fin k) : Fragment k :=
  ⟨Unit, inferInstance, some (), fun _ => .inc r none⟩

def gotoFragment {k : ℕ} (z : Fin k) : Fragment k :=
  ⟨Bool, inferInstance, some false, fun p =>
    if p then .dec z none none else .inc z (some true)⟩

def clearFragment {k : ℕ} (r : Fin k) : Fragment k :=
  ⟨Unit, inferInstance, some (), fun _ => .dec r (some ()) none⟩

def transferFragment {k : ℕ} (r t : Fin k) : Fragment k :=
  ⟨Bool, inferInstance, some false, fun p =>
    if p then .inc t (some false) else .dec r (some true) none⟩

def copyFragment {k : ℕ} (x y z : Fin k) : Fragment k where
  Label := Fin 5
  finite := inferInstance
  entry := some 0
  code p := match p.val with
    | 0 => .dec x (some 1) (some 3)
    | 1 => .inc y (some 2)
    | 2 => .inc z (some 0)
    | 3 => .dec z (some 4) none
    | _ => .inc x (some 3)

inductive SeqLabel (A B : Type)
  | left (p : A) | right (p : B) | returnInc | returnDec
  deriving Fintype

def seqLeft {k : ℕ} (B C : Fragment k) : Option B.Label → Option (SeqLabel B.Label C.Label)
  | none => some .returnInc
  | some p => some (.left p)

def seqRight {k : ℕ} (B C : Fragment k) : Option C.Label → Option (SeqLabel B.Label C.Label) :=
  Option.map SeqLabel.right

def seqFragment {k : ℕ} (z : Fin k) (B C : Fragment k) : Fragment k where
  Label := SeqLabel B.Label C.Label
  finite := inferInstance
  entry := seqLeft B C B.entry
  code
    | .left p => renameInstr id (seqLeft B C) (B.code p)
    | .right p => renameInstr id (seqRight B C) (C.code p)
    | .returnInc => .inc z (some .returnDec)
    | .returnDec => .dec z (seqRight B C C.entry) (seqRight B C C.entry)

def sequence {k : ℕ} (z : Fin k) : List (Fragment k) → Fragment k
  | [] => doneFragment k
  | B :: bs => seqFragment z B (sequence z bs)

inductive RepeatLabel (A : Type)
  | controller | body (p : A) | returnInc | returnDec
  deriving Fintype

def repeatBody {k : ℕ} (B : Fragment k) : Option B.Label → Option (RepeatLabel B.Label)
  | none => some .returnInc
  | some p => some (.body p)

def repeatFragment {k : ℕ} (r z : Fin k) (B : Fragment k) : Fragment k where
  Label := RepeatLabel B.Label
  finite := inferInstance
  entry := some .controller
  code
    | .controller => .dec r (repeatBody B B.entry) none
    | .body p => renameInstr id (repeatBody B) (B.code p)
    | .returnInc => .inc z (some .returnDec)
    | .returnDec => .dec z (some .controller) (some .controller)

inductive SearchLabel (A B C : Type)
  | test (p : A) | positive (p : B) | zero (p : C)
  | branch | testInc | testDec | loopInc | loopDec
  deriving Fintype

def searchTest {k : ℕ} (B P Z : Fragment k) :
    Option B.Label → Option (SearchLabel B.Label P.Label Z.Label)
  | none => some .testInc
  | some p => some (.test p)

def searchPositive {k : ℕ} (B P Z : Fragment k) :
    Option P.Label → Option (SearchLabel B.Label P.Label Z.Label)
  | none => some .loopInc
  | some p => some (.positive p)

def searchZero {k : ℕ} (B P Z : Fragment k) :
    Option Z.Label → Option (SearchLabel B.Label P.Label Z.Label) :=
  Option.map SearchLabel.zero

def searchFragment {k : ℕ} (v z : Fin k) (B P Z : Fragment k) : Fragment k where
  Label := SearchLabel B.Label P.Label Z.Label
  finite := inferInstance
  entry := searchTest B P Z B.entry
  code
    | .test p => renameInstr id (searchTest B P Z) (B.code p)
    | .positive p => renameInstr id (searchPositive B P Z) (P.code p)
    | .zero p => renameInstr id (searchZero B P Z) (Z.code p)
    | .branch => .dec v (searchPositive B P Z P.entry) (searchZero B P Z Z.entry)
    | .testInc => .inc z (some .testDec)
    | .testDec => .dec z (some .branch) (some .branch)
    | .loopInc => .inc z (some .loopDec)
    | .loopDec => .dec z (searchTest B P Z B.entry) (searchTest B P Z B.entry)


private theorem update_agrees {k K : ℕ} (ρ : Fin k → Fin K) (hρ : Function.Injective ρ)
    (R : Registers k) (V : Registers K) (hV : FrameAgrees ρ R V) (r : Fin k) (a : ℕ) :
    FrameAgrees ρ (updateRegister R r a) (updateRegister V (ρ r) a) := by
  intro t
  by_cases ht : t = r
  · subst t; simp [updateRegister]
  · have hρt : ρ t ≠ ρ r := fun h => ht (hρ h)
    simp [updateRegister, ht, hρt, hV t]

private theorem update_frame {k K : ℕ} (ρ : Fin k → Fin K)
    (V : Registers K) (r : Fin k) (a : ℕ) :
    ExternalFrame ρ V (updateRegister V (ρ r) a) := by
  intro t ht
  have hn : t ≠ ρ r := fun h => ht ⟨r, h.symm⟩
  simp [updateRegister, hn]

private theorem renamed_halt {k K : ℕ} {L : Type*} (ρ : Fin k → Fin K)
    (P : Program k L) (p : L) (R : Registers k) (V : Registers K) :
    Halted (renameProgram ρ P) ⟨p, V⟩ ↔ Halted P ⟨p, R⟩ := by
  cases h : P.code p <;> simp [Halted, renameProgram, renameInstr, h]

private theorem rename_advance {k K : ℕ} {L : Type*} (ρ : Fin k → Fin K)
    (hρ : Function.Injective ρ) (P : Program k L) (p : L)
    (R : Registers k) (V : Registers K) (hV : FrameAgrees ρ R V) :
    (advance (renameProgram ρ P) ⟨p,V⟩).pc = (advance P ⟨p,R⟩).pc ∧
    FrameAgrees ρ (advance P ⟨p,R⟩).regs (advance (renameProgram ρ P) ⟨p,V⟩).regs ∧
    ExternalFrame ρ V (advance (renameProgram ρ P) ⟨p,V⟩).regs := by
  cases h : P.code p with
  | halt =>
      simp only [advance, step, renameProgram, renameInstr, h, Option.getD_none]
      exact ⟨by trivial, hV, fun _ _ => rfl⟩
  | inc r q =>
      simp only [advance, step, renameProgram, renameInstr, h, Option.getD_some]
      exact ⟨rfl, by simpa [hV r] using update_agrees ρ hρ R V hV r (R r + 1),
        update_frame ρ V r (V (ρ r) + 1)⟩
  | dec r qp qz =>
      by_cases hz : R r = 0
      · have hv : V (ρ r) = 0 := (hV r).trans hz
        simp only [advance, step, renameProgram, renameInstr, h, hz, hv, ↓reduceIte, Option.getD_some]
        exact ⟨by trivial, hV, fun _ _ => rfl⟩
      · have hv : V (ρ r) ≠ 0 := by simpa [hV r] using hz
        simp only [advance, step, renameProgram, renameInstr, h, hz, hv, ↓reduceIte,
          Option.getD_some]
        exact ⟨rfl, by simpa [hV r] using update_agrees ρ hρ R V hV r (R r - 1),
          update_frame ρ V r (V (ρ r) - 1)⟩

theorem reaches_iff_run {k : ℕ} {L : Type*} (P : Program k L) (S U : Config k L) :
    Reaches P S U ↔ ∃ j, run P S j = U := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail U V h hUV ih =>
        obtain ⟨j, rfl⟩ := ih
        exact ⟨j+1, by simp [run, advance, show step P (run P S j) = some V from hUV]⟩
  · rintro ⟨j, rfl⟩
    induction j with
    | zero => exact .refl
    | succ j ih =>
        cases h : step P (run P S j) with
        | none => simpa [run, advance, h] using ih
        | some U =>
            simpa [run, advance, h, Reaches] using ih.tail (show Step P (run P S j) U from h)

theorem fragment_halt_iff {k : ℕ} (B : Fragment k) (hB : NoInternalHalt B) (S : Config k (Option B.Label)) :
    Halted B.program S ↔ S.pc = none := by
  cases S with
  | mk p R => cases p with
    | none => simp [Halted, Fragment.program]
    | some p => simp [Halted, Fragment.program, hB p]

theorem rename_step {k K : ℕ} {L : Type*} (ρ : Fin k → Fin K)
    (hρ : Function.Injective ρ) (P : Program k L) (S U : Config k L) (V : Registers K)
    (hV : FrameAgrees ρ S.regs V) (hSU : Step P S U) :
    ∃ W, Step (renameProgram ρ P) ⟨S.pc, V⟩ ⟨U.pc, W⟩ ∧
      FrameAgrees ρ U.regs W ∧ ExternalFrame ρ V W := by
  cases S with
  | mk p R =>
    cases U with
    | mk q T =>
      cases hc : P.code p with
      | halt => simp [Step, step, hc] at hSU
      | inc r q' =>
          simp only [Step, step, hc, Option.some.injEq, Config.mk.injEq] at hSU
          rcases hSU with ⟨rfl, rfl⟩
          refine ⟨updateRegister V (ρ r) (R r + 1), ?_, update_agrees ρ hρ R V hV r _, ?_⟩
          · simp [Step, step, renameProgram, renameInstr, hc, hV r]
          · exact update_frame ρ V r _
      | dec r qp qz =>
          by_cases hz : R r = 0
          · simp only [Step, step, hc, hz, ↓reduceIte, Option.some.injEq, Config.mk.injEq] at hSU
            rcases hSU with ⟨rfl, rfl⟩
            refine ⟨V, ?_, hV, fun _ _ => rfl⟩
            simp [Step, step, renameProgram, renameInstr, hc, hV r, hz]
          · simp only [Step, step, hc, hz, ↓reduceIte, Option.some.injEq, Config.mk.injEq] at hSU
            rcases hSU with ⟨rfl, rfl⟩
            refine ⟨updateRegister V (ρ r) (R r - 1), ?_, update_agrees ρ hρ R V hV r _, ?_⟩
            · simp [Step, step, renameProgram, renameInstr, hc, hV r, hz]
            · exact update_frame ρ V r _

theorem rename_run {k K : ℕ} {L : Type*} (ρ : Fin k → Fin K)
    (hρ : Function.Injective ρ) (P : Program k L) (S : Config k L) (V : Registers K)
    (hV : FrameAgrees ρ S.regs V) (j : ℕ) :
    let U := run (renameProgram ρ P) ⟨S.pc, V⟩ j
    U.pc = (run P S j).pc ∧ FrameAgrees ρ (run P S j).regs U.regs ∧
      ExternalFrame ρ V U.regs ∧ (Halted (renameProgram ρ P) U ↔ Halted P (run P S j)) := by
  dsimp only
  have hh : ∀ j, (run (renameProgram ρ P) ⟨S.pc,V⟩ j).pc = (run P S j).pc ∧
      FrameAgrees ρ (run P S j).regs (run (renameProgram ρ P) ⟨S.pc,V⟩ j).regs ∧
      ExternalFrame ρ V (run (renameProgram ρ P) ⟨S.pc,V⟩ j).regs := by
    intro j
    induction j with
    | zero => exact ⟨by trivial, hV, fun _ _ => rfl⟩
    | succ j ih =>
        obtain ⟨hp, ha, hf⟩ := ih
        have hm := rename_advance ρ hρ P (run P S j).pc (run P S j).regs
          (run (renameProgram ρ P) ⟨S.pc,V⟩ j).regs ha
        have he : run (renameProgram ρ P) ⟨S.pc,V⟩ j =
            ⟨(run P S j).pc, (run (renameProgram ρ P) ⟨S.pc,V⟩ j).regs⟩ := by
          ext <;> simp [hp]
        rw [run, he]
        refine ⟨hm.1, hm.2.1, ?_⟩
        intro r hr
        exact (hm.2.2 r hr).trans (hf r hr)
  obtain ⟨hp, ha, hf⟩ := hh j
  refine ⟨hp, ha, hf, ?_⟩
  change renameInstr ρ id (P.code (run (renameProgram ρ P) ⟨S.pc,V⟩ j).pc) = .halt ↔ _
  rw [hp]
  exact
    renamed_halt ρ P (run P S j).pc (run P S j).regs
      (run (renameProgram ρ P) ⟨S.pc,V⟩ j).regs

theorem rename_exec {k K : ℕ} (ρ : Fin k → Fin K) (hρ : Function.Injective ρ)
    (B : Fragment k) (R : Registers k) (U V : Registers K) (hU : FrameAgrees ρ R U) :
    Exec (renameFragment ρ B) U V ↔
      ∃ S, Exec B R S ∧ FrameAgrees ρ S V ∧ ExternalFrame ρ U V := by
  have he : (renameFragment ρ B).program = renameProgram ρ B.program := by
    change Program.mk B.entry _ = Program.mk B.entry _
    congr 1
    funext p
    cases p <;> rfl
  change Reaches (renameFragment ρ B).program (⟨B.entry,U⟩ : Config K (Option B.Label)) ⟨none,V⟩ ↔
    ∃ S, Exec B R S ∧ FrameAgrees ρ S V ∧ ExternalFrame ρ U V
  dsimp only [renameFragment] at *
  rw [he]
  rw [reaches_iff_run]
  constructor
  · rintro ⟨j, hj⟩
    have hh := rename_run ρ hρ B.program ⟨B.entry,R⟩ U hU j
    dsimp only at hh
    rw [hj] at hh
    refine ⟨(run B.program ⟨B.entry,R⟩ j).regs, ?_, hh.2.1, hh.2.2.1⟩
    apply (reaches_iff_run _ _ _).mpr
    refine ⟨j, ?_⟩
    apply Config.ext
    · exact hh.1.symm
    · rfl
  · rintro ⟨S, hS, hV, hf⟩
    obtain ⟨j, hj⟩ := (reaches_iff_run _ _ _).mp hS
    have hh := rename_run ρ hρ B.program ⟨B.entry,R⟩ U hU j
    dsimp only at hh
    rw [hj] at hh
    refine ⟨j, ?_⟩
    apply Config.ext
    · exact hh.1
    · funext r
      by_cases hr : r ∈ Set.range ρ
      · obtain ⟨t, rfl⟩ := hr
        exact (hh.2.1 t).trans (hV t).symm
      · exact (hh.2.2.1 r hr).trans (hf r hr).symm

theorem rename_no_internal_halt {k K : ℕ} (ρ : Fin k → Fin K) (B : Fragment k)
    (hB : NoInternalHalt B) : NoInternalHalt (renameFragment ρ B) := by
  intro p
  cases h : B.code p with
  | halt => exact False.elim (hB p h)
  | inc r q => simp [renameFragment, renameInstr, h]
  | dec r qp qz => simp [renameFragment, renameInstr, h]

theorem elementary_no_internal_halt {k : ℕ} (r t z : Fin k) :
    NoInternalHalt (doneFragment k) ∧ NoInternalHalt (incrementFragment r) ∧
    NoInternalHalt (gotoFragment z) ∧ NoInternalHalt (clearFragment r) ∧
    NoInternalHalt (transferFragment r t) ∧ NoInternalHalt (copyFragment r t z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p; exact Empty.elim p
  · intro p; simp [incrementFragment]
  · intro p; cases p <;> simp [gotoFragment]
  · intro p; simp [clearFragment]
  · intro p; cases p <;> simp [transferFragment]
  · intro p; fin_cases p <;> simp [copyFragment]

theorem goto_exact {k : ℕ} (z : Fin k) (R : Registers k) :
    run (gotoFragment z).program ⟨some false, R⟩ 2 = ⟨none, R⟩ ∧
      ∀ j < 2, ¬ Halted (gotoFragment z).program (run (gotoFragment z).program ⟨some false, R⟩ j) := by
  constructor
  · simp [run, advance, step, gotoFragment, Fragment.program, updateRegister]
  · intro j hj
    interval_cases j <;> simp [run, advance, step, gotoFragment, Fragment.program, Halted]


private theorem nonhalt_before {k : ℕ} {L : Type*} (P : Program k L)
    (S : Config k L) (t : ℕ) (ht : ¬ Halted P (run P S t)) :
    ∀ j < t+1, ¬ Halted P (run P S j) := by
  intro j hj hhalt
  have hle : j ≤ t := by omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  exact ht (by simpa [hd, run_halted_add P S j d hhalt] using hhalt)

private theorem clear_prefix {k : ℕ} (r : Fin k) (R : Registers k) (j : ℕ) (hj : j ≤ R r) :
    run (clearFragment r).program ⟨some (),R⟩ j =
      ⟨some (),updateRegister R r (R r-j)⟩ := by
  induction j with
  | zero => simp [run, updateRegister]
  | succ j ih =>
      rw [run, ih (by omega)]
      have hz : R r-j ≠ 0 := by omega
      simp [advance, step, clearFragment, Fragment.program, updateRegister, hz,
        Function.update_idem, show R r-j-1=R r-(j+1) by omega]

private theorem transfer_prefix {k : ℕ} (r t : Fin k) (hrt : r ≠ t)
    (R : Registers k) (j : ℕ) (hj : j ≤ R r) :
    run (transferFragment r t).program ⟨some false,R⟩ (2*j) =
      ⟨some false,updateRegister (updateRegister R r (R r-j)) t (R t+j)⟩ := by
  induction j with
  | zero =>
      apply Config.ext
      · rfl
      · funext q
        by_cases hqr : q=r <;> by_cases hqt : q=t <;>
          simp_all [run, updateRegister]
  | succ j ih =>
      rw [show 2*(j+1)=2*j+2 by omega,run_add,ih (by omega)]
      have hz : R r-j ≠ 0 := by omega
      simp only [run, advance, step, transferFragment, Fragment.program, Bool.false_eq_true,
        ↓reduceIte, updateRegister, Function.update_of_ne hrt,
        Function.update_self, hz, Option.getD_some]
      apply Config.ext
      · rfl
      · funext q
        by_cases hqr : q=r <;> by_cases hqt : q=t <;>
          simp_all [updateRegister]
        all_goals omega


private theorem copy_a_pos {k : ℕ} (x y z : Fin k) (R : Registers k) (hx : R x ≠ 0) :
    @advance k (Option (Fin 5)) (copyFragment x y z).program ⟨some (0:Fin 5),R⟩ =
      ⟨some (1:Fin 5),updateRegister R x (R x-1)⟩ := by
  simp [advance,step,copyFragment,Fragment.program,hx]
private theorem copy_a_zero {k : ℕ} (x y z : Fin k) (R : Registers k) (hx : R x = 0) :
    @advance k (Option (Fin 5)) (copyFragment x y z).program ⟨some (0:Fin 5),R⟩ = ⟨some (3:Fin 5),R⟩ := by
  simp [advance,step,copyFragment,Fragment.program,hx]
private theorem copy_b {k : ℕ} (x y z : Fin k) (R : Registers k) :
    @advance k (Option (Fin 5)) (copyFragment x y z).program ⟨some (1:Fin 5),R⟩ =
      ⟨some (2:Fin 5),updateRegister R y (R y+1)⟩ := by
  simp [advance,step,copyFragment,Fragment.program]
private theorem copy_c {k : ℕ} (x y z : Fin k) (R : Registers k) :
    @advance k (Option (Fin 5)) (copyFragment x y z).program ⟨some (2:Fin 5),R⟩ =
      ⟨some (0:Fin 5),updateRegister R z (R z+1)⟩ := by
  simp [advance,step,copyFragment,Fragment.program]
private theorem copy_d_pos {k : ℕ} (x y z : Fin k) (R : Registers k) (hz : R z ≠ 0) :
    @advance k (Option (Fin 5)) (copyFragment x y z).program ⟨some (3:Fin 5),R⟩ =
      ⟨some (4:Fin 5),updateRegister R z (R z-1)⟩ := by
  simp [advance,step,copyFragment,Fragment.program,hz]
private theorem copy_d_zero {k : ℕ} (x y z : Fin k) (R : Registers k) (hz : R z = 0) :
    @advance k (Option (Fin 5)) (copyFragment x y z).program ⟨some (3:Fin 5),R⟩ = ⟨none,R⟩ := by
  simp [advance,step,copyFragment,Fragment.program,hz]
private theorem copy_e {k : ℕ} (x y z : Fin k) (R : Registers k) :
    @advance k (Option (Fin 5)) (copyFragment x y z).program ⟨some (4:Fin 5),R⟩ =
      ⟨some (3:Fin 5),updateRegister R x (R x+1)⟩ := by
  simp [advance,step,copyFragment,Fragment.program]

private theorem copy_forward_general {k : ℕ} (x y z : Fin k)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) (R : Registers k) (j : ℕ) (hj : j≤R x) :
    run (copyFragment x y z).program ⟨some (0:Fin 5),R⟩ (3*j) =
      ⟨some (0:Fin 5),updateRegister (updateRegister (updateRegister R x (R x-j)) y (R y+j)) z (R z+j)⟩ := by
  induction j with
  | zero =>
      apply Config.ext
      · rfl
      · funext q
        by_cases hx : q=x <;> by_cases hy : q=y <;> by_cases hz : q=z <;>
          simp_all [run,updateRegister]
  | succ j ih =>
      rw [show 3*(j+1)=3*j+3 by omega,run_add,ih (by omega)]
      have hn : R x-j ≠ 0 := by omega
      dsimp only [run,copyFragment] at *
      change @advance k (Option (Fin 5)) (copyFragment x y z).program (@advance k (Option (Fin 5)) (copyFragment x y z).program
        (@advance k (Option (Fin 5)) (copyFragment x y z).program _)) = _
      rw [copy_a_pos x y z _ (by simpa [updateRegister,hxz,hxy] using hn),copy_b,copy_c]
      apply Config.ext
      · rfl
      · funext q
        by_cases hx : q=x <;> by_cases hy : q=y <;> by_cases hz : q=z <;>
          simp_all [updateRegister]
        all_goals omega

private theorem copy_restoration_general {k : ℕ} (x y z : Fin k)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) (R : Registers k) (j : ℕ) (hj : j≤R x+R z) :
    run (copyFragment x y z).program ⟨some (0:Fin 5),R⟩ (3*R x+1+2*j) =
      ⟨some (3:Fin 5),updateRegister (updateRegister (updateRegister R x j) y (R y+R x)) z (R x+R z-j)⟩ := by
  induction j with
  | zero =>
      rw [show 3*R x+1+2*0=3*R x+1 by omega,run_add,
        copy_forward_general x y z hxy hxz hyz R (R x) le_rfl]
      dsimp only [run,copyFragment] at *
      change @advance k (Option (Fin 5)) (copyFragment x y z).program _ = _
      rw [copy_a_zero x y z _ (by simp [updateRegister,hxz,hxy])]
      apply Config.ext
      · rfl
      · funext q
        by_cases hx : q=x <;> by_cases hy : q=y <;> by_cases hz : q=z <;>
          simp_all [updateRegister]
        all_goals omega
  | succ j ih =>
      rw [show 3*R x+1+2*(j+1)=(3*R x+1+2*j)+2 by omega,run_add,ih (by omega)]
      have hn : R x+R z-j ≠ 0 := by omega
      dsimp only [run,copyFragment] at *
      change @advance k (Option (Fin 5)) (copyFragment x y z).program (@advance k (Option (Fin 5)) (copyFragment x y z).program _) = _
      rw [copy_d_pos x y z _ (by simpa [updateRegister] using hn),copy_e]
      apply Config.ext
      · rfl
      · funext q
        by_cases hx : q=x <;> by_cases hy : q=y <;> by_cases hz : q=z <;>
          simp_all [updateRegister]
        all_goals omega

theorem clear_exact {k : ℕ} (r : Fin k) (R : Registers k) :
    run (clearFragment r).program ⟨some (), R⟩ (R r + 1) = ⟨none, updateRegister R r 0⟩ ∧
      ∀ j < R r + 1, ¬ Halted (clearFragment r).program
        (run (clearFragment r).program ⟨some (), R⟩ j) := by
  have hpre := clear_prefix r R (R r) le_rfl
  constructor
  · rw [show R r+1=R r+1 by rfl, run_add,hpre]
    simp [run,advance,step,clearFragment,Fragment.program,updateRegister]
  · exact nonhalt_before _ _ (R r) (by rw [hpre]; simp [Halted,Fragment.program,clearFragment])

theorem transfer_exact {k : ℕ} (r t : Fin k) (hrt : r ≠ t) (R : Registers k) :
    run (transferFragment r t).program ⟨some false, R⟩ (2 * R r + 1) =
      ⟨none, updateRegister (updateRegister R r 0) t (R t + R r)⟩ ∧
      ∀ j < 2 * R r + 1, ¬ Halted (transferFragment r t).program
        (run (transferFragment r t).program ⟨some false, R⟩ j) := by
  have hpre := transfer_prefix r t hrt R (R r) le_rfl
  constructor
  · rw [run_add,hpre]
    simp [run,advance,step,transferFragment,Fragment.program,updateRegister,hrt]
  · exact nonhalt_before _ _ (2*R r) (by rw [hpre]; simp [Halted,Fragment.program,transferFragment])

theorem copy_forward {k : ℕ} (x y z : Fin k)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (R : Registers k)
    (hy : R y = 0) (hz : R z = 0) (j : ℕ) (hj : j ≤ R x) :
    run (copyFragment x y z).program ⟨some (0 : Fin 5), R⟩ (3 * j) =
      ⟨some (0 : Fin 5), updateRegister (updateRegister (updateRegister R x (R x - j)) y j) z j⟩ := by
  simpa [hy,hz] using copy_forward_general x y z hxy hxz hyz R j hj

theorem copy_restoration {k : ℕ} (x y z : Fin k)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (R : Registers k)
    (hy : R y = 0) (hz : R z = 0) (j : ℕ) (hj : j ≤ R x) :
    run (copyFragment x y z).program ⟨some (0 : Fin 5), R⟩ (3 * R x + 1 + 2 * j) =
      ⟨some (3 : Fin 5), updateRegister (updateRegister (updateRegister R x j) y (R x)) z (R x - j)⟩ := by
  simpa [hy,hz] using copy_restoration_general x y z hxy hxz hyz R j (by omega)

theorem copy_exact {k : ℕ} (x y z : Fin k)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (R : Registers k)
    (hy : R y = 0) (hz : R z = 0) :
    run (copyFragment x y z).program ⟨some (0 : Fin 5), R⟩ (5 * R x + 2) =
      ⟨none, updateRegister R y (R x)⟩ ∧
      ∀ j < 5 * R x + 2, ¬ Halted (copyFragment x y z).program
        (run (copyFragment x y z).program ⟨some (0 : Fin 5), R⟩ j) := by
  have hpre := copy_restoration x y z hxy hxz hyz R hy hz (R x) le_rfl
  have ht : 3*R x+1+2*R x=5*R x+1 := by omega
  rw [ht] at hpre
  constructor
  · rw [show 5*R x+2=(5*R x+1)+1 by omega,run_add,hpre]
    dsimp only [run,copyFragment] at *
    change @advance k (Option (Fin 5)) (copyFragment x y z).program _ = _
    rw [copy_d_zero x y z _ (by simp [updateRegister])]
    apply Config.ext
    · rfl
    · funext q
      by_cases hqx : q=x <;> by_cases hqy : q=y <;> by_cases hqz : q=z <;>
        simp_all [updateRegister]
  · have hn := nonhalt_before (copyFragment x y z).program ⟨some (0:Fin 5),R⟩
      (5*R x+1) (by rw [hpre]; simp [Halted,Fragment.program,copyFragment])
    simpa [Nat.add_assoc] using hn


theorem copy_offsets {k : ℕ} (x y z : Fin k)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (R : Registers k) :
    run (copyFragment x y z).program ⟨some (0 : Fin 5), R⟩ (5 * R x + 2 * R z + 2) =
      ⟨none, updateRegister (updateRegister (updateRegister R x (R x + R z)) y (R y + R x)) z 0⟩ := by
  have hpre := copy_restoration_general x y z hxy hxz hyz R (R x+R z) le_rfl
  rw [show 5*R x+2*R z+2=(3*R x+1+2*(R x+R z))+1 by omega,run_add,hpre]
  dsimp only [run,copyFragment] at *
  change @advance k (Option (Fin 5)) (copyFragment x y z).program _ = _
  rw [copy_d_zero x y z _ (by simp [updateRegister])]
  simp only [Nat.sub_self]

theorem seq_return_goto {k : ℕ} (z : Fin k) (B C : Fragment k) (R : Registers k) :
    run (seqFragment z B C).program ⟨some .returnInc, R⟩ 2 =
      ⟨seqRight B C C.entry, R⟩ := by
  simp [run, advance, step, seqFragment, Fragment.program, updateRegister]


def InFirstComponent {k : ℕ} (B C : Fragment k) : Option (SeqLabel B.Label C.Label) → Prop
  | some (.left _) | some .returnInc | some .returnDec => True
  | _ => False


private theorem exit_reaches {k : ℕ} (B : Fragment k) (R S : Registers k) :
    Reaches B.program ⟨none,R⟩ ⟨none,S⟩ ↔ R=S := by
  rw [reaches_iff_run]
  constructor
  · rintro ⟨j,hj⟩
    have hs : run B.program ⟨none,R⟩ j = ⟨none,R⟩ := by
      simpa only [Nat.zero_add,run] using run_halted_add B.program ⟨none,R⟩ 0 j rfl
    rw [hs] at hj
    exact congrArg Config.regs hj
  · rintro rfl
    exact ⟨0,rfl⟩

private theorem lift_step {k : ℕ} {L M : Type*} (P : Program k L) (Q : Program k M)
    (τ : L → M) (hc : ∀ p, P.code p ≠ .halt → Q.code (τ p) = renameInstr id τ (P.code p))
    (S U : Config k L) (hSU : Step P S U) :
    Step Q ⟨τ S.pc,S.regs⟩ ⟨τ U.pc,U.regs⟩ := by
  cases S with
  | mk p R => cases U with
    | mk q T =>
      cases h : P.code p with
      | halt => simp [Step,step,h] at hSU
      | inc r next =>
          have hq := hc p (by simp [h])
          simp only [Step,step,h,Option.some.injEq,Config.mk.injEq] at hSU
          rcases hSU with ⟨rfl,rfl⟩
          simp [Step,step,hq,h,renameInstr]
      | dec r positive zero =>
          have hq := hc p (by simp [h])
          by_cases hz : R r=0
          · simp only [Step,step,h,hz,↓reduceIte,Option.some.injEq,Config.mk.injEq] at hSU
            rcases hSU with ⟨rfl,rfl⟩
            simp [Step,step,hq,h,renameInstr,hz]
          · simp only [Step,step,h,hz,↓reduceIte,Option.some.injEq,Config.mk.injEq] at hSU
            rcases hSU with ⟨rfl,rfl⟩
            simp [Step,step,hq,h,renameInstr,hz]

private theorem lift_reaches {k : ℕ} {L M : Type*} (P : Program k L) (Q : Program k M)
    (τ : L → M) (hc : ∀ p, P.code p ≠ .halt → Q.code (τ p) = renameInstr id τ (P.code p))
    (S U : Config k L) (hSU : Reaches P S U) :
    Reaches Q ⟨τ S.pc,S.regs⟩ ⟨τ U.pc,U.regs⟩ := by
  exact Relation.ReflTransGen.lift (fun S : Config k L => (⟨τ S.pc,S.regs⟩ : Config k M))
    (fun _ _ h => lift_step P Q τ hc _ _ h) S U hSU

private theorem backward_reaches {k : ℕ} {L : Type*} (P : Program k L)
    (S U : Config k L) (h : Reaches P S U) (V : Config k L → Prop)
    (hU : V U) (hstep : ∀ a b, Step P a b → V b → V a) : V S := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hU
  | @head a b hab _ ih => exact hstep a b hab ih

private def SeqSpec {k : ℕ} (z : Fin k) (B C : Fragment k) (S : Registers k) :
    Config k (Option (SeqLabel B.Label C.Label)) → Prop
  | ⟨none,R⟩ => R=S
  | ⟨some (.left p),R⟩ => ∃ U, Reaches B.program ⟨some p,R⟩ ⟨none,U⟩ ∧ Exec C U S
  | ⟨some (.right p),R⟩ => Reaches C.program ⟨some p,R⟩ ⟨none,S⟩
  | ⟨some .returnInc,R⟩ => Exec C R S
  | ⟨some .returnDec,R⟩ => Exec C (updateRegister R z (R z-1)) S

private theorem seqSpec_left {k : ℕ} (z : Fin k) (B C : Fragment k)
    (p : Option B.Label) (R S : Registers k) :
    SeqSpec z B C S ⟨seqLeft B C p,R⟩ ↔
      ∃ U, Reaches B.program ⟨p,R⟩ ⟨none,U⟩ ∧ Exec C U S := by
  cases p with
  | none => simp [SeqSpec,seqLeft,exit_reaches]
  | some p => rfl

private theorem seqSpec_right {k : ℕ} (z : Fin k) (B C : Fragment k)
    (p : Option C.Label) (R S : Registers k) :
    SeqSpec z B C S ⟨seqRight B C p,R⟩ ↔ Reaches C.program ⟨p,R⟩ ⟨none,S⟩ := by
  cases p with
  | none => simp [SeqSpec,seqRight,exit_reaches]
  | some p => rfl

private theorem seq_backward {k : ℕ} (z : Fin k) (B C : Fragment k)
    (R S : Registers k) (h : Exec (seqFragment z B C) R S) :
    ∃ U, Exec B R U ∧ Exec C U S := by
  dsimp only [seqFragment] at *
  have hh : SeqSpec z B C S ⟨seqLeft B C B.entry,R⟩ := by
    apply backward_reaches (seqFragment z B C).program _ ⟨none,S⟩ h (SeqSpec z B C S)
    · exact rfl
    · intro a b hab hb
      dsimp only [seqFragment] at *
      cases a with
      | mk p A =>
        cases p with
        | none => simp [Step,step,Fragment.program] at hab
        | some p =>
          cases p with
          | left p =>
              cases hc : B.code p with
              | halt => simp [Step,step,Fragment.program,seqFragment,hc,renameInstr] at hab
              | inc r next =>
                  simp only [Step,step,Fragment.program,seqFragment,hc,renameInstr,id_eq,
                    ] at hab
                  have he := Option.some.inj hab
                  subst b
                  obtain ⟨U,hU,hC⟩ := (seqSpec_left z B C next _ _).mp hb
                  exact ⟨U,hU.head (by simp [Step,step,Fragment.program,hc]),hC⟩
              | dec r positive zero =>
                  by_cases hz : A r=0
                  · simp only [Step,step,Fragment.program,seqFragment,hc,renameInstr,id_eq,hz,
                      ↓reduceIte] at hab
                    have he := Option.some.inj hab
                    subst b
                    obtain ⟨U,hU,hC⟩ := (seqSpec_left z B C zero _ _).mp hb
                    exact ⟨U,hU.head (by simp [Step,step,Fragment.program,hc,hz]),hC⟩
                  · simp only [Step,step,Fragment.program,seqFragment,hc,renameInstr,id_eq,hz,
                      ↓reduceIte] at hab
                    have he := Option.some.inj hab
                    subst b
                    obtain ⟨U,hU,hC⟩ := (seqSpec_left z B C positive _ _).mp hb
                    exact ⟨U,hU.head (by simp [Step,step,Fragment.program,hc,hz]),hC⟩
          | right p =>
              cases hc : C.code p with
              | halt => simp [Step,step,Fragment.program,seqFragment,hc,renameInstr] at hab
              | inc r next =>
                  simp only [Step,step,Fragment.program,seqFragment,hc,renameInstr,id_eq,
                    ] at hab
                  have he := Option.some.inj hab
                  subst b
                  exact ((seqSpec_right z B C next _ _).mp hb).head (by simp [Step,step,Fragment.program,hc])
              | dec r positive zero =>
                  by_cases hz : A r=0
                  · simp only [Step,step,Fragment.program,seqFragment,hc,renameInstr,id_eq,hz,
                      ↓reduceIte] at hab
                    have he := Option.some.inj hab
                    subst b
                    exact ((seqSpec_right z B C zero _ _).mp hb).head (by simp [Step,step,Fragment.program,hc,hz])
                  · simp only [Step,step,Fragment.program,seqFragment,hc,renameInstr,id_eq,hz,
                      ↓reduceIte] at hab
                    have he := Option.some.inj hab
                    subst b
                    exact ((seqSpec_right z B C positive _ _).mp hb).head (by simp [Step,step,Fragment.program,hc,hz])
          | returnInc =>
              simp only [Step,step,Fragment.program,seqFragment] at hab
              have he := Option.some.inj hab
              subst b
              simpa [SeqSpec,updateRegister] using hb
          | returnDec =>
              by_cases hz : A z=0
              · simp only [Step,step,Fragment.program,seqFragment,hz,↓reduceIte] at hab
                have he := Option.some.inj hab
                subst b
                have hh := (seqSpec_right z B C C.entry _ _).mp hb
                have hu : updateRegister A z (A z-1) = A := by
                  funext t
                  by_cases ht : t=z <;> simp_all [updateRegister]
                change Exec C (updateRegister A z (A z-1)) S
                rw [hu]
                exact hh
              · simp only [Step,step,Fragment.program,seqFragment,hz,↓reduceIte] at hab
                have he := Option.some.inj hab
                subst b
                exact (seqSpec_right z B C C.entry _ _).mp hb
  exact (seqSpec_left z B C B.entry R S).mp hh


private theorem seq_forward {k : ℕ} (z : Fin k) (B C : Fragment k)
    (R U S : Registers k) (hB : Exec B R U) (hC : Exec C U S) :
    Exec (seqFragment z B C) R S := by
  have hleft := lift_reaches B.program (seqFragment z B C).program (seqLeft B C)
    (by intro p hp; cases p with
        | none => exact False.elim (hp rfl)
        | some p => rfl) _ _ hB
  have hright := lift_reaches C.program (seqFragment z B C).program (seqRight B C)
    (by intro p hp; cases p with
        | none => exact False.elim (hp rfl)
        | some p => rfl) _ _ hC
  have hjump := (reaches_iff_run (seqFragment z B C).program
    (⟨some .returnInc,U⟩ : Config k (Option (SeqLabel B.Label C.Label)))
    ⟨seqRight B C C.entry,U⟩).mpr ⟨2,seq_return_goto z B C U⟩
  exact hleft.trans (hjump.trans hright)

private theorem guarded_lift {k : ℕ} {L M : Type*} (P : Program k L) (Q : Program k M)
    (τ : L → M) (hc : ∀ p, P.code p ≠ .halt → Q.code (τ p) = renameInstr id τ (P.code p))
    (G : M → Prop) (hG : ∀ p, G (τ p)) (S U : Config k L) (hSU : Reaches P S U) :
    ∃ j, run Q ⟨τ S.pc,S.regs⟩ j = ⟨τ U.pc,U.regs⟩ ∧
      ∀ t < j, G (run Q ⟨τ S.pc,S.regs⟩ t).pc := by
  induction hSU with
  | refl => exact ⟨0,rfl,by omega⟩
  | @tail U V h hUV ih =>
      obtain ⟨j,hj,hguard⟩ := ih
      have hstep := lift_step P Q τ hc U V hUV
      refine ⟨j+1,?_,?_⟩
      · rw [run,hj]
        simp [advance,show step Q ⟨τ U.pc,U.regs⟩=some ⟨τ V.pc,V.regs⟩ from hstep]
      · intro t ht
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ ht) with hlt | rfl
        · exact hguard t hlt
        · rw [hj]
          exact hG U.pc

private theorem seq_first_forward {k : ℕ} (z : Fin k) (B C : Fragment k)
    (R S : Registers k) (hB : Exec B R S) :
    ∃ j, run (seqFragment z B C).program ⟨seqLeft B C B.entry,R⟩ j =
      ⟨seqRight B C C.entry,S⟩ ∧ ∀ t < j, InFirstComponent B C
        (run (seqFragment z B C).program ⟨seqLeft B C B.entry,R⟩ t).pc := by
  obtain ⟨j,hj,hguard⟩ := guarded_lift B.program (seqFragment z B C).program (seqLeft B C)
    (by intro p hp; cases p with
        | none => exact False.elim (hp rfl)
        | some p => rfl)
    (InFirstComponent B C) (by intro p; cases p <;> trivial) _ _ hB
  refine ⟨j+2,?_,?_⟩
  · rw [run_add,hj]
    exact seq_return_goto z B C S
  · intro t ht
    by_cases hlt : t<j
    · exact hguard t hlt
    · have hcases : t=j ∨ t=j+1 := by omega
      rcases hcases with rfl | rfl
      · rw [hj]; trivial
      · rw [run,hj]
        simp [advance,step,Fragment.program,seqFragment,seqLeft,InFirstComponent]


private def FirstSpec {k : ℕ} (z : Fin k) (B C : Fragment k) (S : Registers k) :
    Config k (Option (SeqLabel B.Label C.Label)) → Prop
  | ⟨some (.left p),R⟩ => Reaches B.program ⟨some p,R⟩ ⟨none,S⟩
  | ⟨some .returnDec,R⟩ => updateRegister R z (R z-1)=S
  | ⟨_,R⟩ => R=S

private theorem firstSpec_left {k : ℕ} (z : Fin k) (B C : Fragment k)
    (p : Option B.Label) (R S : Registers k) :
    FirstSpec z B C S ⟨seqLeft B C p,R⟩ ↔ Reaches B.program ⟨p,R⟩ ⟨none,S⟩ := by
  cases p with
  | none => simp [FirstSpec,seqLeft,exit_reaches]
  | some p => rfl

private theorem firstSpec_right {k : ℕ} (z : Fin k) (B C : Fragment k)
    (p : Option C.Label) (R S : Registers k) :
    FirstSpec z B C S ⟨seqRight B C p,R⟩ ↔ R=S := by
  cases p <;> rfl

private theorem run_shift {k : ℕ} {L : Type*} (P : Program k L) (U : Config k L) (j : ℕ) :
    run P (advance P U) j = run P U (j+1) := by
  change run P (run P U 1) j = _
  rw [←run_add]
  congr 1
  omega

private theorem seq_first_backward {k : ℕ} (z : Fin k) (B C : Fragment k)
    (R S : Registers k)
    (h : ∃ j, run (seqFragment z B C).program ⟨seqLeft B C B.entry,R⟩ j =
      ⟨seqRight B C C.entry,S⟩ ∧ ∀ t<j, InFirstComponent B C
        (run (seqFragment z B C).program ⟨seqLeft B C B.entry,R⟩ t).pc) : Exec B R S := by
  let Q : Program k (Option (SeqLabel B.Label C.Label)) := (seqFragment z B C).program
  have general : ∀ j (U : Config k (Option (SeqLabel B.Label C.Label))),
      (∀ t<j,InFirstComponent B C (run Q U t).pc) →
      run Q U j = ⟨seqRight B C C.entry,S⟩ → FirstSpec z B C S U := by
    intro j
    induction j with
    | zero =>
        intro U _ he
        simp only [run] at he
        subst U
        exact (firstSpec_right z B C C.entry S S).mpr rfl
    | succ j ih =>
        intro U hg he
        have hstart := hg 0 (by omega)
        simp only [run] at hstart
        have hrest := ih (advance Q U)
          (by intro t ht; rw [run_shift];exact hg (t+1) (by omega))
          (by rw [run_shift];exact he)
        dsimp only [Q,seqFragment] at *
        cases U with
        | mk p A =>
          cases p with
          | none => exact False.elim hstart
          | some p => cases p with
            | right p => exact False.elim hstart
            | left p =>
                cases hc : B.code p with
                | halt => simpa [advance,step,Fragment.program,hc,renameInstr] using hrest
                | inc r next =>
                    simp only [advance,step,Fragment.program,hc,renameInstr,id_eq,Option.getD_some] at hrest
                    exact ((firstSpec_left z B C next _ _).mp hrest).head
                      (by simp [Step,step,Fragment.program,hc])
                | dec r positive zero =>
                    by_cases hz : A r=0
                    · simp only [advance,step,Fragment.program,hc,renameInstr,id_eq,hz,↓reduceIte,Option.getD_some] at hrest
                      exact ((firstSpec_left z B C zero _ _).mp hrest).head
                        (by simp [Step,step,Fragment.program,hc,hz])
                    · simp only [advance,step,Fragment.program,hc,renameInstr,id_eq,hz,↓reduceIte,Option.getD_some] at hrest
                      exact ((firstSpec_left z B C positive _ _).mp hrest).head
                        (by simp [Step,step,Fragment.program,hc,hz])
            | returnInc =>
                simpa [advance,step,Fragment.program,FirstSpec,updateRegister] using hrest
            | returnDec =>
                by_cases hz : A z=0
                · simp only [advance,step,Fragment.program,hz,↓reduceIte,Option.getD_some] at hrest
                  have hh := (firstSpec_right z B C C.entry _ _).mp hrest
                  change updateRegister A z (A z-1)=S
                  rw [←hh]
                  funext t
                  by_cases ht : t=z <;> simp_all [updateRegister]
                · simp only [advance,step,Fragment.program,hz,↓reduceIte,Option.getD_some] at hrest
                  exact (firstSpec_right z B C C.entry _ _).mp hrest
  obtain ⟨j,hj,hguard⟩ := h
  exact (firstSpec_left z B C B.entry R S).mp (general j _ hguard hj)


theorem seq_exec {k : ℕ} (z : Fin k) (B C : Fragment k) (R S : Registers k) :
    Exec (seqFragment z B C) R S ↔ ∃ U, Exec B R U ∧ Exec C U S := by
  constructor
  · exact seq_backward z B C R S
  · rintro ⟨U,hB,hC⟩
    exact seq_forward z B C R U S hB hC

theorem seq_first_continuation {k : ℕ} (z : Fin k) (B C : Fragment k) (R S : Registers k) :
    (∃ j, run (seqFragment z B C).program ⟨seqLeft B C B.entry, R⟩ j =
      ⟨seqRight B C C.entry, S⟩ ∧
      ∀ t < j, InFirstComponent B C
        (run (seqFragment z B C).program ⟨seqLeft B C B.entry, R⟩ t).pc) ↔ Exec B R S := by
  exact ⟨seq_first_backward z B C R S,seq_first_forward z B C R S⟩

theorem seq_no_internal_halt {k : ℕ} (z : Fin k) (B C : Fragment k)
    (hB : NoInternalHalt B) (hC : NoInternalHalt C) : NoInternalHalt (seqFragment z B C) := by
  intro p
  cases p with
  | left p => cases h : B.code p <;> simp_all [NoInternalHalt, seqFragment, renameInstr]
  | right p => cases h : C.code p <;> simp_all [NoInternalHalt, seqFragment, renameInstr]
  | returnInc => simp [seqFragment]
  | returnDec => simp [seqFragment]

inductive RepeatReturns {k : ℕ} (r : Fin k) (B : Fragment k) : Registers k → Registers k → Prop
  | zero (R : Registers k) (h : R r = 0) : RepeatReturns r B R R
  | positive {R U S : Registers k} (h : 0 < R r)
      (hB : Exec B (updateRegister R r (R r - 1)) U)
      (hrest : RepeatReturns r B U S) : RepeatReturns r B R S

private def LoopSpec {k : ℕ} (r z : Fin k) (B : Fragment k) (S : Registers k) :
    Config k (Option (RepeatLabel B.Label)) → Prop
  | ⟨none,R⟩ => R=S
  | ⟨some .controller,R⟩ => RepeatReturns r B R S
  | ⟨some (.body p),R⟩ => ∃ U, Reaches B.program ⟨some p,R⟩ ⟨none,U⟩ ∧ RepeatReturns r B U S
  | ⟨some .returnInc,R⟩ => RepeatReturns r B R S
  | ⟨some .returnDec,R⟩ => RepeatReturns r B (updateRegister R z (R z-1)) S

private theorem loopSpec_body {k : ℕ} (r z : Fin k) (B : Fragment k)
    (p : Option B.Label) (R S : Registers k) :
    LoopSpec r z B S ⟨repeatBody B p,R⟩ ↔
      ∃ U, Reaches B.program ⟨p,R⟩ ⟨none,U⟩ ∧ RepeatReturns r B U S := by
  cases p with
  | none => simp [LoopSpec,repeatBody,exit_reaches]
  | some p => rfl

private theorem repeat_backward {k : ℕ} (r z : Fin k) (B : Fragment k) (R S : Registers k)
    (h : Exec (repeatFragment r z B) R S) : RepeatReturns r B R S := by
  have hh : LoopSpec r z B S ⟨some .controller,R⟩ := by
    apply backward_reaches (repeatFragment r z B).program _ ⟨none,S⟩ h (LoopSpec r z B S)
    · exact rfl
    · intro a b hab hb
      dsimp only [repeatFragment] at *
      cases a with
      | mk p A =>
        cases p with
        | none => simp [Step,step,Fragment.program] at hab
        | some p =>
          cases p with
          | body p =>
              cases hc : B.code p with
              | halt => simp [Step,step,Fragment.program,hc,renameInstr] at hab
              | inc t next =>
                  simp only [Step,step,Fragment.program,hc,renameInstr,id_eq] at hab
                  have he := Option.some.inj hab
                  subst b
                  obtain ⟨U,hU,hrest⟩ := (loopSpec_body r z B next _ _).mp hb
                  exact ⟨U,hU.head (by simp [Step,step,Fragment.program,hc]),hrest⟩
              | dec t positive zero =>
                  by_cases hz : A t=0
                  · simp only [Step,step,Fragment.program,hc,renameInstr,id_eq,hz,↓reduceIte] at hab
                    have he := Option.some.inj hab
                    subst b
                    obtain ⟨U,hU,hrest⟩ := (loopSpec_body r z B zero _ _).mp hb
                    exact ⟨U,hU.head (by simp [Step,step,Fragment.program,hc,hz]),hrest⟩
                  · simp only [Step,step,Fragment.program,hc,renameInstr,id_eq,hz,↓reduceIte] at hab
                    have he := Option.some.inj hab
                    subst b
                    obtain ⟨U,hU,hrest⟩ := (loopSpec_body r z B positive _ _).mp hb
                    exact ⟨U,hU.head (by simp [Step,step,Fragment.program,hc,hz]),hrest⟩
          | controller =>
              by_cases hz : A r=0
              · simp only [Step,step,Fragment.program,hz,↓reduceIte] at hab
                have he := Option.some.inj hab
                subst b
                have hb : A=S := hb
                subst S
                exact RepeatReturns.zero A hz
              · simp only [Step,step,Fragment.program,hz,↓reduceIte] at hab
                have he := Option.some.inj hab
                subst b
                obtain ⟨U,hU,hrest⟩ := (loopSpec_body r z B B.entry _ _).mp hb
                exact RepeatReturns.positive (by omega) hU hrest
          | returnInc =>
              simp only [Step,step,Fragment.program] at hab
              have he := Option.some.inj hab
              subst b
              simpa [LoopSpec,updateRegister] using hb
          | returnDec =>
              by_cases hz : A z=0
              · simp only [Step,step,Fragment.program,hz,↓reduceIte] at hab
                have he := Option.some.inj hab
                subst b
                have hu : updateRegister A z (A z-1)=A := by
                  funext t
                  by_cases ht : t=z <;> simp_all [updateRegister]
                change RepeatReturns r B (updateRegister A z (A z-1)) S
                rw [hu]
                exact hb
              · simp only [Step,step,Fragment.program,hz,↓reduceIte] at hab
                have he := Option.some.inj hab
                subst b
                exact hb
  exact hh

private theorem repeat_forward {k : ℕ} (r z : Fin k) (B : Fragment k) (R S : Registers k)
    (h : RepeatReturns r B R S) : Exec (repeatFragment r z B) R S := by
  let Q : Program k (Option (RepeatLabel B.Label)) := (repeatFragment r z B).program
  induction h with
  | zero R hz =>
      exact Relation.ReflTransGen.single (by simp [Step,step,Fragment.program,repeatFragment,hz])
  | @positive R U S hr hB hrest ih =>
      have hbody := lift_reaches B.program Q (repeatBody B)
        (by intro p hp;cases p with
            | none => exact False.elim (hp rfl)
            | some p => rfl) _ _ hB
      have hstart : Step Q ⟨some .controller,R⟩
          ⟨repeatBody B B.entry,updateRegister R r (R r-1)⟩ := by
        simp [Step,step,Q,Fragment.program,repeatFragment,Nat.ne_of_gt hr]
      have hreturn : Reaches Q ⟨some .returnInc,U⟩ ⟨some .controller,U⟩ := by
        apply (reaches_iff_run _ _ _).mpr
        refine ⟨2,?_⟩
        simp [run,advance,step,Q,Fragment.program,repeatFragment,updateRegister]
      exact (hbody.trans (hreturn.trans ih)).head hstart


theorem repeat_exec {k : ℕ} (r z : Fin k) (B : Fragment k) (R S : Registers k) :
    Exec (repeatFragment r z B) R S ↔ RepeatReturns r B R S := by
  exact ⟨repeat_backward r z B R S,repeat_forward r z B R S⟩

theorem repeat_no_internal_halt {k : ℕ} (r z : Fin k) (B : Fragment k)
    (hB : NoInternalHalt B) : NoInternalHalt (repeatFragment r z B) := by
  intro p
  cases p with
  | body p => cases h : B.code p <;> simp_all [NoInternalHalt, repeatFragment, renameInstr]
  | controller => simp [repeatFragment]
  | returnInc => simp [repeatFragment]
  | returnDec => simp [repeatFragment]

inductive SearchReturns {k : ℕ} (v : Fin k) (B P Z : Fragment k) : Registers k → Registers k → Prop
  | zero {R U S : Registers k} (hB : Exec B R U) (hv : U v = 0)
      (hZ : Exec Z U S) : SearchReturns v B P Z R S
  | positive {R U V S : Registers k} (hB : Exec B R U) (hv : 0 < U v)
      (hP : Exec P (updateRegister U v (U v - 1)) V)
      (hrest : SearchReturns v B P Z V S) : SearchReturns v B P Z R S

private def SearchNext {k : ℕ} (v : Fin k) (B P Z : Fragment k)
    (R S : Registers k) : Prop :=
  (R v=0 ∧ Exec Z R S) ∨ ∃ U, 0<R v ∧
    Exec P (updateRegister R v (R v-1)) U ∧ SearchReturns v B P Z U S

private def SearchSpec {k : ℕ} (v z : Fin k) (B P Z : Fragment k) (S : Registers k) :
    Config k (Option (SearchLabel B.Label P.Label Z.Label)) → Prop
  | ⟨none,R⟩ => R=S
  | ⟨some (.test p),R⟩ => ∃ U, Reaches B.program ⟨some p,R⟩ ⟨none,U⟩ ∧ SearchNext v B P Z U S
  | ⟨some (.positive p),R⟩ => ∃ U, Reaches P.program ⟨some p,R⟩ ⟨none,U⟩ ∧ SearchReturns v B P Z U S
  | ⟨some (.zero p),R⟩ => Reaches Z.program ⟨some p,R⟩ ⟨none,S⟩
  | ⟨some .branch,R⟩ => SearchNext v B P Z R S
  | ⟨some .testInc,R⟩ => SearchNext v B P Z R S
  | ⟨some .testDec,R⟩ => SearchNext v B P Z (updateRegister R z (R z-1)) S
  | ⟨some .loopInc,R⟩ => SearchReturns v B P Z R S
  | ⟨some .loopDec,R⟩ => SearchReturns v B P Z (updateRegister R z (R z-1)) S

private theorem searchSpec_test {k : ℕ} (v z : Fin k) (B P Z : Fragment k)
    (p : Option B.Label) (R S : Registers k) :
    SearchSpec v z B P Z S ⟨searchTest B P Z p,R⟩ ↔
      ∃ U, Reaches B.program ⟨p,R⟩ ⟨none,U⟩ ∧ SearchNext v B P Z U S := by
  cases p with
  | none => simp [SearchSpec,searchTest,exit_reaches]
  | some p => rfl

private theorem searchSpec_positive {k : ℕ} (v z : Fin k) (B P Z : Fragment k)
    (p : Option P.Label) (R S : Registers k) :
    SearchSpec v z B P Z S ⟨searchPositive B P Z p,R⟩ ↔
      ∃ U, Reaches P.program ⟨p,R⟩ ⟨none,U⟩ ∧ SearchReturns v B P Z U S := by
  cases p with
  | none => simp [SearchSpec,searchPositive,exit_reaches]
  | some p => rfl

private theorem searchSpec_zero {k : ℕ} (v z : Fin k) (B P Z : Fragment k)
    (p : Option Z.Label) (R S : Registers k) :
    SearchSpec v z B P Z S ⟨searchZero B P Z p,R⟩ ↔ Reaches Z.program ⟨p,R⟩ ⟨none,S⟩ := by
  cases p with
  | none => simp [SearchSpec,searchZero,exit_reaches]
  | some p => rfl

private theorem searchSpec_entry {k : ℕ} (v z : Fin k) (B P Z : Fragment k)
    (R S : Registers k) :
    SearchSpec v z B P Z S ⟨searchTest B P Z B.entry,R⟩ ↔ SearchReturns v B P Z R S := by
  rw [searchSpec_test]
  constructor
  · rintro ⟨U,hB,hn⟩
    rcases hn with ⟨hv,hZ⟩ | ⟨V,hv,hP,hrest⟩
    · exact .zero hB hv hZ
    · exact .positive hB hv hP hrest
  · intro h
    cases h with
    | zero hB hv hZ => exact ⟨_,hB,Or.inl ⟨hv,hZ⟩⟩
    | positive hB hv hP hrest => exact ⟨_,hB,Or.inr ⟨_,hv,hP,hrest⟩⟩

private theorem search_backward {k : ℕ} (v z : Fin k) (B P Z : Fragment k) (R S : Registers k)
    (h : Exec (searchFragment v z B P Z) R S) : SearchReturns v B P Z R S := by
  have hh : SearchSpec v z B P Z S ⟨searchTest B P Z B.entry,R⟩ := by
    apply backward_reaches (searchFragment v z B P Z).program _ ⟨none,S⟩ h (SearchSpec v z B P Z S)
    · exact rfl
    · intro a b hab hb
      dsimp only [searchFragment] at *
      cases a with
      | mk p A =>
        cases p with
        | none => simp [Step,step,Fragment.program] at hab
        | some p =>
          cases p with
          | test p =>
              cases hc : B.code p with
              | halt => simp [Step,step,Fragment.program,hc,renameInstr] at hab
              | inc t next =>
                  simp only [Step,step,Fragment.program,hc,renameInstr,id_eq] at hab
                  have he := Option.some.inj hab
                  subst b
                  obtain ⟨U,hU,hrest⟩ := (searchSpec_test v z B P Z next _ _).mp hb
                  exact ⟨U,hU.head (by simp [Step,step,Fragment.program,hc]),hrest⟩
              | dec t positive zero =>
                  by_cases hz : A t=0
                  · simp only [Step,step,Fragment.program,hc,renameInstr,id_eq,hz,↓reduceIte] at hab
                    have he := Option.some.inj hab
                    subst b
                    obtain ⟨U,hU,hrest⟩ := (searchSpec_test v z B P Z zero _ _).mp hb
                    exact ⟨U,hU.head (by simp [Step,step,Fragment.program,hc,hz]),hrest⟩
                  · simp only [Step,step,Fragment.program,hc,renameInstr,id_eq,hz,↓reduceIte] at hab
                    have he := Option.some.inj hab
                    subst b
                    obtain ⟨U,hU,hrest⟩ := (searchSpec_test v z B P Z positive _ _).mp hb
                    exact ⟨U,hU.head (by simp [Step,step,Fragment.program,hc,hz]),hrest⟩
          | positive p =>
              cases hc : P.code p with
              | halt => simp [Step,step,Fragment.program,hc,renameInstr] at hab
              | inc t next =>
                  simp only [Step,step,Fragment.program,hc,renameInstr,id_eq] at hab
                  have he := Option.some.inj hab
                  subst b
                  obtain ⟨U,hU,hrest⟩ := (searchSpec_positive v z B P Z next _ _).mp hb
                  exact ⟨U,hU.head (by simp [Step,step,Fragment.program,hc]),hrest⟩
              | dec t positive zero =>
                  by_cases hz : A t=0
                  · simp only [Step,step,Fragment.program,hc,renameInstr,id_eq,hz,↓reduceIte] at hab
                    have he := Option.some.inj hab
                    subst b
                    obtain ⟨U,hU,hrest⟩ := (searchSpec_positive v z B P Z zero _ _).mp hb
                    exact ⟨U,hU.head (by simp [Step,step,Fragment.program,hc,hz]),hrest⟩
                  · simp only [Step,step,Fragment.program,hc,renameInstr,id_eq,hz,↓reduceIte] at hab
                    have he := Option.some.inj hab
                    subst b
                    obtain ⟨U,hU,hrest⟩ := (searchSpec_positive v z B P Z positive _ _).mp hb
                    exact ⟨U,hU.head (by simp [Step,step,Fragment.program,hc,hz]),hrest⟩
          | zero p =>
              cases hc : Z.code p with
              | halt => simp [Step,step,Fragment.program,hc,renameInstr] at hab
              | inc t next =>
                  simp only [Step,step,Fragment.program,hc,renameInstr,id_eq] at hab
                  have he := Option.some.inj hab
                  subst b
                  exact ((searchSpec_zero v z B P Z next _ _).mp hb).head (by simp [Step,step,Fragment.program,hc])
              | dec t positive zero =>
                  by_cases hz : A t=0
                  · simp only [Step,step,Fragment.program,hc,renameInstr,id_eq,hz,↓reduceIte] at hab
                    have he := Option.some.inj hab
                    subst b
                    exact ((searchSpec_zero v z B P Z zero _ _).mp hb).head (by simp [Step,step,Fragment.program,hc,hz])
                  · simp only [Step,step,Fragment.program,hc,renameInstr,id_eq,hz,↓reduceIte] at hab
                    have he := Option.some.inj hab
                    subst b
                    exact ((searchSpec_zero v z B P Z positive _ _).mp hb).head (by simp [Step,step,Fragment.program,hc,hz])
          | branch =>
              by_cases hz : A v=0
              · simp only [Step,step,Fragment.program,hz,↓reduceIte] at hab
                have he := Option.some.inj hab
                subst b
                exact Or.inl ⟨hz,(searchSpec_zero v z B P Z Z.entry _ _).mp hb⟩
              · simp only [Step,step,Fragment.program,hz,↓reduceIte] at hab
                have he := Option.some.inj hab
                subst b
                obtain ⟨U,hU,hrest⟩ := (searchSpec_positive v z B P Z P.entry _ _).mp hb
                exact Or.inr ⟨U,by omega,hU,hrest⟩
          | testInc =>
              simp only [Step,step,Fragment.program] at hab
              have he := Option.some.inj hab
              subst b
              simpa [SearchSpec,updateRegister] using hb
          | loopInc =>
              simp only [Step,step,Fragment.program] at hab
              have he := Option.some.inj hab
              subst b
              simpa [SearchSpec,updateRegister] using hb
          | testDec =>
              by_cases hz : A z=0
              · simp only [Step,step,Fragment.program,hz,↓reduceIte] at hab
                have he := Option.some.inj hab
                subst b
                have hu : updateRegister A z (A z-1)=A := by
                  funext t
                  by_cases ht : t=z <;> simp_all [updateRegister]
                change SearchNext v B P Z (updateRegister A z (A z-1)) S
                rw [hu]
                exact hb
              · simp only [Step,step,Fragment.program,hz,↓reduceIte] at hab
                have he := Option.some.inj hab
                subst b
                exact hb
          | loopDec =>
              by_cases hz : A z=0
              · simp only [Step,step,Fragment.program,hz,↓reduceIte] at hab
                have he := Option.some.inj hab
                subst b
                have hu : updateRegister A z (A z-1)=A := by
                  funext t
                  by_cases ht : t=z <;> simp_all [updateRegister]
                change SearchReturns v B P Z (updateRegister A z (A z-1)) S
                rw [hu]
                exact (searchSpec_entry v z B P Z _ _).mp hb
              · simp only [Step,step,Fragment.program,hz,↓reduceIte] at hab
                have he := Option.some.inj hab
                subst b
                exact (searchSpec_entry v z B P Z _ _).mp hb
  obtain ⟨U,hB,hn⟩ := (searchSpec_test v z B P Z B.entry R S).mp hh
  rcases hn with ⟨hv,hZ⟩ | ⟨V,hv,hP,hrest⟩
  · exact .zero hB hv hZ
  · exact .positive hB hv hP hrest

private theorem search_forward {k : ℕ} (v z : Fin k) (B P Z : Fragment k) (R S : Registers k)
    (h : SearchReturns v B P Z R S) : Exec (searchFragment v z B P Z) R S := by
  let Q : Program k (Option (SearchLabel B.Label P.Label Z.Label)) := (searchFragment v z B P Z).program
  have testLift (R U : Registers k) (hB : Exec B R U) :
      Reaches Q ⟨searchTest B P Z B.entry,R⟩ ⟨some .branch,U⟩ := by
    have hb := lift_reaches B.program Q (searchTest B P Z)
      (by intro p hp;cases p with
          | none => exact False.elim (hp rfl)
          | some p => rfl) _ _ hB
    have hj : Reaches Q ⟨some .testInc,U⟩ ⟨some .branch,U⟩ := by
      apply (reaches_iff_run _ _ _).mpr
      exact ⟨2,by simp [run,advance,step,Q,Fragment.program,searchFragment,updateRegister]⟩
    exact hb.trans hj
  induction h with
  | @zero R U S hB hv hZ =>
      have hz := lift_reaches Z.program Q (searchZero B P Z)
        (by intro p hp;cases p with
            | none => exact False.elim (hp rfl)
            | some p => rfl) _ _ hZ
      have hs : Step Q ⟨some .branch,U⟩ ⟨searchZero B P Z Z.entry,U⟩ := by
        simp [Step,step,Q,Fragment.program,searchFragment,hv]
      exact (testLift R U hB).trans (hz.head hs)
  | @positive R U V S hB hv hP hrest ih =>
      have hp := lift_reaches P.program Q (searchPositive B P Z)
        (by intro p hp;cases p with
            | none => exact False.elim (hp rfl)
            | some p => rfl) _ _ hP
      have hs : Step Q ⟨some .branch,U⟩
          ⟨searchPositive B P Z P.entry,updateRegister U v (U v-1)⟩ := by
        simp [Step,step,Q,Fragment.program,searchFragment,Nat.ne_of_gt hv]
      have hj : Reaches Q ⟨some .loopInc,V⟩ ⟨searchTest B P Z B.entry,V⟩ := by
        apply (reaches_iff_run _ _ _).mpr
        exact ⟨2,by simp [run,advance,step,Q,Fragment.program,searchFragment,updateRegister]⟩
      exact (testLift R U hB).trans ((hp.trans (hj.trans ih)).head hs)


theorem search_exec {k : ℕ} (v z : Fin k) (B P Z : Fragment k) (R S : Registers k) :
    Exec (searchFragment v z B P Z) R S ↔ SearchReturns v B P Z R S := by
  exact ⟨search_backward v z B P Z R S,search_forward v z B P Z R S⟩

theorem search_no_internal_halt {k : ℕ} (v z : Fin k) (B P Z : Fragment k)
    (hB : NoInternalHalt B) (hP : NoInternalHalt P) (hZ : NoInternalHalt Z) :
    NoInternalHalt (searchFragment v z B P Z) := by
  intro p
  cases p with
  | test p => cases h : B.code p <;> simp_all [NoInternalHalt, searchFragment, renameInstr]
  | positive p => cases h : P.code p <;> simp_all [NoInternalHalt, searchFragment, renameInstr]
  | zero p => cases h : Z.code p <;> simp_all [NoInternalHalt, searchFragment, renameInstr]
  | branch => simp [searchFragment]
  | testInc => simp [searchFragment]
  | testDec => simp [searchFragment]
  | loopInc => simp [searchFragment]
  | loopDec => simp [searchFragment]


inductive SequenceReturns {k : ℕ} : List (Fragment k) → Registers k → Registers k → Prop
  | nil (R : Registers k) : SequenceReturns [] R R
  | cons {B : Fragment k} {bs : List (Fragment k)} {R U S : Registers k}
      (hB : Exec B R U) (hrest : SequenceReturns bs U S) : SequenceReturns (B :: bs) R S

theorem sequence_exec {k : ℕ} (z : Fin k) (bs : List (Fragment k)) (R S : Registers k) :
    Exec (sequence z bs) R S ↔ SequenceReturns bs R S := by
  induction bs generalizing R with
  | nil =>
      change Reaches (doneFragment k).program ⟨none,R⟩ ⟨none,S⟩ ↔ SequenceReturns [] R S
      rw [exit_reaches]
      constructor
      · rintro rfl
        exact .nil R
      · intro h
        cases h
        rfl
  | cons B bs ih =>
      rw [sequence,seq_exec]
      constructor
      · rintro ⟨U,hB,hrest⟩
        exact .cons hB ((ih U).mp hrest)
      · intro h
        cases h with
        | cons hB hrest => exact ⟨_,hB,(ih _).mpr hrest⟩

theorem sequence_no_internal_halt {k : ℕ} (z : Fin k) (bs : List (Fragment k))
    (hbs : ∀ B ∈ bs, NoInternalHalt B) : NoInternalHalt (sequence z bs) := by
  induction bs with
  | nil => intro p; exact Empty.elim p
  | cons B bs ih =>
      exact seq_no_internal_halt z B (sequence z bs) (hbs B (by simp))
        (ih (fun C hC => hbs C (by simp [hC])))

end Lemmatheca.ComputabilityTheory.RecursiveTapeCompiler
