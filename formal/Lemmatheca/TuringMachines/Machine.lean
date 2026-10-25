import Lemmatheca.TuringMachines.Tape

namespace Lemmatheca.ComputabilityTheory.TuringMachines

structure Machine {Γ : Type*} (A : Alphabet Γ) (Q : Type*) [Fintype Γ] [Fintype Q] where
  initial : Q
  table : Q → Γ → Option (Q × Γ × Move)

variable {Γ Q : Type*} {A : Alphabet Γ} [Fintype Γ] [Fintype Q]

noncomputable def step (T : Machine A Q) (C : Config A Q) : Option (Config A Q) :=
  (T.table C.state (C.tape C.head)).map fun r =>
    ⟨r.1, C.head + r.2.2.displacement, C.tape.write C.head r.2.1⟩

def Halted (T : Machine A Q) (C : Config A Q) : Prop :=
  T.table C.state (C.tape C.head) = none

def Step (T : Machine A Q) (C D : Config A Q) : Prop := step T C = some D

noncomputable def advance (T : Machine A Q) (C : Config A Q) : Config A Q :=
  (step T C).getD C

noncomputable def run (T : Machine A Q) (C : Config A Q) : ℕ → Config A Q
  | 0 => C
  | k + 1 => advance T (run T C k)

def ActualRun (T : Machine A Q) (r : ℕ) (D : Fin (r + 1) → Config A Q) : Prop :=
  ∀ i : Fin r, Step T (D i.castSucc) (D i.succ)

def HaltingTime (T : Machine A Q) (C : Config A Q) (k : ℕ) : Prop :=
  Halted T (run T C k)

def FirstHaltingTime (T : Machine A Q) (C : Config A Q) (k : ℕ) : Prop :=
  HaltingTime T C k ∧ ∀ j < k, ¬ HaltingTime T C j

def visited (T : Machine A Q) (C : Config A Q) (k : ℕ) : Set ℤ :=
  {z | ∃ i ≤ k, (run T C i).head = z}

private theorem halted_step_none (T : Machine A Q) (C : Config A Q) :
    Halted T C ↔ step T C = none := by
  simp [Halted, step]

private theorem advance_halted (T : Machine A Q) (C : Config A Q)
    (h : Halted T C) : advance T C = C := by
  simp [advance, (halted_step_none T C).mp h]

private theorem advance_cases (T : Machine A Q) (C : Config A Q) :
    (Halted T C ∧ advance T C = C) ∨ Step T C (advance T C) := by
  cases hs : step T C with
  | none => exact Or.inl ⟨(halted_step_none T C).mpr hs, by simp [advance, hs]⟩
  | some D => exact Or.inr (by simp [Step, advance, hs])

theorem exists_first_halting (T : Machine A Q) (C : Config A Q)
    (h : ∃ k, HaltingTime T C k) : ∃ k, FirstHaltingTime T C k := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun j hj => Nat.find_min h hj⟩

theorem run_actual_prefix (T : Machine A Q) (C : Config A Q) (r : ℕ)
    (h : ∀ i < r, ¬ Halted T (run T C i)) :
    ActualRun T r (fun i => run T C i.val) := by
  intro i
  change step T (run T C i.val) = some (advance T (run T C i.val))
  exact (advance_cases T (run T C i.val)).resolve_left (fun hh => h i.val i.isLt hh.1)

theorem step_deterministic (T : Machine A Q) (C D E : Config A Q)
    (hD : Step T C D) (hE : Step T C E) : D = E := by
  exact Option.some.inj (hD.symm.trans hE)

theorem halted_no_step (T : Machine A Q) (C : Config A Q) :
    Halted T C ↔ step T C = none := by
  exact halted_step_none T C

theorem step_locality (T : Machine A Q) (C D : Config A Q) (h : Step T C D) :
    |D.head - C.head| ≤ 1 ∧ ∀ z ≠ C.head, D.tape z = C.tape z := by
  classical
  unfold Step step at h
  cases hr : T.table C.state (C.tape C.head) with
  | none => simp [hr] at h
  | some r =>
    simp only [hr, Option.map_some, Option.some.injEq] at h
    subst D
    constructor
    · cases r with
      | mk q r => cases r with
        | mk b m => cases m <;> norm_num [Move.displacement]
    · intro z hz
      exact Function.update_of_ne hz _ _

theorem actualRun_agrees (T : Machine A Q) (r : ℕ)
    (D : Fin (r + 1) → Config A Q) (hD : ActualRun T r D) :
    ∀ i : Fin (r + 1), D i = run T (D 0) i.val := by
  have aux : ∀ j (hj : j < r + 1), D ⟨j, hj⟩ = run T (D 0) j := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      have hjr : j < r := by omega
      have hs := hD ⟨j, hjr⟩
      change step T (D ⟨j, by omega⟩) = some (D ⟨j + 1, hj⟩) at hs
      rw [ih] at hs
      change D ⟨j + 1, hj⟩ = advance T (run T (D 0) j)
      simp [advance, hs]
  intro i
  exact aux i.val i.isLt

theorem run_halted_add (T : Machine A Q) (C : Config A Q) (k j : ℕ)
    (hk : Halted T (run T C k)) : run T C (k + j) = run T C k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ, run, ih]
    exact advance_halted T _ hk

theorem halting_configs_equal (T : Machine A Q) (C : Config A Q) (k l : ℕ)
    (hk : Halted T (run T C k)) (hl : Halted T (run T C l)) :
    run T C k = run T C l := by
  rcases le_total k l with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    exact (run_halted_add T C k j hk).symm
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    exact run_halted_add T C l j hl

theorem run_head_bound (T : Machine A Q) (C : Config A Q) (i : ℕ) :
    |(run T C i).head - C.head| ≤ (i : ℤ) := by
  induction i with
  | zero => simp [run]
  | succ i ih =>
    have hs : |(advance T (run T C i)).head - (run T C i).head| ≤ 1 := by
      rcases advance_cases T (run T C i) with h | h
      · rw [h.2]; simp
      · exact (step_locality T _ _ h).1
    have hsa := abs_le.mp hs
    have hi := abs_le.mp ih
    change |(advance T (run T C i)).head - C.head| ≤ ((i + 1 : ℕ) : ℤ)
    apply abs_le.mpr
    push_cast
    omega

theorem visited_interval (T : Machine A Q) (C : Config A Q) (k : ℕ) :
    visited T C k ⊆ Set.Icc (C.head - k) (C.head + k) := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := hz
  have hb := abs_le.mp (run_head_bound T C i)
  constructor <;> omega

theorem visited_finite (T : Machine A Q) (C : Config A Q) (k : ℕ) :
    (visited T C k).Finite := by
  exact (Set.finite_Icc _ _).subset (visited_interval T C k)

theorem interval_card (h : ℤ) (k : ℕ) :
    (Set.Icc (h - (k : ℤ)) (h + k)).ncard = 2 * k + 1 := by
  rw [Set.ncard_Icc, Int.card_Icc]
  omega

theorem run_tape_outside (T : Machine A Q) (C : Config A Q) (k : ℕ) (z : ℤ)
    (hz : z ∉ Set.Icc (C.head - k) (C.head + k)) :
    (run T C k).tape z = C.tape z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hsmall : z ∉ Set.Icc (C.head - (k : ℤ)) (C.head + k) := by
      intro hh
      apply hz
      constructor <;> simp only [Set.mem_Icc] at hh <;> push_cast <;> omega
    have hne : z ≠ (run T C k).head := by
      intro he
      apply hz
      have hb := abs_le.mp (run_head_bound T C k)
      rw [he]
      constructor <;> push_cast <;> omega
    change (advance T (run T C k)).tape z = C.tape z
    rcases advance_cases T (run T C k) with hh | hs
    · rw [hh.2]
      exact ih hsmall
    · exact ((step_locality T _ _ hs).2 z hne).trans (ih hsmall)

theorem run_support (T : Machine A Q) (C : Config A Q) (k : ℕ) :
    (run T C k).tape.support ⊆ C.tape.support ∪ Set.Icc (C.head - k) (C.head + k) := by
  intro z hz
  by_cases hi : z ∈ Set.Icc (C.head - k) (C.head + k)
  · exact Or.inr hi
  · left
    change C.tape z ≠ A.blank
    change (run T C k).tape z ≠ A.blank at hz
    rwa [run_tape_outside T C k z hi] at hz

theorem actualRun_region (T : Machine A Q) (r : ℕ)
    (D : Fin (r + 1) → Config A Q) (hD : ActualRun T r D) :
    (∀ i : Fin (r + 1), |(D i).head - (D 0).head| ≤ (i.val : ℤ)) ∧
    (∀ z ∉ Set.Icc ((D 0).head - r) ((D 0).head + r),
      (D (Fin.last r)).tape z = (D 0).tape z) ∧
    (D (Fin.last r)).tape.support ⊆
      (D 0).tape.support ∪ Set.Icc ((D 0).head - r) ((D 0).head + r) := by
  have ha := actualRun_agrees T r D hD
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [ha i]
    exact run_head_bound T (D 0) i.val
  · intro z hz
    rw [ha (Fin.last r)]
    exact run_tape_outside T (D 0) r z hz
  · rw [ha (Fin.last r)]
    exact run_support T (D 0) r

end Lemmatheca.ComputabilityTheory.TuringMachines
