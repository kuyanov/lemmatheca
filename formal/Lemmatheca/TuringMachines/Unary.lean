import Lemmatheca.TuringMachines.Machine
import Lemmatheca.FiniteDescriptionsAndDecisionProblems.Decisions

namespace Lemmatheca.ComputabilityTheory.TuringMachines

variable {Γ Q : Type*} (A : Alphabet Γ)

def unaryTape (n : ℕ) : Tape Γ A.blank := by
  refine ⟨fun z => if 0 ≤ z ∧ z < (n : ℤ) then A.mark else A.blank, ?_⟩
  apply (Set.finite_Ico (0 : ℤ) (n : ℤ)).subset
  intro z hz
  by_contra hn
  exact hz (ite_eq_right hn)

def input [Fintype Γ] [Fintype Q] (T : Machine A Q) (n : ℕ) : Config A Q :=
  ⟨T.initial, 0, unaryTape A n⟩

theorem unary_support (n : ℕ) : (unaryTape A n).support = Set.Ico 0 (n : ℤ) := by
  ext z
  change ((if 0 ≤ z ∧ z < (n : ℤ) then A.mark else A.blank) ≠ A.blank) ↔
    0 ≤ z ∧ z < (n : ℤ)
  by_cases hz : 0 ≤ z ∧ z < (n : ℤ)
  · simp [hz, A.mark_ne_blank]
  · simp [hz]

theorem readout_exists (C : Config A Q) :
    ∃ r : ℕ, C.tape (C.head + r) ≠ A.mark := by
  obtain ⟨B, hB⟩ := C.tape.support_bounded
  refine ⟨B + C.head.natAbs + 1, ?_⟩
  have hlow := (abs_le.mp (le_refl |C.head|)).1
  have hlow' : -(C.head.natAbs : ℤ) ≤ C.head := by
    simpa only [Int.natCast_natAbs] using hlow
  have hblank : C.tape (C.head + ((B + C.head.natAbs + 1 : ℕ) : ℤ)) = A.blank := by
    by_contra hn
    have hb := (hB _ hn).2
    push_cast at hb
    omega
  intro he
  exact A.mark_ne_blank (he.symm.trans hblank)

noncomputable def readout (C : Config A Q) : ℕ := by
  classical
  exact Nat.find (readout_exists A C)

theorem readout_spec (C : Config A Q) :
    C.tape (C.head + readout A C) ≠ A.mark ∧
    ∀ r < readout A C, C.tape (C.head + r) = A.mark := by
  classical
  refine ⟨Nat.find_spec (readout_exists A C), ?_⟩
  intro r hr
  exact Classical.not_not.mp (Nat.find_min (readout_exists A C) hr)

theorem input_readout [Fintype Γ] [Fintype Q] (T : Machine A Q) (n : ℕ) :
    readout A (input A T n) = n := by
  classical
  apply (Nat.find_eq_iff (readout_exists A (input A T n))).mpr
  constructor
  · simp [input, unaryTape, A.mark_ne_blank.symm]
  · intro r hr
    have hr' : (r : ℤ) < (n : ℤ) := by exact_mod_cast hr
    simp [input, unaryTape, hr']

theorem head_readouts (q : Q) (t : Tape Γ A.blank)
    (ht : ∀ z, t z = A.mark ↔ z = 0 ∨ z = 1) :
    readout A (⟨q, 0, t⟩ : Config A Q) = 2 ∧
    readout A (⟨q, 1, t⟩ : Config A Q) = 1 ∧
    readout A (⟨q, 2, t⟩ : Config A Q) = 0 := by
  classical
  have eq_readout (C : Config A Q) (r : ℕ)
      (hs : C.tape (C.head + r) ≠ A.mark)
      (hb : ∀ s < r, C.tape (C.head + s) = A.mark) : readout A C = r := by
    apply (Nat.find_eq_iff (readout_exists A C)).mpr
    exact ⟨hs, fun s hh hn => hn (hb s hh)⟩
  refine ⟨?_, ?_, ?_⟩
  · apply eq_readout
    · change t (0 + (2 : ℤ)) ≠ A.mark
      simp [ht]
    · intro r hr
      change t (0 + (r : ℤ)) = A.mark
      rw [ht]
      omega
  · apply eq_readout
    · change t (1 + (1 : ℤ)) ≠ A.mark
      simp [ht]
    · intro r hr
      change t (1 + (r : ℤ)) = A.mark
      rw [ht]
      omega
  · apply eq_readout
    · change t (2 + (0 : ℤ)) ≠ A.mark
      simp [ht]
    · intro r hr
      omega

variable {A}

def Output [Fintype Γ] [Fintype Q] (T : Machine A Q) (n m : ℕ) : Prop :=
  ∃ k, Halted T (run T (input A T n) k) ∧ readout A (run T (input A T n) k) = m

theorem output_unique [Fintype Γ] [Fintype Q] (T : Machine A Q) (n a b : ℕ)
    (ha : Output T n a) (hb : Output T n b) : a = b := by
  obtain ⟨k, hk, hka⟩ := ha
  obtain ⟨l, hl, hlb⟩ := hb
  have he := halting_configs_equal T (input A T n) k l hk hl
  rw [he] at hka
  exact hka.symm.trans hlb

noncomputable def computed [Fintype Γ] [Fintype Q] (T : Machine A Q) (n : ℕ) : Option ℕ :=
  FiniteDescriptions.familyFromGraph (fun _ x y => Output T x y) 0 n

theorem computed_spec [Fintype Γ] [Fintype Q] (T : Machine A Q) (n m : ℕ) :
    computed T n = some m ↔ Output T n m := by
  apply FiniteDescriptions.familyFromGraph_spec
  intro e x a b ha hb
  exact output_unique T x a b ha hb

end Lemmatheca.ComputabilityTheory.TuringMachines
