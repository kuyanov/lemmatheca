import Lemmatheca.CounterProgramsOnTape.CounterPrograms

namespace Lemmatheca.ComputabilityTheory.CounterPrograms

abbrev Symbol (k : ℕ) := Bool × (Fin k → Bool)

def blank {k : ℕ} : Symbol k := (false, fun _ => false)
def mark {k : ℕ} (i : Fin k) : Symbol k := (false, fun r => decide (r = i))

theorem mark_ne_blank {k : ℕ} (i : Fin k) : mark i ≠ blank := by
  intro h
  have hb := congrArg (fun a : Symbol k => a.2 i) h
  simp [mark, blank] at hb

def alphabet {k : ℕ} (i : Fin k) : TuringMachines.Alphabet (Symbol k) :=
  ⟨blank, mark i, mark_ne_blank i⟩

def setBit {k : ℕ} (a : Symbol k) (r : Fin k) (b : Bool) : Symbol k :=
  (a.1, Function.update a.2 r b)
def setOrigin {k : ℕ} (a : Symbol k) : Symbol k := (true, a.2)
def clearOrigin {k : ℕ} (a : Symbol k) : Symbol k := (false, a.2)
def outputProjection {k : ℕ} (i o : Fin k) (a : Symbol k) : Symbol k :=
  (false, fun r => if r = i then a.2 o else false)
def anyBit {k : ℕ} (a : Symbol k) : Bool := decide (∃ r : Fin k, a.2 r = true)

theorem symbol_card (k : ℕ) : Fintype.card (Symbol k) = 2 ^ (k + 1) := by
  simp [Symbol, pow_succ, Nat.mul_comm]

theorem setBit_spec {k : ℕ} (a : Symbol k) (r : Fin k) (b : Bool) :
    (setBit a r b).1 = a.1 ∧ (setBit a r b).2 r = b ∧
    ∀ s, s ≠ r → (setBit a r b).2 s = a.2 s := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [setBit]
  · intro s hs
    simp [setBit, hs]

theorem outputProjection_spec {k : ℕ} (i o : Fin k) (a : Symbol k) :
    outputProjection i o a = if a.2 o then mark i else blank := by
  apply Prod.ext
  · cases h : a.2 o <;> rfl
  · funext r
    by_cases hr : r = i <;> cases h : a.2 o <;>
      simp [outputProjection, mark, blank, hr, h]

def maxRegister {k : ℕ} (R : Registers k) : ℕ := Finset.univ.sup R

theorem maxRegister_spec {k : ℕ} (hk : 0 < k) (R : Registers k) :
    (∀ r, R r ≤ maxRegister R) ∧ ∃ r, R r = maxRegister R := by
  constructor
  · intro r
    exact Finset.le_sup (Finset.mem_univ r)
  · obtain ⟨r, _, hr⟩ := Finset.exists_mem_eq_sup
      (Finset.univ : Finset (Fin k)) ⟨⟨0, hk⟩, Finset.mem_univ _⟩ R
    exact ⟨r, hr.symm⟩

def boundaryCell {k : ℕ} (R : Registers k) (z : ℤ) : Symbol k :=
  (decide (z = 0), fun r => decide (0 ≤ z ∧ z < (R r : ℤ)))

theorem boundary_support {k : ℕ} (R : Registers k) :
    {z | boundaryCell R z ≠ blank} ⊆ ({0} : Set ℤ) ∪ Set.Ico 0 (maxRegister R : ℤ) := by
  intro z hz
  by_contra hn
  change ¬ (z = 0 ∨ (0 ≤ z ∧ z < (maxRegister R : ℤ))) at hn
  have hz0 : z ≠ 0 := fun h => hn (Or.inl h)
  have hbits (r : Fin k) : ¬ (0 ≤ z ∧ z < (R r : ℤ)) := by
    intro h
    have hb : (R r : ℤ) ≤ (maxRegister R : ℤ) :=
      Int.ofNat_le.mpr (Finset.le_sup (Finset.mem_univ r))
    exact hn (Or.inr ⟨h.1, lt_of_lt_of_le h.2 hb⟩)
  apply hz
  apply Prod.ext
  · simp [boundaryCell, blank, hz0]
  · funext r
    simpa [boundaryCell, blank] using hbits r

def boundaryTape {k : ℕ} (i : Fin k) (R : Registers k) :
    TuringMachines.Tape (Symbol k) (alphabet i).blank :=
  ⟨boundaryCell R, ((Set.finite_singleton 0).union (Set.finite_Ico _ _)).subset
    (boundary_support R)⟩

private theorem tape_ext {β : Type*} {b : β}
    {t u : TuringMachines.Tape β b} (h : ∀ z, t z = u z) : t = u := by
  cases t with
  | mk t ht =>
    cases u with
    | mk u hu =>
      have he : t = u := funext h
      cases he
      rfl

theorem boundary_write_inc {k : ℕ} (i r : Fin k) (R : Registers k) :
    (boundaryTape i R).write (R r : ℤ) (setBit (boundaryCell R (R r)) r true) =
      boundaryTape i (updateRegister R r (R r + 1)) := by
  classical
  apply tape_ext
  intro z
  change Function.update (boundaryCell R) (R r : ℤ)
    (setBit (boundaryCell R (R r)) r true) z =
      boundaryCell (updateRegister R r (R r + 1)) z
  by_cases hz : z = (R r : ℤ)
  · subst z
    simp only [Function.update_self]
    apply Prod.ext
    · rfl
    · funext s
      by_cases hs : s = r
      · subst s
        simp [setBit, boundaryCell, updateRegister]
      · simp [setBit, boundaryCell, updateRegister, hs]
  · rw [Function.update_of_ne hz]
    apply Prod.ext
    · rfl
    · funext s
      by_cases hs : s = r
      · subst s
        simp only [boundaryCell, updateRegister, Function.update_self]
        have h : (0 ≤ z ∧ z < (R r : ℤ)) ↔
            (0 ≤ z ∧ z < ((R r + 1 : ℕ) : ℤ)) := by omega
        simp only [h]
      · simp [boundaryCell, updateRegister, hs]

theorem boundary_write_dec {k : ℕ} (i r : Fin k) (R : Registers k) (hn : 0 < R r) :
    (boundaryTape i R).write ((R r : ℤ) - 1)
      (setBit (boundaryCell R ((R r : ℤ) - 1)) r false) =
      boundaryTape i (updateRegister R r (R r - 1)) := by
  classical
  have hcast : ((R r - 1 : ℕ) : ℤ) = (R r : ℤ) - 1 := by omega
  apply tape_ext
  intro z
  change Function.update (boundaryCell R) ((R r : ℤ) - 1)
    (setBit (boundaryCell R ((R r : ℤ) - 1)) r false) z =
      boundaryCell (updateRegister R r (R r - 1)) z
  by_cases hz : z = (R r : ℤ) - 1
  · subst z
    simp only [Function.update_self]
    apply Prod.ext
    · rfl
    · funext s
      by_cases hs : s = r
      · subst s
        simp [setBit, boundaryCell, updateRegister, hn]
      · simp [setBit, boundaryCell, updateRegister, hs]
  · rw [Function.update_of_ne hz]
    apply Prod.ext
    · rfl
    · funext s
      by_cases hs : s = r
      · subst s
        simp only [boundaryCell, updateRegister, Function.update_self]
        have h : (0 ≤ z ∧ z < (R r : ℤ)) ↔
            (0 ≤ z ∧ z < ((R r - 1 : ℕ) : ℤ)) := by
          rw [hcast]
          omega
        simp only [h]
      · simp [boundaryCell, updateRegister, hs]

def Frame {k : ℕ} (R : Registers k) (r : Fin k)
    (t : TuringMachines.Tape (Symbol k) blank) : Prop :=
  ∀ z, (t z).1 = (boundaryCell R z).1 ∧
    ∀ s, s ≠ r → (t z).2 s = (boundaryCell R z).2 s

def cleanedAboveCell {k : ℕ} (i o : Fin k) (R : Registers k) (h z : ℤ) : Symbol k :=
  if h < z then outputProjection i o (boundaryCell R z) else boundaryCell R z

theorem cleanedAbove_support {k : ℕ} (i o : Fin k) (R : Registers k) (h : ℤ) :
    {z | cleanedAboveCell i o R h z ≠ blank} ⊆ {z | boundaryCell R z ≠ blank} := by
  intro z hz hn
  apply hz
  have hb : boundaryCell R z = blank := by simpa using hn
  by_cases hh : h < z
  · simp [cleanedAboveCell, hh, hb, outputProjection, blank]
  · simp [cleanedAboveCell, hh, hb]

def cleanedAboveTape {k : ℕ} (i o : Fin k) (R : Registers k) (h : ℤ) :
    TuringMachines.Tape (Symbol k) (alphabet i).blank :=
  ⟨cleanedAboveCell i o R h,
    (boundaryTape i R).finite_support.subset (cleanedAbove_support i o R h)⟩

theorem projection_boundary {k : ℕ} (i o : Fin k) (R : Registers k) (z : ℤ) :
    outputProjection i o (boundaryCell R z) =
      TuringMachines.unaryTape (alphabet i) (R o) z := by
  rw [outputProjection_spec]
  simp [boundaryCell, TuringMachines.unaryTape, alphabet]

end Lemmatheca.ComputabilityTheory.CounterPrograms
