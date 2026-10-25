import Lemmatheca.CodingTuringComputations.Labeling
import Lemmatheca.CodingTuringComputations.Data

namespace Lemmatheca.ComputabilityTheory.TapeCoding

open TuringMachines (Alphabet Config)

variable {Γ Q : Type*} {A : Alphabet Γ} [Fintype Γ] [Fintype Q]
variable {T : TuringMachines.Machine A Q}

def Represents (L : Labeling T) (X : Config A Q) (c : ℕ) : Prop :=
  Valid (Fintype.card Γ) (Fintype.card Q) c ∧
  stateCode c = (L.state X.state).val ∧ currentCode c = (L.symbol (X.tape X.head)).val ∧
  (∀ i : ℕ, FiniteSequenceCoding.entry (leftCode c) i =
    (L.symbol (X.tape (X.head - (i : ℤ) - 1))).val) ∧
  (∀ i : ℕ, FiniteSequenceCoding.entry (rightCode c) i =
    (L.symbol (X.tape (X.head + (i : ℤ) + 1))).val)

noncomputable def supportRadius (X : Config A Q) : ℕ :=
  X.tape.finite_support.toFinset.sup Int.natAbs + X.head.natAbs + 1

noncomputable def leftList (L : Labeling T) (X : Config A Q) : List ℕ :=
  (List.range (supportRadius X)).map fun i => (L.symbol (X.tape (X.head - (i : ℤ) - 1))).val

noncomputable def rightList (L : Labeling T) (X : Config A Q) : List ℕ :=
  (List.range (supportRadius X)).map fun i => (L.symbol (X.tape (X.head + (i : ℤ) + 1))).val

noncomputable def encodeGlobal (L : Labeling T) (X : Config A Q) : ℕ :=
  pack (L.state X.state).val (L.symbol (X.tape X.head)).val
    (FiniteSequenceCoding.code (leftList L X)) (FiniteSequenceCoding.code (rightList L X))

private theorem range_entry (f : ℕ → ℕ) (B i : ℕ) :
    FiniteSequenceCoding.entry (FiniteSequenceCoding.code ((List.range B).map f)) i =
      if i < B then f i else 0 := by
  by_cases hi : i < B <;> simp [FiniteSequenceCoding.entry_code, hi]

omit [Fintype Γ] [Fintype Q] in
private theorem support_abs_bound (X : Config A Q) (z : ℤ) (hz : X.tape z ≠ A.blank) :
    -((X.tape.finite_support.toFinset.sup Int.natAbs : ℕ) : ℤ) ≤ z ∧
      z ≤ (X.tape.finite_support.toFinset.sup Int.natAbs : ℕ) := by
  have hm : z ∈ X.tape.finite_support.toFinset := by simpa using hz
  have hb := Int.ofNat_le.mpr (Finset.le_sup (f := Int.natAbs) hm)
  have hp := Int.le_natAbs (a := z)
  have hn := Int.le_natAbs (a := -z)
  simp only [Int.natAbs_neg] at hn
  omega

omit [Fintype Γ] [Fintype Q] in
private theorem outside_sides (X : Config A Q) (i : ℕ) (hi : supportRadius X ≤ i) :
    X.tape (X.head - (i : ℤ) - 1) = A.blank ∧
      X.tape (X.head + (i : ℤ) + 1) = A.blank := by
  have hi' := Int.ofNat_le.mpr hi
  simp only [supportRadius, Nat.cast_add, Nat.cast_one] at hi'
  have hp := Int.le_natAbs (a := X.head)
  have hn := Int.le_natAbs (a := -X.head)
  simp only [Int.natAbs_neg] at hn
  constructor <;> by_contra h
  · have hb := support_abs_bound X _ h; omega
  · have hb := support_abs_bound X _ h; omega

theorem encodeGlobal_represents (L : Labeling T) (X : Config A Q) :
    Represents L X (encodeGlobal L X) := by
  have hl (i : ℕ) : FiniteSequenceCoding.entry (FiniteSequenceCoding.code (leftList L X)) i =
      (L.symbol (X.tape (X.head - (i : ℤ) - 1))).val := by
    simp only [leftList, List.bind_eq_flatMap]
    change FiniteSequenceCoding.entry (FiniteSequenceCoding.code
      (((List.range (supportRadius X)).flatMap (pure ∘ Int.ofNat)).map
        (fun z : ℤ => (L.symbol (X.tape (X.head - z - 1))).val))) i = _
    rw [List.flatMap_pure_eq_map, List.map_map, range_entry]
    split_ifs with hi
    · rfl
    · rw [(outside_sides X i (by omega)).1, L.blank_zero]
  have hr (i : ℕ) : FiniteSequenceCoding.entry (FiniteSequenceCoding.code (rightList L X)) i =
      (L.symbol (X.tape (X.head + (i : ℤ) + 1))).val := by
    simp only [rightList, List.bind_eq_flatMap]
    change FiniteSequenceCoding.entry (FiniteSequenceCoding.code
      (((List.range (supportRadius X)).flatMap (pure ∘ Int.ofNat)).map
        (fun z : ℤ => (L.symbol (X.tape (X.head + z + 1))).val))) i = _
    rw [List.flatMap_pure_eq_map, List.map_map, range_entry]
    split_ifs with hi
    · rfl
    · rw [(outside_sides X i (by omega)).2, L.blank_zero]
  unfold Represents
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Valid, encodeGlobal, pack, stateCode, currentCode, leftCode,
      rightCode, Nat.unpair_pair]
    refine ⟨(L.state X.state).isLt, (L.symbol (X.tape X.head)).isLt, ?_, ?_⟩
    · intro i _; rw [hl]; exact Fin.isLt _
    · intro i _; rw [hr]; exact Fin.isLt _
  · exact (pack_fields _ _ _ _).1
  · exact (pack_fields _ _ _ _).2.1
  · intro i
    simpa only [encodeGlobal, pack, leftCode, Nat.unpair_pair] using hl i
  · intro i
    simpa only [encodeGlobal, pack, rightCode, Nat.unpair_pair] using hr i

def decodeSymbol (L : Labeling T) (n : ℕ) : Γ :=
  if h : n < Fintype.card Γ then L.symbol.symm ⟨n, h⟩ else A.blank

def decodeState (L : Labeling T) (n : ℕ) : Q :=
  if h : n < Fintype.card Q then L.state.symm ⟨n, h⟩ else T.initial

def realizedCells (L : Labeling T) (c : ℕ) (h z : ℤ) : Γ :=
  if z = h then decodeSymbol L (currentCode c)
  else if z < h then decodeSymbol L (FiniteSequenceCoding.entry (leftCode c) (h - z - 1).toNat)
  else decodeSymbol L (FiniteSequenceCoding.entry (rightCode c) (z - h - 1).toNat)

private theorem decode_zero (L : Labeling T) : decodeSymbol L 0 = A.blank := by
  conv_lhs => rw [← L.blank_zero]
  simp [decodeSymbol]

private theorem symbol_decode (L : Labeling T) (n : ℕ) (hn : n < Fintype.card Γ) :
    (L.symbol (decodeSymbol L n)).val = n := by
  simp [decodeSymbol, hn]

theorem realizedCells_support (L : Labeling T) (c : ℕ) (h : ℤ) :
    {z | realizedCells L c h z ≠ A.blank} ⊆
      Set.Icc (h - FiniteSequenceCoding.length (leftCode c))
        (h + FiniteSequenceCoding.length (rightCode c)) := by
  intro z hz
  change realizedCells L c h z ≠ A.blank at hz
  constructor
  · by_contra hb
    have he : z ≠ h := by omega
    have hl : z < h := by omega
    have hi : FiniteSequenceCoding.length (leftCode c) ≤ (h - z - 1).toNat := by omega
    simp only [realizedCells, ite_eq_right he, ite_eq_left hl] at hz
    rw [FiniteSequenceCoding.entry_out_of_range _ _ hi, decode_zero] at hz
    exact hz rfl
  · by_contra hb
    have he : z ≠ h := by omega
    have hl : ¬ z < h := by omega
    have hi : FiniteSequenceCoding.length (rightCode c) ≤ (z - h - 1).toNat := by omega
    simp only [realizedCells, ite_eq_right he, ite_eq_right hl] at hz
    rw [FiniteSequenceCoding.entry_out_of_range _ _ hi, decode_zero] at hz
    exact hz rfl

def realize (L : Labeling T) (c : ℕ) (h : ℤ) : Config A Q where
  state := decodeState L (stateCode c)
  head := h
  tape := ⟨realizedCells L c h,
    (Set.finite_Icc _ _).subset (realizedCells_support L c h)⟩

theorem realize_represents (L : Labeling T) (c : ℕ) (h : ℤ)
    (hc : Valid (Fintype.card Γ) (Fintype.card Q) c) :
    (realize L c h).head = h ∧ Represents L (realize L c h) c := by
  have hg : 0 < Fintype.card Γ := lt_of_lt_of_le (by decide : 0 < 2) (cardinal_bounds T).1
  have hall (d : ℕ) (hd : ∀ i < FiniteSequenceCoding.length d,
      FiniteSequenceCoding.entry d i < Fintype.card Γ) (i : ℕ) :
      FiniteSequenceCoding.entry d i < Fintype.card Γ := by
    by_cases hi : i < FiniteSequenceCoding.length d
    · exact hd i hi
    · rw [FiniteSequenceCoding.entry_out_of_range d i (by omega)]; exact hg
  refine ⟨rfl, hc, ?_, ?_, ?_, ?_⟩
  · simp [realize, decodeState, hc.1]
  · simpa [realize, realizedCells] using (symbol_decode L (currentCode c) hc.2.1).symm
  · intro i
    have hn : h - (i : ℤ) - 1 ≠ h := by omega
    have hl : h - (i : ℤ) - 1 < h := by omega
    have hi : (h - (h - (i : ℤ) - 1) - 1).toNat = i := by omega
    simpa [realize, realizedCells, hn, hl, hi] using
      (symbol_decode L _ (hall _ hc.2.2.1 i)).symm
  · intro i
    have hn : h + (i : ℤ) + 1 ≠ h := by omega
    have hl : ¬ h + (i : ℤ) + 1 < h := by omega
    have hi : (h + (i : ℤ) + 1 - h - 1).toNat = i := by omega
    simpa [realize, realizedCells, hn, hl, hi] using
      (symbol_decode L _ (hall _ hc.2.2.2 i)).symm

end Lemmatheca.ComputabilityTheory.TapeCoding
