import Lemmatheca.CodingFiniteSequences.FiniteSequenceCoding

namespace Lemmatheca.ComputabilityTheory.TapeCoding

def pack (q a l r : ℕ) : ℕ := Nat.pair q (Nat.pair a (Nat.pair l r))
def stateCode (c : ℕ) : ℕ := (Nat.unpair c).1
def currentCode (c : ℕ) : ℕ := (Nat.unpair (Nat.unpair c).2).1
def leftCode (c : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1
def rightCode (c : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).2

theorem pack_fields (q a l r : ℕ) :
    stateCode (pack q a l r) = q ∧ currentCode (pack q a l r) = a ∧
    leftCode (pack q a l r) = l ∧ rightCode (pack q a l r) = r := by
  simp [pack, stateCode, currentCode, leftCode, rightCode]

theorem pack_unpack (c : ℕ) :
    pack (stateCode c) (currentCode c) (leftCode c) (rightCode c) = c := by
  simp only [pack, stateCode, currentCode, leftCode, rightCode, Nat.pair_unpair]

theorem pack_primrec : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => pack p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact Primrec₂.natPair.comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
      (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

theorem fields_primrec :
    Primrec stateCode ∧ Primrec currentCode ∧ Primrec leftCode ∧ Primrec rightCode := by
  have hu := Primrec.fst.comp Primrec.unpair
  have hv := Primrec.snd.comp Primrec.unpair
  exact ⟨hu, hu.comp hv, hu.comp (hv.comp hv), hv.comp (hv.comp hv)⟩

def listTest (g c : ℕ) : ℕ :=
  FiniteSequenceCoding.fold (fun z a => z * if a < g then 1 else 0) c 1

def Valid (g s c : ℕ) : Prop :=
  stateCode c < s ∧ currentCode c < g ∧
  (∀ i < FiniteSequenceCoding.length (leftCode c),
    FiniteSequenceCoding.entry (leftCode c) i < g) ∧
  (∀ i < FiniteSequenceCoding.length (rightCode c),
    FiniteSequenceCoding.entry (rightCode c) i < g)

def validTest (g s c : ℕ) : Bool :=
  decide (stateCode c < s) && decide (currentCode c < g) &&
  (listTest g (leftCode c) == 1) && (listTest g (rightCode c) == 1)

theorem listTest_spec (g c : ℕ) : listTest g c = 1 ↔
    ∀ i < FiniteSequenceCoding.length c, FiniteSequenceCoding.entry c i < g := by
  have hfold (xs : List ℕ) (z : ℕ) :
      xs.foldl (fun z a => z * if a < g then 1 else 0) z =
        if ∀ a ∈ xs, a < g then z else 0 := by
    induction xs generalizing z with
    | nil => simp
    | cons a xs ih =>
      rw [List.foldl_cons, ih]
      by_cases ha : a < g <;> simp [ha]
  have hentries : (∀ a ∈ FiniteSequenceCoding.decode c, a < g) ↔
      ∀ i < FiniteSequenceCoding.length c, FiniteSequenceCoding.entry c i < g := by
    constructor
    · intro h i hi
      have hm := h _ (List.getElem_mem hi)
      simpa only [FiniteSequenceCoding.entry, List.getElem?_eq_getElem hi,
        Option.getD_some] using hm
    · intro h a ha
      obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
      have hm := h i hi
      simpa only [FiniteSequenceCoding.entry, List.getElem?_eq_getElem hi,
        Option.getD_some, hia] using hm
  change (FiniteSequenceCoding.decode c).foldl _ 1 = 1 ↔ _
  rw [hfold, ← hentries]
  split_ifs <;> simp_all

theorem validTest_spec (g s c : ℕ) : validTest g s c = true ↔ Valid g s c := by
  simp only [validTest, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    listTest_spec, Valid]
  tauto

theorem listTest_primrec : Primrec₂ listTest := by
  have hstep : Primrec (fun p : ℕ × ℕ × ℕ =>
      p.2.1 * if p.2.2 < p.1 then 1 else 0) :=
    Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.ite (Primrec.nat_lt.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
        (Primrec.const 1) (Primrec.const 0))
  have hfold := FiniteSequenceCoding.primrec_fold_param
    (h := fun g z a => z * if a < g then 1 else 0) hstep
  exact hfold.comp (Primrec.fst.pair (Primrec.snd.pair (Primrec.const 1)))

theorem validTest_primrec (g s : ℕ) : Primrec (validTest g s) := by
  have hq := (Primrec.nat_lt.comp fields_primrec.1 (Primrec.const s)).decide
  have ha := (Primrec.nat_lt.comp fields_primrec.2.1 (Primrec.const g)).decide
  have hl := Primrec.beq.comp
    (listTest_primrec.comp (Primrec.const g) fields_primrec.2.2.1) (Primrec.const 1)
  have hr := Primrec.beq.comp
    (listTest_primrec.comp (Primrec.const g) fields_primrec.2.2.2) (Primrec.const 1)
  exact Primrec.and.comp (Primrec.and.comp (Primrec.and.comp hq ha) hl) hr

theorem valid_primrec (g s : ℕ) : PrimrecPred (Valid g s) := by
  exact (Primrec.eq.comp (validTest_primrec g s) (Primrec.const true)).of_eq
    (validTest_spec g s)

theorem valid_zero (g s : ℕ) (hg : 0 < g) (hs : 0 < s) : Valid g s 0 := by
  simp [Valid, stateCode, currentCode, leftCode, rightCode,
    FiniteSequenceCoding.length, hg, hs]

end Lemmatheca.ComputabilityTheory.TapeCoding
