import Lemmatheca.UniversalComputation.UniversalComputation

/-! Separators and the two diagonal output classes of the existing program numbering. -/

namespace Lemmatheca.ComputabilityTheory.ComputableSeparation

open UniversalComputation

def Separator (A B C : Set ℕ) : Prop := A ⊆ C ∧ Disjoint C B

def ComputablySeparable (A B : Set ℕ) : Prop :=
  ∃ C : Set ℕ, ComputablePred (fun x => x ∈ C) ∧ Separator A B C

def ComputablyInseparable (A B : Set ℕ) : Prop :=
  Disjoint A B ∧ ¬ ComputablySeparable A B

theorem separator_exists_iff (A B : Set ℕ) :
    (∃ C, Separator A B C) ↔ Disjoint A B := by
  constructor
  · rintro ⟨C, hAC, hCB⟩
    exact hCB.mono_left hAC
  · intro h
    exact ⟨A, Set.Subset.rfl, h⟩

def diagonalOutput (y : ℕ) : Set ℕ := {e | y ∈ phi e e}

theorem diagonalCertificate_primitive (y : ℕ) :
    PrimrecPred (fun p : ℕ × ℕ => boundedValue p.2 p.1 p.1 = y + 1) := by
  exact Primrec.eq.comp
    (boundedValue_primitive.comp ((Primrec.snd.pair Primrec.fst).pair Primrec.fst))
    (Primrec.const (y + 1))

theorem diagonalOutput_enumerable (y : ℕ) :
    REPred (fun e => e ∈ diagonalOutput y) := by
  apply (enumerable_iff_primitive_certificate _).mpr
  exact ⟨fun e k => boundedValue k e e = y + 1,
    diagonalCertificate_primitive y, fun e => phi_output e e y⟩

theorem diagonalOutput_disjoint {y z : ℕ} (h : y ≠ z) :
    Disjoint (diagonalOutput y) (diagonalOutput z) := by
  exact Set.disjoint_left.mpr fun _ hy hz => h (Part.mem_unique hy hz)

theorem diagonal_inseparable :
    ComputablyInseparable (diagonalOutput 0) (diagonalOutput 1) := by
  classical
  refine ⟨diagonalOutput_disjoint (by decide), ?_⟩
  rintro ⟨C, hC, hsep⟩
  obtain ⟨g, hg, hχ⟩ := (decidable_iff_characteristic (fun x => x ∈ C)).mp hC
  obtain ⟨j, hj⟩ := phi_complete (Partrec.nat_iff.mp hg.partrec)
  have hv : phi j j = Part.some (indicator (fun x => x ∈ C) j) :=
    (congrFun hj j).trans (congrArg Part.some (hχ j))
  by_cases hc : j ∈ C
  · have hb : j ∈ diagonalOutput 1 := by
      change 1 ∈ phi j j
      simp [hv, indicator, hc]
    exact Set.disjoint_left.mp hsep.2 hc hb
  · have ha : j ∈ diagonalOutput 0 := by
      change 0 ∈ phi j j
      simp [hv, indicator, hc]
    exact hc (hsep.1 ha)

theorem diagonalOutput_undecidable (y : ℕ) (hy : y ≤ 1) :
    ¬ ComputablePred (fun e => e ∈ diagonalOutput y) := by
  intro hc
  have hdis := diagonal_inseparable.1
  rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl
  · exact diagonal_inseparable.2 ⟨diagonalOutput 0, hc, Set.Subset.rfl, hdis⟩
  · apply diagonal_inseparable.2
    refine ⟨(diagonalOutput 1)ᶜ, hc.not, ?_, ?_⟩
    · intro e he
      exact fun hb => Set.disjoint_left.mp hdis he hb
    · exact Set.disjoint_left.mpr fun _ ha hb => ha hb

theorem diagonalOutput_infinite (y : ℕ) (hy : y ≤ 1) :
    (diagonalOutput y).Infinite := by
  classical
  intro hfin
  have hF := hfin
  let L : List ℕ := hF.toFinset.toList
  have htest : PrimrecPred (fun x : ℕ => ∃ a ∈ L, a = x) :=
    Primrec.eq.exists_mem_list.comp (Primrec.const L) Primrec.id
  apply diagonalOutput_undecidable y hy
  exact htest.computablePred.of_eq fun x => by simp [L]

theorem diagonalOutput_complement_not_enumerable (y : ℕ) (hy : y ≤ 1) :
    ¬ REPred (fun e => e ∉ diagonalOutput y) := by
  intro h
  exact diagonalOutput_undecidable y hy
    (ComputablePred.computable_iff_re_compl_re'.mpr ⟨diagonalOutput_enumerable y, h⟩)

/-- Search exactly for a finite zero-output or one-output self-computation. -/
def binaryDiagonal (e : ℕ) : Part ℕ :=
  (Nat.rfind fun k => Part.some
    (decide (boundedValue k e e = 1 ∨ boundedValue k e e = 2))).map
      (fun k => boundedValue k e e - 1)

theorem binaryDiagonal_partial : Nat.Partrec binaryDiagonal := by
  have hb : Primrec (fun p : ℕ × ℕ => boundedValue p.2 p.1 p.1) :=
    boundedValue_primitive.comp ((Primrec.snd.pair Primrec.fst).pair Primrec.fst)
  have htest := (Primrec.eq.comp hb (Primrec.const 1)).or
    (Primrec.eq.comp hb (Primrec.const 2))
  have hc : Computable₂ (fun e k => decide (boundedValue k e e = 1 ∨ boundedValue k e e = 2)) :=
    htest.decide.to_comp
  have hs := Partrec.rfind hc.partrec₂
  exact Partrec.nat_iff.mp (hs.map
    (Primrec.nat_sub.comp hb (Primrec.const 1)).to_comp.to₂)

theorem binaryDiagonal_spec (e y : ℕ) :
    y ∈ binaryDiagonal e ↔
      (y = 0 ∧ e ∈ diagonalOutput 0) ∨ (y = 1 ∧ e ∈ diagonalOutput 1) := by
  let Q : ℕ → Prop := fun k => boundedValue k e e = 1 ∨ boundedValue k e e = 2
  have reverse (a : ℕ) (ha : a = 0 ∨ a = 1) (hphi : a ∈ phi e e) :
      a ∈ binaryDiagonal e := by
    obtain ⟨k, hk⟩ := (phi_output e e a).mp hphi
    have hQ : ∃ k, Q k := ⟨k, by dsimp [Q]; rcases ha with rfl | rfl <;> simp_all⟩
    let t := Nat.find hQ
    have ht : t ∈ Nat.rfind (fun k => Part.some (decide (Q k))) := by
      apply Nat.mem_rfind.mpr
      exact ⟨by simpa using Nat.find_spec hQ,
        fun {m} hm => by simpa using Nat.find_min hQ hm⟩
    have hval : boundedValue t e e - 1 = a := by
      rcases Nat.find_spec hQ with h0 | h1
      · change boundedValue t e e = 1 at h0
        have h0phi : 0 ∈ phi e e := (phi_output e e 0).mpr ⟨t, h0⟩
        have heq := Part.mem_unique h0phi hphi
        omega
      · change boundedValue t e e = 2 at h1
        have h1phi : 1 ∈ phi e e := (phi_output e e 1).mpr ⟨t, h1⟩
        have heq := Part.mem_unique h1phi hphi
        omega
    exact (Part.mem_map_iff _).mpr ⟨t, ht, hval⟩
  constructor
  · rintro ⟨hd, hy⟩
    obtain ⟨k, hk, hout⟩ := (Part.mem_map_iff _).mp ⟨hd, hy⟩
    have hQ : Q k := by simpa using Nat.rfind_spec hk
    rcases hQ with h0 | h1
    · exact Or.inl ⟨by omega, (phi_output e e 0).mpr ⟨k, h0⟩⟩
    · exact Or.inr ⟨by omega, (phi_output e e 1).mpr ⟨k, h1⟩⟩
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact reverse 0 (Or.inl rfl) h
    · exact reverse 1 (Or.inr rfl) h

theorem binaryDiagonal_domain (e : ℕ) :
    (binaryDiagonal e).Dom ↔ e ∈ diagonalOutput 0 ∪ diagonalOutput 1 := by
  rw [Part.dom_iff_mem]
  simp only [binaryDiagonal_spec, Set.mem_union]
  simp only [exists_or, exists_eq_left]

def positiveSeparatorAttempt (e : ℕ) : Part ℕ :=
  (binaryDiagonal e).map (fun y => 1 - y)

theorem positiveSeparatorAttempt_spec (e y : ℕ) :
    y ∈ positiveSeparatorAttempt e ↔
      (y = 1 ∧ e ∈ diagonalOutput 0) ∨ (y = 0 ∧ e ∈ diagonalOutput 1) := by
  simp only [positiveSeparatorAttempt, Part.mem_map_iff, binaryDiagonal_spec]
  constructor
  · rintro ⟨a, (⟨rfl, ha⟩ | ⟨rfl, ha⟩), hy⟩
    · exact Or.inl ⟨hy.symm, ha⟩
    · exact Or.inr ⟨hy.symm, ha⟩
  · rintro (⟨rfl, ha⟩ | ⟨rfl, ha⟩)
    · exact ⟨0, Or.inl ⟨rfl, ha⟩, rfl⟩
    · exact ⟨1, Or.inr ⟨rfl, ha⟩, rfl⟩

def Extends (f : ℕ → Part ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ x y, y ∈ f x → g x = y

def TotalComputableExtension (f : ℕ → Part ℕ) (g : ℕ → ℕ) : Prop :=
  Computable g ∧ Extends f g

def zeroFiber (g : ℕ → ℕ) : Set ℕ := {x | g x = 0}

theorem extension_gives_separator (g : ℕ → ℕ)
    (hg : TotalComputableExtension binaryDiagonal g) :
    ComputablePred (fun x => x ∈ zeroFiber g) ∧
      Separator (diagonalOutput 0) (diagonalOutput 1) (zeroFiber g) := by
  classical
  refine ⟨(Primrec.eq.decide.to_comp.comp hg.1 (Computable.const 0)).computablePred, ?_, ?_⟩
  · intro e he
    exact hg.2 e 0 ((binaryDiagonal_spec e 0).mpr (Or.inl ⟨rfl, he⟩))
  · apply Set.disjoint_left.mpr
    intro e hzero hone
    have h1 := hg.2 e 1 ((binaryDiagonal_spec e 1).mpr (Or.inr ⟨rfl, hone⟩))
    change g e = 0 at hzero
    omega

theorem no_total_computable_extension :
    ¬ ∃ g, TotalComputableExtension binaryDiagonal g := by
  rintro ⟨g, hg⟩
  exact diagonal_inseparable.2 ⟨zeroFiber g, extension_gives_separator g hg⟩

def normalizeBinary (g : ℕ → ℕ) (x : ℕ) : ℕ := if g x = 0 then 0 else 1

theorem normalizeBinary_computable {g : ℕ → ℕ} (hg : Computable g) :
    Computable (normalizeBinary g) := by
  exact ComputablePred.ite (Computable.const 0) (Computable.const 1)
    (Primrec.eq.decide.to_comp.comp hg (Computable.const 0)).computablePred

theorem normalizeBinary_extends {f : ℕ → Part ℕ} {g : ℕ → ℕ}
    (hf : ∀ x y, y ∈ f x → y = 0 ∨ y = 1) (hg : Extends f g) :
    Extends f (normalizeBinary g) ∧ ∀ x, normalizeBinary g x = 0 ∨
      normalizeBinary g x = 1 := by
  constructor
  · intro x y hy
    have he := hg x y hy
    rcases hf x y hy with rfl | rfl <;> simp [normalizeBinary, he]
  · intro x
    simp only [normalizeBinary]
    split_ifs <;> simp

theorem binary_extension_iff (f : ℕ → Part ℕ)
    (hf : ∀ x y, y ∈ f x → y = 0 ∨ y = 1) :
    (∃ g, TotalComputableExtension f g) ↔
      ∃ g, TotalComputableExtension f g ∧ ∀ x, g x = 0 ∨ g x = 1 := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨normalizeBinary g,
      ⟨normalizeBinary_computable hg.1, (normalizeBinary_extends hf hg.2).1⟩,
      (normalizeBinary_extends hf hg.2).2⟩
  · rintro ⟨g, hg, _⟩
    exact ⟨g, hg⟩

theorem separator_gives_extension (C : Set ℕ)
    (hC : ComputablePred (fun x => x ∈ C))
    (hsep : Separator (diagonalOutput 0) (diagonalOutput 1) C) :
    TotalComputableExtension binaryDiagonal (fun x => 1 - indicator (fun n => n ∈ C) x) := by
  classical
  obtain ⟨g, hg, he⟩ := (decidable_iff_characteristic (fun x => x ∈ C)).mp hC
  have hχ : Computable (indicator (fun x => x ∈ C)) := hg.of_eq he
  refine ⟨Primrec.nat_sub.to_comp.comp (Computable.const 1) hχ, ?_⟩
  intro x y hy
  rcases (binaryDiagonal_spec x y).mp hy with ⟨rfl, h0⟩ | ⟨rfl, h1⟩
  · simp [indicator, hsep.1 h0]
  · have hn : x ∉ C := fun hc => Set.disjoint_left.mp hsep.2 hc h1
    simp [indicator, hn]

end Lemmatheca.ComputabilityTheory.ComputableSeparation
