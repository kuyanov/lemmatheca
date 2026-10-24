import Lemmatheca.UniversalComputation.UniversalComputation
import Mathlib.Computability.Reduce

/-! Rice's theorem for the corpus's fixed natural-number program indices.
The waiting map uses the existing specialization function, without renumbering programs. -/
namespace Lemmatheca.ComputabilityTheory.RicesTheorem

open Encodable Denumerable
open Nat.Partrec (Code)
open UniversalComputation

abbrev PartialFunction := ℕ → Part ℕ

def indexSet (C : Set PartialFunction) : Set ℕ := {e | phi e ∈ C}

def Nontrivial (C : Set PartialFunction) : Prop :=
  (∃ g, Nat.Partrec g ∧ g ∈ C) ∧ (∃ h, Nat.Partrec h ∧ h ∉ C)

def Extensional (A : Set ℕ) : Prop :=
  ∀ e d, phi e = phi d → (e ∈ A ↔ d ∈ A)

def bottom : PartialFunction := fun _ => Part.none

theorem indexSet_extensional (C : Set PartialFunction) : Extensional (indexSet C) := by
  intro e d h
  change phi e ∈ C ↔ phi d ∈ C
  rw [h]

theorem extensional_iff_indexSet (A : Set ℕ) :
    Extensional A ↔ ∃ C : Set PartialFunction,
      (∀ g ∈ C, Nat.Partrec g) ∧ A = indexSet C := by
  constructor
  · intro hA
    refine ⟨{g | ∃ e, e ∈ A ∧ phi e = g}, ?_, ?_⟩
    · rintro g ⟨e, _, rfl⟩
      exact Partrec.nat_iff.mp (phi_recursive.comp (Computable.const e) Computable.id)
    · ext e
      constructor
      · intro he
        exact ⟨e, he, rfl⟩
      · rintro ⟨d, hd, he⟩
        exact (hA e d he.symm).mpr hd
  · rintro ⟨C, _, rfl⟩
    exact indexSet_extensional C

theorem nontrivial_iff (C : Set PartialFunction) :
    Nontrivial C ↔ (indexSet C).Nonempty ∧ (indexSet C)ᶜ.Nonempty := by
  constructor
  · rintro ⟨⟨g, hg, hCg⟩, ⟨h, hh, hCh⟩⟩
    obtain ⟨e, he⟩ := phi_complete hg
    obtain ⟨d, hd⟩ := phi_complete hh
    exact ⟨⟨e, by simpa [indexSet, he]⟩, ⟨d, by simpa [indexSet, hd]⟩⟩
  · rintro ⟨⟨e, he⟩, ⟨d, hd⟩⟩
    exact ⟨⟨phi e, Partrec.nat_iff.mp (phi_recursive.comp (Computable.const e) Computable.id), he⟩,
      ⟨phi d, Partrec.nat_iff.mp (phi_recursive.comp (Computable.const d) Computable.id), hd⟩⟩

theorem bottom_ne_zero : bottom ≠ (fun _ => Part.some 0) := by
  intro h
  exact Part.none_ne_some 0 (congrFun h 0)

/-- Run the diagonal computation first, discarding its output only after it exists. -/
def waiting (g : PartialFunction) (e x : ℕ) : Part ℕ :=
  (phi e e).bind fun _ => g x

theorem waiting_partial {g : PartialFunction} (hg : Nat.Partrec g) :
    Nat.Partrec (Nat.unpaired (waiting g)) := by
  have hw : Partrec (fun p : ℕ × ℕ => waiting g p.1 p.2) :=
    (phi_recursive.comp Computable.fst Computable.fst).bind
      (((Partrec.nat_iff.mpr hg).comp (Computable.snd.comp Computable.fst)).to₂)
  exact Partrec.nat_iff.mp (hw.comp Computable.unpair)

noncomputable def waitingProgram (g : PartialFunction) (hg : Nat.Partrec g) : ℕ :=
  Classical.choose (phi_complete (waiting_partial hg))

noncomputable def waitingMap (g : PartialFunction) (hg : Nat.Partrec g) (e : ℕ) : ℕ :=
  specialize (waitingProgram g hg) e

theorem waitingProgram_spec (g : PartialFunction) (hg : Nat.Partrec g) :
    phi (waitingProgram g hg) = Nat.unpaired (waiting g) := by
  exact Classical.choose_spec (phi_complete (waiting_partial hg))

theorem waitingMap_primitive (g : PartialFunction) (hg : Nat.Partrec g) :
    Primrec (waitingMap g hg) := by
  exact specialize_primitive.comp (Primrec.const _) Primrec.id

theorem waitingMap_eval (g : PartialFunction) (hg : Nat.Partrec g) (e x : ℕ) :
    phi (waitingMap g hg e) x = (phi e e).bind (fun _ => g x) := by
  rw [waitingMap, specialize_eval, waitingProgram_spec]
  simp only [Nat.unpaired, Nat.unpair_pair, waiting]

theorem waitingMap_cases (g : PartialFunction) (hg : Nat.Partrec g) (e : ℕ) :
    ((phi e e).Dom → phi (waitingMap g hg e) = g) ∧
    (¬ (phi e e).Dom → phi (waitingMap g hg e) = bottom) := by
  constructor
  · intro h
    funext x
    rw [waitingMap_eval]
    exact h.bind (fun _ => g x)
  · intro h
    funext x
    rw [waitingMap_eval, Part.eq_none_iff'.mpr h, Part.bind_none]
    rfl

theorem waitingMap_membership (C : Set PartialFunction) (g : PartialFunction)
    (hg : Nat.Partrec g) (hbot : bottom ∉ C) (hgood : g ∈ C) (e : ℕ) :
    e ∈ haltingDiagonal ↔ waitingMap g hg e ∈ indexSet C := by
  change (phi e e).Dom ↔ phi (waitingMap g hg e) ∈ C
  by_cases h : (phi e e).Dom
  · rw [show phi (waitingMap g hg e) = g from (waitingMap_cases g hg e).1 h]
    simp [h, hgood]
  · rw [show phi (waitingMap g hg e) = bottom from (waitingMap_cases g hg e).2 h]
    simp [h, hbot]

theorem waitingMap_nonmembership (C : Set PartialFunction) (g : PartialFunction)
    (hg : Nat.Partrec g) (hbot : bottom ∈ C) (hbad : g ∉ C) (e : ℕ) :
    e ∈ haltingDiagonal ↔ waitingMap g hg e ∉ indexSet C := by
  change (phi e e).Dom ↔ phi (waitingMap g hg e) ∉ C
  by_cases h : (phi e e).Dom
  · rw [show phi (waitingMap g hg e) = g from (waitingMap_cases g hg e).1 h]
    simp [h, hbad]
  · rw [show phi (waitingMap g hg e) = bottom from (waitingMap_cases g hg e).2 h]
    simp [h, hbot]

theorem rice_reductions (C : Set PartialFunction) (hC : Nontrivial C) :
    (bottom ∉ C → (fun e => e ∈ haltingDiagonal) ≤₀ (fun e => e ∈ indexSet C)) ∧
    (bottom ∈ C → (fun e => e ∈ haltingDiagonal) ≤₀ (fun e => e ∉ indexSet C)) := by
  constructor
  · intro hbot
    obtain ⟨g, hg, hgood⟩ := hC.1
    exact ⟨waitingMap g hg, (waitingMap_primitive g hg).to_comp,
      waitingMap_membership C g hg hbot hgood⟩
  · intro hbot
    obtain ⟨g, hg, hbad⟩ := hC.2
    exact ⟨waitingMap g hg, (waitingMap_primitive g hg).to_comp,
      waitingMap_nonmembership C g hg hbot hbad⟩

theorem rice_undecidable (C : Set PartialFunction) (hC : Nontrivial C) :
    ¬ ComputablePred (fun e => e ∈ indexSet C) := by
  classical
  intro h
  by_cases hb : bottom ∈ C
  · exact haltingDiagonal_undecidable
      (ComputablePred.computable_of_manyOneReducible ((rice_reductions C hC).2 hb) h.not)
  · exact haltingDiagonal_undecidable
      (ComputablePred.computable_of_manyOneReducible ((rice_reductions C hC).1 hb) h)

theorem rice_extensional_iff (A : Set ℕ) (hA : Extensional A) :
    ComputablePred (fun e => e ∈ A) ↔ A = ∅ ∨ A = Set.univ := by
  classical
  constructor
  · intro hc
    by_cases h0 : A = ∅
    · exact Or.inl h0
    · right
      by_contra hu
      obtain ⟨C, _, rfl⟩ := (extensional_iff_indexSet A).mp hA
      apply rice_undecidable C ((nontrivial_iff C).mpr ?_) hc
      constructor
      · exact Set.nonempty_iff_ne_empty.mpr h0
      · by_contra hn
        apply hu
        apply Set.eq_univ_of_forall
        intro x
        by_contra hx
        exact hn ⟨x, hx⟩
  · rintro (rfl | rfl)
    · exact ⟨inferInstance, by simpa using (Computable.const false : Computable (fun _ : ℕ => false))⟩
    · exact ⟨inferInstance, by simpa using (Computable.const true : Computable (fun _ : ℕ => true))⟩

def haltsZero : Set ℕ := {e | (phi e 0).Dom}

def everOutputs (m : ℕ) : Set ℕ := {e | ∃ x, m ∈ phi e x}

def totality : Set ℕ := {e | ∀ x, (phi e x).Dom}

def equivalentTo (h : PartialFunction) : Set ℕ := {e | phi e = h}

def equivalentPrograms : Set ℕ := {n | phi n.unpair.1 = phi n.unpair.2}

theorem haltsZero_facts :
    REPred (fun e => e ∈ haltsZero) ∧ ¬ ComputablePred (fun e => e ∈ haltsZero) ∧
    (∀ e, e ∈ haltingDiagonal ↔ waitingMap (fun _ => Part.some 0) Nat.Partrec.zero e ∈ haltsZero) := by
  let C : Set PartialFunction := {g | (g 0).Dom}
  have hb : bottom ∉ C := by simp [C, bottom]
  have hg : (fun _ : ℕ => Part.some 0) ∈ C := by simp [C]
  have hn : Nontrivial C := ⟨⟨_, Nat.Partrec.zero, hg⟩, ⟨_, Nat.Partrec.none, hb⟩⟩
  refine ⟨(phi_recursive.comp Computable.id (Computable.const 0)).dom_re,
    rice_undecidable C hn, ?_⟩
  exact waitingMap_membership C _ Nat.Partrec.zero hb hg

theorem everOutputs_facts (m : ℕ) :
    REPred (fun e => e ∈ everOutputs m) ∧ ¬ ComputablePred (fun e => e ∈ everOutputs m) ∧
    (∀ e, e ∈ haltingDiagonal ↔
      waitingMap (fun _ => Part.some m) (Nat.Partrec.of_primrec (Nat.Primrec.const m)) e ∈ everOutputs m) := by
  let C : Set PartialFunction := {g | ∃ x, m ∈ g x}
  have hb : bottom ∉ C := by simp [C, bottom]
  have hg : (fun _ : ℕ => Part.some m) ∈ C := ⟨0, Part.mem_some _⟩
  have hm : Nat.Partrec (fun _ : ℕ => Part.some m) := Nat.Partrec.of_primrec (Nat.Primrec.const m)
  have hn : Nontrivial C := ⟨⟨_, hm, hg⟩, ⟨_, Nat.Partrec.none, hb⟩⟩
  refine ⟨?_, rice_undecidable C hn, waitingMap_membership C _ hm hb hg⟩
  apply (enumerable_iff_primitive_certificate _).mpr
  refine ⟨fun e w => boundedValue w.unpair.2 e w.unpair.1 = m + 1, ?_, ?_⟩
  · exact Primrec.eq.comp (boundedValue_primitive.comp
      (((Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).pair Primrec.fst).pair
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))) (Primrec.const _)
  · intro e
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨k, hk⟩ := (phi_output e x m).mp hx
      exact ⟨Nat.pair x k, by simpa⟩
    · rintro ⟨w, hw⟩
      exact ⟨w.unpair.1, (phi_output _ _ _).mpr ⟨w.unpair.2, hw⟩⟩

theorem totality_facts :
    ¬ ComputablePred (fun e => e ∈ totality) ∧
    (∀ e, e ∈ haltingDiagonal ↔ waitingMap (fun _ => Part.some 0) Nat.Partrec.zero e ∈ totality) := by
  let C : Set PartialFunction := {g | ∀ x, (g x).Dom}
  have hb : bottom ∉ C := by simp [C, bottom]
  have hg : (fun _ : ℕ => Part.some 0) ∈ C := by simp [C]
  have hn : Nontrivial C := ⟨⟨_, Nat.Partrec.zero, hg⟩, ⟨_, Nat.Partrec.none, hb⟩⟩
  exact ⟨rice_undecidable C hn, waitingMap_membership C _ Nat.Partrec.zero hb hg⟩

theorem equivalentTo_undecidable (h : PartialFunction) (hh : Nat.Partrec h) :
    ¬ ComputablePred (fun e => e ∈ equivalentTo h) := by
  classical
  apply rice_undecidable {h}
  refine ⟨⟨h, hh, rfl⟩, ?_⟩
  by_cases hb : h = bottom
  · refine ⟨fun _ => Part.some 0, Nat.Partrec.zero, ?_⟩
    change (fun _ => Part.some 0) ≠ h
    rw [hb]
    exact bottom_ne_zero.symm
  · exact ⟨bottom, Nat.Partrec.none, by change bottom ≠ h; exact Ne.symm hb⟩

theorem equivalentPrograms_undecidable :
    ¬ ComputablePred (fun n => n ∈ equivalentPrograms) := by
  intro h
  obtain ⟨d, hd⟩ := phi_complete (f := fun _ => Part.some 0) Nat.Partrec.zero
  apply equivalentTo_undecidable (fun _ => Part.some 0) Nat.Partrec.zero
  exact ComputablePred.computable_of_manyOneReducible
    ⟨fun e => Nat.pair e d, (Primrec₂.natPair.comp Primrec.id (Primrec.const d)).to_comp,
      fun e => by simp [equivalentPrograms, equivalentTo, hd]⟩ h

end Lemmatheca.ComputabilityTheory.RicesTheorem
