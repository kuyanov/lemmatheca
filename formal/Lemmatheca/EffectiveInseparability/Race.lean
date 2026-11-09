import Lemmatheca.EffectiveInseparability.Basic
import Lemmatheca.ComputablyInseparableSets.NegativeSearch
import Lemmatheca.UniformSelfReference.Uniform

/-! A least-certificate race, its actual program indices, and the diagonal escape witness. -/
namespace Lemmatheca.ComputabilityTheory.EffectiveInseparability

open UniversalComputation EffectiveEnumerations ComputableSeparation UniformSelfReference

def leftCertificate (w k : ℕ) : Prop :=
  0 < boundedValue k w.unpair.1 w.unpair.2.unpair.2

def rightCertificate (w k : ℕ) : Prop :=
  0 < boundedValue k w.unpair.2.unpair.1 w.unpair.2.unpair.2

noncomputable def certificateRace (w : ℕ) : Part ℕ :=
  negativeRace leftCertificate rightCertificate w

private theorem left_certificate_primitive :
    PrimrecPred (fun t : ℕ × ℕ => leftCertificate t.1 t.2) := by
  have hc : Primrec (fun t : ℕ × ℕ => t.1.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hx : Primrec (fun t : ℕ × ℕ => t.1.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
  exact certificate_primitive.comp ((hc.pair hx).pair Primrec.snd)

private theorem right_certificate_primitive :
    PrimrecPred (fun t : ℕ × ℕ => rightCertificate t.1 t.2) := by
  have hr : Primrec (fun t : ℕ × ℕ => t.1.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hd : Primrec (fun t : ℕ × ℕ => t.1.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hr)
  have hx : Primrec (fun t : ℕ × ℕ => t.1.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hr)
  exact certificate_primitive.comp ((hd.pair hx).pair Primrec.snd)

theorem certificate_race_partial : Nat.Partrec certificateRace := by
  exact negativeRace_partial _ _ left_certificate_primitive right_certificate_primitive

theorem certificate_race_stage (w k : ℕ)
    (hk : k ∈ raceStage leftCertificate rightCertificate w) :
    certificateRace w = Part.some
      (@ite ℕ (leftCertificate w k) (Classical.propDecidable _) 0 1) := by
  exact negativeRace_at_stage _ _ w k hk

theorem certificate_race_domain (c d x : ℕ) :
    (certificateRace (Nat.pair c (Nat.pair d x))).Dom ↔
      x ∈ indexSet c ∪ indexSet d := by
  rw [certificateRace, negativeRace_domain]
  simp only [leftCertificate, rightCertificate, Nat.unpair_pair]
  change ((∃ k, certificate c x k) ∨ (∃ k, certificate d x k)) ↔
    (phi c x).Dom ∨ (phi d x).Dom
  rw [← phi_domain, ← phi_domain]

theorem certificate_race_left (c d x : ℕ) (hc : x ∈ indexSet c)
    (hd : x ∉ indexSet d) :
    certificateRace (Nat.pair c (Nat.pair d x)) = Part.some 0 := by
  have hdom := (certificate_race_domain c d x).mpr (Or.inl hc)
  have hs : (raceStage leftCertificate rightCertificate (Nat.pair c (Nat.pair d x))).Dom := by
    simpa only [certificateRace, negativeRace, Part.map_Dom] using hdom
  obtain ⟨k, hk⟩ := Part.dom_iff_mem.mp hs
  have hright : ¬ rightCertificate (Nat.pair c (Nat.pair d x)) k := by
    intro ht
    exact hd ((phi_domain d x).mpr ⟨k, by simpa [rightCertificate, certificate] using ht⟩)
  have hleft := ((raceStage_spec _ _ _ _).mp hk).1.resolve_right hright
  simpa only [hleft, ↓reduceIte] using certificate_race_stage _ k hk

theorem certificate_race_right (c d x : ℕ) (hc : x ∉ indexSet c)
    (hd : x ∈ indexSet d) :
    certificateRace (Nat.pair c (Nat.pair d x)) = Part.some 1 := by
  have hdom := (certificate_race_domain c d x).mpr (Or.inr hd)
  have hs : (raceStage leftCertificate rightCertificate (Nat.pair c (Nat.pair d x))).Dom := by
    simpa only [certificateRace, negativeRace, Part.map_Dom] using hdom
  obtain ⟨k, hk⟩ := Part.dom_iff_mem.mp hs
  have hleft : ¬ leftCertificate (Nat.pair c (Nat.pair d x)) k := by
    intro ht
    exact hc ((phi_domain c x).mpr ⟨k, by simpa [leftCertificate, certificate] using ht⟩)
  simpa only [hleft, ↓reduceIte] using certificate_race_stage _ k hk

def CanonicalProgramIndex (r : ℕ) : Prop :=
  ∀ w z, phi r (Nat.pair w z) = certificateRace w

def canonicalIndex (r c d x : ℕ) : ℕ := specialize r (Nat.pair c (Nat.pair d x))

theorem canonical_program_index_exists : ∃ r, CanonicalProgramIndex r := by
  have hp : Partrec₂ (fun (w _z : ℕ) => certificateRace w) :=
    (Partrec.nat_iff.mpr certificate_race_partial).comp Computable.fst
  obtain ⟨r, hr⟩ := phi_complete (Partrec₂.unpaired'.mpr hp)
  exact ⟨r, fun w z => by
    simpa only [Nat.unpaired, Nat.unpair_pair] using congrFun hr (Nat.pair w z)⟩

theorem canonical_index_primitive (r : ℕ) :
    Primrec (fun t : ℕ × (ℕ × ℕ) => canonicalIndex r t.1 t.2.1 t.2.2) := by
  exact specialize_primitive.comp (Primrec.const r)
    (Primrec₂.natPair.comp Primrec.fst (Primrec₂.natPair.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem canonical_index_evaluation (r : ℕ) (hr : CanonicalProgramIndex r) (c d x z : ℕ) :
    phi (canonicalIndex r c d x) z = certificateRace (Nat.pair c (Nat.pair d x)) := by
  exact (specialize_eval r _ z).trans (hr _ z)

theorem canonical_pair_reduction (r : ℕ) (hr : CanonicalProgramIndex r) (c d : ℕ)
    (hcd : Disjoint (indexSet c) (indexSet d)) :
    PairReduction (indexSet c) (indexSet d) (diagonalOutput 0) (diagonalOutput 1)
      (canonicalIndex r c d) := by
  have hcomp : Computable (canonicalIndex r c d) :=
    ((canonical_index_primitive r).comp
      ((Primrec.const c).pair ((Primrec.const d).pair Primrec.id))).to_comp
  have hcases (x : ℕ) :
      (x ∈ indexSet c ↔ canonicalIndex r c d x ∈ diagonalOutput 0) ∧
      (x ∈ indexSet d ↔ canonicalIndex r c d x ∈ diagonalOutput 1) := by
    by_cases hc : x ∈ indexSet c
    · have hd : x ∉ indexSet d := fun hx => Set.disjoint_left.mp hcd hc hx
      have he := (canonical_index_evaluation r hr c d x (canonicalIndex r c d x)).trans
        (certificate_race_left c d x hc hd)
      simp [diagonalOutput, he, hc, hd]
    · by_cases hd : x ∈ indexSet d
      · have he := (canonical_index_evaluation r hr c d x (canonicalIndex r c d x)).trans
          (certificate_race_right c d x hc hd)
        simp [diagonalOutput, he, hc, hd]
      · have hn : certificateRace (Nat.pair c (Nat.pair d x)) = Part.none :=
          Part.eq_none_iff'.mpr (by simp only [certificate_race_domain, Set.mem_union, hc, hd,
            or_self, not_false_eq_true])
        have he := (canonical_index_evaluation r hr c d x (canonicalIndex r c d x)).trans hn
        simp [diagonalOutput, he, hc, hd]
  exact ⟨hcomp, fun x => (hcases x).1, fun x => (hcases x).2⟩

theorem canonical_empty_source (r : ℕ) (hr : CanonicalProgramIndex r) (c d : ℕ)
    (hc : indexSet c = ∅) (hd : indexSet d = ∅) :
    ∀ x z, phi (canonicalIndex r c d x) z = Part.none := by
  intro x z
  rw [canonical_index_evaluation r hr]
  apply Part.eq_none_iff'.mpr
  simp [certificate_race_domain, hc, hd]

noncomputable def oppositeProgram (z a _x : ℕ) : Part ℕ :=
  (certificateRace (Nat.pair a.unpair.1 (Nat.pair a.unpair.2 z))).map (fun y => 1 - y)

def OppositeSelector (d : ℕ → ℕ → ℕ) : Prop :=
  Primrec₂ d ∧ ∀ u v x, phi (d u v) x = oppositeProgram (d u v) (Nat.pair u v) x

theorem opposite_program_partial :
    Partrec (fun t : ℕ × (ℕ × ℕ) => oppositeProgram t.1 t.2.1 t.2.2) := by
  have hu : Computable (fun t : ℕ × (ℕ × ℕ) => t.2.1.unpair.1) :=
    Computable.fst.comp (Computable.unpair.comp (Computable.fst.comp Computable.snd))
  have hv : Computable (fun t : ℕ × (ℕ × ℕ) => t.2.1.unpair.2) :=
    Computable.snd.comp (Computable.unpair.comp (Computable.fst.comp Computable.snd))
  have hw : Computable (fun t : ℕ × (ℕ × ℕ) =>
      Nat.pair t.2.1.unpair.1 (Nat.pair t.2.1.unpair.2 t.1)) :=
    Primrec₂.natPair.to_comp.comp hu (Primrec₂.natPair.to_comp.comp hv Computable.fst)
  exact ((Partrec.nat_iff.mpr certificate_race_partial).comp hw).map
    (Primrec.nat_sub.to_comp.comp (Computable.const 1) Computable.snd).to₂

theorem opposite_selector_exists : ∃ d, OppositeSelector d := by
  obtain ⟨h, hh, he⟩ := parameterized_partial_recursion opposite_program_partial
  refine ⟨fun u v => h (Nat.pair u v), hh.comp Primrec₂.natPair, ?_⟩
  intro u v x
  exact he (Nat.pair u v) x

theorem specified_diagonal_witness {d : ℕ → ℕ → ℕ} (hd : OppositeSelector d) :
    EffectiveWitness (diagonalOutput 0) (diagonalOutput 1) d := by
  refine ⟨hd.1.to_comp, ?_⟩
  intro u v h0 h1 huv
  rintro (hu | hv)
  · have hvn : d u v ∉ indexSet v := fun hv => Set.disjoint_left.mp huv hu hv
    have he : phi (d u v) (d u v) = Part.some 1 := by
      rw [hd.2 u v (d u v)]
      simp only [oppositeProgram, Nat.unpair_pair, certificate_race_left u v _ hu hvn,
        Part.map_some]
    have hone : d u v ∈ diagonalOutput 1 := by simp [diagonalOutput, he]
    exact hvn (h1 hone)
  · have hun : d u v ∉ indexSet u := fun hu => Set.disjoint_left.mp huv hu hv
    have he : phi (d u v) (d u v) = Part.some 0 := by
      rw [hd.2 u v (d u v)]
      simp only [oppositeProgram, Nat.unpair_pair, certificate_race_right u v _ hun hv,
        Part.map_some]
    have hzero : d u v ∈ diagonalOutput 0 := by simp [diagonalOutput, he]
    exact hun (h0 hzero)

theorem diagonal_effective_pair :
    EffectivelyInseparable (diagonalOutput 0) (diagonalOutput 1) := by
  obtain ⟨d, hd⟩ := opposite_selector_exists
  exact ⟨diagonalOutput_enumerable 0, diagonalOutput_enumerable 1,
    diagonalOutput_disjoint (by decide), d, specified_diagonal_witness hd⟩

end Lemmatheca.ComputabilityTheory.EffectiveInseparability
