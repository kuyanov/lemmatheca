import Lemmatheca.AntiDiagonalNormalization.Basic

namespace Lemmatheca.ComputabilityTheory.AntiDiagonalNormalization

open UniversalComputation EffectiveEnumerations
noncomputable section
open Classical

/-- The request wins a simultaneous first success. -/
def raceStage (d p z n : ℕ) : Part ℕ :=
  ComputableSeparation.raceStage
    (fun w s => certificate p w.unpair.2 s)
    (fun w s => certificate d w.unpair.1 s) (Nat.pair z n)

def winningIndex (d p z n s : ℕ) : ℕ :=
  if certificate p n s then boundedValue s p n - 1 else boundedValue s d z - 1

def raceProcedure (d p z n x : ℕ) : Part ℕ :=
  (raceStage d p z n).bind (fun s => phi (winningIndex d p z n s) x)

/-- Input ((d,p),(z,(n,x))) keeps all four numerical parameters. -/
def raceInput (w : ℕ) : Part ℕ :=
  raceProcedure w.unpair.1.unpair.1 w.unpair.1.unpair.2 w.unpair.2.unpair.1
    w.unpair.2.unpair.2.unpair.1 w.unpair.2.unpair.2.unpair.2

theorem race_stage_spec (d p z n s : ℕ) :
    s ∈ raceStage d p z n ↔
      (certificate p n s ∨ certificate d z s) ∧
      ∀ t < s, ¬ certificate p n t ∧ ¬ certificate d z t := by
  simpa only [raceStage, Nat.unpair_pair] using
    ComputableSeparation.raceStage_spec
      (fun w t => certificate p w.unpair.2 t)
      (fun w t => certificate d w.unpair.1 t) (Nat.pair z n) s

theorem race_stage_domain (d p z n : ℕ) :
    (raceStage d p z n).Dom ↔ (phi p n).Dom ∨ (phi d z).Dom := by
  have h := ComputableSeparation.negativeRace_domain
    (fun w s => certificate p w.unpair.2 s)
    (fun w s => certificate d w.unpair.1 s) (Nat.pair z n)
  simpa only [ComputableSeparation.negativeRace, Part.map_Dom, raceStage,
    Nat.unpair_pair, ← phi_domain] using h

theorem winning_request (d p z n s : ℕ) (hp : certificate p n s) :
    winningIndex d p z n s ∈ phi p n := by
  apply (phi_output p n _).mpr
  refine ⟨s, ?_⟩
  simp only [winningIndex, hp, ↓reduceIte]
  change 0 < boundedValue s p n at hp
  omega

theorem winning_avoidance (d p z n s : ℕ)
    (hs : s ∈ raceStage d p z n) (hp : ¬ certificate p n s) :
    winningIndex d p z n s ∈ phi d z := by
  have hd := ((race_stage_spec d p z n s).mp hs).1.resolve_left hp
  apply (phi_output d z _).mpr
  refine ⟨s, ?_⟩
  simp only [winningIndex, hp, ↓reduceIte]
  change 0 < boundedValue s d z at hd
  omega

theorem race_procedure_at_stage (d p z n s x : ℕ)
    (hs : s ∈ raceStage d p z n) :
    raceProcedure d p z n x = phi (winningIndex d p z n s) x := by
  exact Part.bind_of_mem hs _

theorem race_input_partial : Nat.Partrec raceInput := by
  have hL : Primrec (fun w : ℕ => w.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hR : Primrec (fun w : ℕ => w.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hd : Primrec (fun w : ℕ => w.unpair.1.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hL)
  have hp : Primrec (fun w : ℕ => w.unpair.1.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hL)
  have hz : Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hR)
  have hRR : Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hR)
  have hn : Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hRR)
  have hx : Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hRR)
  have hψ : PrimrecPred (fun v : ℕ × ℕ =>
      certificate v.1.unpair.1.unpair.2 v.1.unpair.2.unpair.2.unpair.1 v.2) :=
    certificate_primitive.comp
      (((hp.comp Primrec.fst).pair (hn.comp Primrec.fst)).pair Primrec.snd)
  have hδ : PrimrecPred (fun v : ℕ × ℕ =>
      certificate v.1.unpair.1.unpair.1 v.1.unpair.2.unpair.1 v.2) :=
    certificate_primitive.comp
      (((hd.comp Primrec.fst).pair (hz.comp Primrec.fst)).pair Primrec.snd)
  have htest : Computable₂ (fun (w s : ℕ) => decide
      (certificate w.unpair.1.unpair.2 w.unpair.2.unpair.2.unpair.1 s ∨
       certificate w.unpair.1.unpair.1 w.unpair.2.unpair.1 s)) :=
    (hψ.or hδ).decide.to_comp
  have hs : Partrec (fun w : ℕ => raceStage w.unpair.1.unpair.1 w.unpair.1.unpair.2
      w.unpair.2.unpair.1 w.unpair.2.unpair.2.unpair.1) :=
    (Partrec.rfind htest.partrec₂).of_eq fun w => by
      simp only [raceStage, ComputableSeparation.raceStage, Nat.unpair_pair]
      rfl
  have hψvalue : Primrec (fun v : ℕ × ℕ =>
      boundedValue v.2 v.1.unpair.1.unpair.2 v.1.unpair.2.unpair.2.unpair.1) :=
    boundedValue_primitive.comp
      ((Primrec.snd.pair (hp.comp Primrec.fst)).pair (hn.comp Primrec.fst))
  have hδvalue : Primrec (fun v : ℕ × ℕ =>
      boundedValue v.2 v.1.unpair.1.unpair.1 v.1.unpair.2.unpair.1) :=
    boundedValue_primitive.comp
      ((Primrec.snd.pair (hd.comp Primrec.fst)).pair (hz.comp Primrec.fst))
  have hwin : Computable (fun v : ℕ × ℕ => winningIndex
      v.1.unpair.1.unpair.1 v.1.unpair.1.unpair.2 v.1.unpair.2.unpair.1
      v.1.unpair.2.unpair.2.unpair.1 v.2) :=
    (Primrec.ite hψ (Primrec.nat_sub.comp hψvalue (Primrec.const 1))
      (Primrec.nat_sub.comp hδvalue (Primrec.const 1))).to_comp
  have hrun : Partrec (fun v : ℕ × ℕ => phi (winningIndex
      v.1.unpair.1.unpair.1 v.1.unpair.1.unpair.2 v.1.unpair.2.unpair.1
      v.1.unpair.2.unpair.2.unpair.1 v.2) v.1.unpair.2.unpair.2.unpair.2) :=
    phi_recursive.comp hwin (hx.to_comp.comp Computable.fst)
  exact Partrec.nat_iff.mp (hs.bind hrun.to₂)

theorem race_procedure_partial (d p : ℕ) :
    Partrec (fun w : ℕ × (ℕ × ℕ) => raceProcedure d p w.1 w.2.1 w.2.2) := by
  have hcode : Primrec (fun w : ℕ × (ℕ × ℕ) =>
      Nat.pair (Nat.pair d p) (Nat.pair w.1 (Nat.pair w.2.1 w.2.2))) :=
    Primrec₂.natPair.comp (Primrec.const (Nat.pair d p))
      (Primrec₂.natPair.comp Primrec.fst
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))
  exact ((Partrec.nat_iff.mpr race_input_partial).comp hcode.to_comp).of_eq fun w => by
    simp only [raceInput, Nat.unpair_pair]

end
end Lemmatheca.ComputabilityTheory.AntiDiagonalNormalization
