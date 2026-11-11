import Lemmatheca.ArslanovCompletenessCriterion.DNC

namespace Lemmatheca.ComputabilityTheory.ArslanovCompletenessCriterion
open UniversalComputation OracleComputation
open BusyBeaverFunctions (ordinaryProgram)
noncomputable section

def diagonalSimulationInput (w : ℕ) : Part ℕ :=
  (phi w.unpair.1 w.unpair.1).bind fun k => phi k w.unpair.2

theorem diagonal_simulation_input_partial : Nat.Partrec diagonalSimulationInput := by
  apply Partrec.nat_iff.mp
  exact (phi_recursive.comp (Computable.fst.comp Computable.unpair)
    (Computable.fst.comp Computable.unpair)).bind
      (phi_recursive.comp Computable.snd
        (Computable.snd.comp (Computable.unpair.comp Computable.fst))).to₂

def diagonalSimulationMaster : ℕ :=
  Classical.choose (phi_complete diagonal_simulation_input_partial)

def diagonalSimulationIndex (n : ℕ) : ℕ := specialize diagonalSimulationMaster n

theorem diagonal_simulation_index_primitive : Primrec diagonalSimulationIndex := by
  exact specialize_primitive.comp (Primrec.const _) Primrec.id

theorem diagonal_simulation_eval (n x : ℕ) :
    phi (diagonalSimulationIndex n) x = (phi n n).bind (fun k => phi k x) := by
  rw [diagonalSimulationIndex, specialize_eval]
  have h := congrFun (Classical.choose_spec (phi_complete diagonal_simulation_input_partial))
    (Nat.pair n x)
  simpa only [diagonalSimulationMaster, diagonalSimulationInput, Nat.unpair_pair] using h

theorem diagonal_simulation_copy (n k : ℕ) (hk : k ∈ phi n n) :
    ∀ x, phi (diagonalSimulationIndex n) x = phi k x := by
  intro x
  rw [diagonal_simulation_eval, Part.eq_some_iff.mpr hk, Part.bind_some]

theorem diagonal_simulation_domain (n k : ℕ) (hk : k ∈ phi n n) :
    EffectiveEnumerations.indexSet (diagonalSimulationIndex n) =
      EffectiveEnumerations.indexSet k := by
  ext x
  change (phi (diagonalSimulationIndex n) x).Dom ↔ (phi k x).Dom
  rw [diagonal_simulation_copy n k hk x]

def fpfDNC (f : ℕ → ℕ) (n : ℕ) : ℕ := f (diagonalSimulationIndex n)

theorem fpf_dnc (f : ℕ → ℕ) (hf : FPF f) :
    EffectivelyClosedClassesAndDnc.DNC (fpfDNC f) := by
  intro n k hk he
  apply hf (diagonalSimulationIndex n)
  change f (diagonalSimulationIndex n) = k at he
  rw [he]
  exact (diagonal_simulation_domain n k hk).symm

def fpfDNCCode (c : Code) : Code :=
  .comp c (embed (ordinaryProgram diagonalSimulationIndex
    diagonal_simulation_index_primitive.to_comp))

theorem fpf_dnc_code_eval (B : Set ℕ) (f : ℕ → ℕ) (c : Code)
    (hc : ∀ n, eval B c n = Part.some (f n)) (n : ℕ) :
    eval B (fpfDNCCode c) n = Part.some (fpfDNC f n) := by
  simp only [fpfDNCCode, eval, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval,
    Part.bind_some, hc, fpfDNC]

theorem computes_dnc_of_fpf (B : Set ℕ) (hB : ComputesFPF B) :
    ∃ g : ℕ → ℕ, PartialComputable B (fun n => Part.some (g n)) ∧
      EffectivelyClosedClassesAndDnc.DNC g := by
  obtain ⟨f, ⟨c, hc⟩, hf⟩ := hB
  refine ⟨fpfDNC f, ⟨fpfDNCCode c, ?_⟩, fpf_dnc f hf⟩
  funext n
  exact fpf_dnc_code_eval B f c (fun i => congrFun hc i) n

theorem computes_fpf_iff_dnc (B : Set ℕ) :
    ComputesFPF B ↔ ∃ g : ℕ → ℕ,
      PartialComputable B (fun n => Part.some (g n)) ∧
        EffectivelyClosedClassesAndDnc.DNC g := by
  constructor
  · exact computes_dnc_of_fpf B
  · rintro ⟨g, hc, hg⟩
    exact computes_fpf_of_dnc B g hg hc

end
end Lemmatheca.ComputabilityTheory.ArslanovCompletenessCriterion
