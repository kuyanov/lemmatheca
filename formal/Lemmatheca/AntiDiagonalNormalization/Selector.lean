import Lemmatheca.AntiDiagonalNormalization.Race

namespace Lemmatheca.ComputabilityTheory.AntiDiagonalNormalization

open UniversalComputation EffectiveEnumerations
noncomputable section

/-- A single ordinary program for the joint race before d,p vary. -/
def raceMaster : ℕ := Classical.choose (phi_complete race_input_partial)

def raceFamilyIndex (d p : ℕ) : ℕ := specialize raceMaster (Nat.pair d p)

theorem race_master_eval (d p z n x : ℕ) :
    phi raceMaster (Nat.pair (Nat.pair d p) (Nat.pair z (Nat.pair n x))) =
      raceProcedure d p z n x := by
  simpa only [raceMaster, raceInput, Nat.unpair_pair] using
    congrFun (Classical.choose_spec (phi_complete race_input_partial))
      (Nat.pair (Nat.pair d p) (Nat.pair z (Nat.pair n x)))

theorem race_family_eval (d p z n x : ℕ) :
    phi (raceFamilyIndex d p) (Nat.pair z (Nat.pair n x)) =
      raceProcedure d p z n x := by
  rw [raceFamilyIndex, specialize_eval, race_master_eval]

def raceAuxiliary (d p : ℕ) : ℕ :=
  Classical.choose (UniformSelfReference.specified_partial_family_selector
    (raceFamilyIndex d p) (race_family_eval d p))

def selector (d p n : ℕ) : ℕ :=
  UniformSelfReference.selector (RecursionTheorem.selfSpecialize (raceAuxiliary d p)) n

theorem selector_primitive (d p : ℕ) : Primrec (selector d p) := by
  exact (Classical.choose_spec (UniformSelfReference.specified_partial_family_selector
    (raceFamilyIndex d p) (race_family_eval d p))).2.1

theorem selector_eval (d p n x : ℕ) :
    phi (selector d p n) x = raceProcedure d p (selector d p n) n x := by
  exact (Classical.choose_spec (UniformSelfReference.specified_partial_family_selector
    (raceFamilyIndex d p) (race_family_eval d p))).2.2 n x

theorem forbidden_winning_branch (d p n s : ℕ) (hd : PartialFPF (phi d))
    (hs : s ∈ raceStage d p (selector d p n) n) : certificate p n s := by
  by_contra hp
  have hj := winning_avoidance d p (selector d p n) n s hs hp
  apply hd (selector d p n) (winningIndex d p (selector d p n) n s) hj
  ext x
  change (phi (winningIndex d p (selector d p n) n s) x).Dom ↔
    (phi (selector d p n) x).Dom
  rw [selector_eval, race_procedure_at_stage d p (selector d p n) n s x hs]

theorem selector_copies (d p n j : ℕ) (hd : PartialFPF (phi d))
    (hj : j ∈ phi p n) : ∀ x, phi (selector d p n) x = phi j x := by
  have hr : (raceStage d p (selector d p n) n).Dom :=
    (race_stage_domain d p (selector d p n) n).mpr
      (Or.inl (Part.dom_iff_mem.mpr ⟨j, hj⟩))
  obtain ⟨s, hs⟩ := Part.dom_iff_mem.mp hr
  have hp := forbidden_winning_branch d p n s hd hs
  have hw : winningIndex d p (selector d p n) n s = j :=
    Part.mem_unique (winning_request d p (selector d p n) n s hp) hj
  intro x
  rw [selector_eval, race_procedure_at_stage d p (selector d p n) n s x hs, hw]

theorem selector_domains (d p n j : ℕ) (hd : PartialFPF (phi d))
    (hj : j ∈ phi p n) : indexSet (selector d p n) = indexSet j := by
  ext x
  change (phi (selector d p n) x).Dom ↔ (phi j x).Dom
  rw [selector_copies d p n j hd hj]

theorem selector_avoids (d p n : ℕ) (hd : PartialFPF (phi d))
    (hn : ¬ (phi p n).Dom) : ¬ (phi d (selector d p n)).Dom := by
  intro hδ
  have hr := (race_stage_domain d p (selector d p n) n).mpr (Or.inr hδ)
  obtain ⟨s, hs⟩ := Part.dom_iff_mem.mp hr
  exact hn ((phi_domain p n).mpr ⟨s, forbidden_winning_branch d p n s hd hs⟩)

theorem selector_undefined_request (d p n x : ℕ) (hd : PartialFPF (phi d))
    (hn : ¬ (phi p n).Dom) : phi (selector d p n) x = Part.none := by
  have hδ := selector_avoids d p n hd hn
  have hr : raceStage d p (selector d p n) n = Part.none :=
    Part.eq_none_iff'.mpr (fun h =>
      ((race_stage_domain d p (selector d p n) n).mp h).elim hn hδ)
  rw [selector_eval, raceProcedure, hr, Part.bind_none]

theorem specified_adn (d p : ℕ) (hd : PartialFPF (phi d)) :
    Primrec (selector d p) ∧ TotalizesAvoiding (phi d) (phi p) (selector d p) := by
  refine ⟨selector_primitive d p, ⟨(selector_primitive d p).to_comp, ?_⟩, ?_⟩
  · exact fun n j hj => selector_domains d p n j hd hj
  · exact fun n hn => selector_avoids d p n hd hn

theorem adn {δ ψ : ℕ → Part ℕ} (hδ : Nat.Partrec δ) (hψ : Nat.Partrec ψ)
    (hd : PartialFPF δ) :
    ∃ f : ℕ → ℕ, Primrec f ∧ TotalizesAvoiding δ ψ f ∧
      (∀ n j, j ∈ ψ n → ∀ x, phi (f n) x = phi j x) ∧
      (∀ n, ¬ (ψ n).Dom → ∀ x, phi (f n) x = Part.none) := by
  obtain ⟨d, hdδ⟩ := phi_complete hδ
  obtain ⟨p, hpψ⟩ := phi_complete hψ
  subst δ
  subst ψ
  exact ⟨selector d p, (specified_adn d p hd).1, (specified_adn d p hd).2,
    fun n j hj => selector_copies d p n j hd hj,
    fun n hn x => selector_undefined_request d p n x hd hn⟩

end
end Lemmatheca.ComputabilityTheory.AntiDiagonalNormalization
