import Lemmatheca.FiniteInjuryAndPostsProblem.Construction

/-! Finite-state update identities, ownership, and strategy-data provenance. -/
namespace Lemmatheca.ComputabilityTheory.FiniteInjury

set_option backward.isDefEq.respectTransparency false

open PostsTheorem

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem beta_outside (u x : ℕ) (h : FiniteSequenceCoding.length u ≤ x) :
    beta u x = 0 := by
  unfold beta
  rw [FiniteSequenceCoding.entry_out_of_range u x h]

private theorem beta_tabulate (n : ℕ) (f : ℕ → ℕ)
    (hf : ∀ j, f j = 0 ∨ f j = 1) (j : ℕ) :
    beta (tabulate n f) j = if j < n then f j else 0 := by
  unfold beta
  rw [tabulate_entry]
  by_cases h : j < n
  · rcases hf j with hz | ho
    · simp [h, hz]
    · simp [h, ho]
  · simp [h]

private theorem target_mem (i s x : ℕ) :
    x ∈ targetStage i s ↔ beta (targetCode (stage s) i) x = 1 := by
  by_cases h : i % 2 = 0 <;>
    simp [targetStage, targetCode, leftStage, rightStage, finiteOracle, h]

private theorem oracle_mem (i s x : ℕ) :
    x ∈ oracleStage i s ↔ beta (oracleCode (stage s) i) x = 1 := by
  by_cases h : i % 2 = 0 <;>
    simp [oracleStage, oracleCode, leftStage, rightStage, finiteOracle, h]

theorem state_lengths (s : ℕ) :
    FiniteSequenceCoding.length (aCode (stage s)) = s ∧
      FiniteSequenceCoding.length (bCode (stage s)) = s ∧
      FiniteSequenceCoding.length (dCode (stage s)) = s ∧
      FiniteSequenceCoding.length (rCode (stage s)) = s := by
  cases s with
  | zero => simp [stage, aCode, bCode, dCode, rCode, FiniteSequenceCoding.length]
  | succ s => simp only [stage, next, aCode, bCode, dCode, rCode, tabulate_length, and_self]

theorem state_entries_binary (s j : ℕ) :
    (FiniteSequenceCoding.entry (aCode (stage s)) j = 0 ∨
      FiniteSequenceCoding.entry (aCode (stage s)) j = 1) ∧
    (FiniteSequenceCoding.entry (bCode (stage s)) j = 0 ∨
      FiniteSequenceCoding.entry (bCode (stage s)) j = 1) ∧
    (FiniteSequenceCoding.entry (dCode (stage s)) j = 0 ∨
      FiniteSequenceCoding.entry (dCode (stage s)) j = 1) := by
  cases s with
  | zero => simp [stage, aCode, bCode, dCode, FiniteSequenceCoding.entry]
  | succ s =>
    simp only [stage, next, aCode, bCode, dCode, tabulate_entry]
    by_cases hj : j < s + 1
    · simp only [ite_eq_left hj]
      constructor
      · split_ifs <;> simp [beta_bits]
      · constructor
        · split_ifs <;> simp [beta_bits]
        · split_ifs <;> simp [flag, beta_bits]
    · simp [hj]

theorem stage_bounds (s : ℕ) : leftStage s ⊆ Set.Iio s ∧ rightStage s ⊆ Set.Iio s := by
  constructor
  · intro x hx
    change beta (aCode (stage s)) x = 1 at hx
    change x < s
    by_contra h
    have hz := beta_outside (aCode (stage s)) x (by rw [(state_lengths s).1]; omega)
    omega
  · intro x hx
    change beta (bCode (stage s)) x = 1 at hx
    change x < s
    by_contra h
    have hz := beta_outside (bCode (stage s)) x (by rw [(state_lengths s).2.1]; omega)
    omega

theorem stage_bits_binary (s x : ℕ) :
    (leftBit s x = 0 ∨ leftBit s x = 1) ∧
      (rightBit s x = 0 ∨ rightBit s x = 1) := by
  exact ⟨beta_bits _ _, beta_bits _ _⟩

theorem left_bit_succ (s x : ℕ) :
    leftBit (s + 1) x =
      if HasAction s (stage s) ∧ priority s (stage s) % 2 = 0 ∧ x = witnessAt s
      then 1 else leftBit s x := by
  have hf : ∀ q, (if HasAction s (stage s) ∧ priority s (stage s) % 2 = 0 ∧
      q = chosenWitness s (stage s) then 1 else beta (aCode (stage s)) q) = 0 ∨
      (if HasAction s (stage s) ∧ priority s (stage s) % 2 = 0 ∧
      q = chosenWitness s (stage s) then 1 else beta (aCode (stage s)) q) = 1 := by
    intro q
    split_ifs <;> simp [beta_bits]
  have he := beta_tabulate (s + 1) _ hf x
  change leftBit (s + 1) x = _ at he
  rw [he]
  by_cases hx : x < s + 1
  · simp only [ite_eq_left hx, witnessAt, leftBit]
  · have ho : leftBit s x = 0 :=
      beta_outside _ _ (by rw [(state_lengths s).1]; omega)
    have hp : ¬ (HasAction s (stage s) ∧ priority s (stage s) % 2 = 0 ∧ x = witnessAt s) := by
      rintro ⟨ha, _, hw⟩
      have hb := (chosen_eligible s (stage s) ha).2.1
      change witnessAt s ≤ s at hb
      omega
    simp only [ite_eq_right hx, ite_eq_right hp, ho]

theorem right_bit_succ (s x : ℕ) :
    rightBit (s + 1) x =
      if HasAction s (stage s) ∧ priority s (stage s) % 2 ≠ 0 ∧ x = witnessAt s
      then 1 else rightBit s x := by
  have hf : ∀ q, (if HasAction s (stage s) ∧ priority s (stage s) % 2 ≠ 0 ∧
      q = chosenWitness s (stage s) then 1 else beta (bCode (stage s)) q) = 0 ∨
      (if HasAction s (stage s) ∧ priority s (stage s) % 2 ≠ 0 ∧
      q = chosenWitness s (stage s) then 1 else beta (bCode (stage s)) q) = 1 := by
    intro q
    split_ifs <;> simp [beta_bits]
  have he := beta_tabulate (s + 1) _ hf x
  change rightBit (s + 1) x = _ at he
  rw [he]
  by_cases hx : x < s + 1
  · simp only [ite_eq_left hx, witnessAt, rightBit]
  · have ho : rightBit s x = 0 :=
      beta_outside _ _ (by rw [(state_lengths s).2.1]; omega)
    have hp : ¬ (HasAction s (stage s) ∧ priority s (stage s) % 2 ≠ 0 ∧ x = witnessAt s) := by
      rintro ⟨ha, _, hw⟩
      have hb := (chosen_eligible s (stage s) ha).2.1
      change witnessAt s ≤ s at hb
      omega
    simp only [ite_eq_right hx, ite_eq_right hp, ho]

theorem stage_monotone : Monotone leftStage ∧ Monotone rightStage := by
  constructor
  · apply monotone_nat_of_le_succ
    intro s x hx
    change leftBit s x = 1 at hx
    change leftBit (s + 1) x = 1
    rw [left_bit_succ]
    split_ifs <;> simp_all
  · apply monotone_nat_of_le_succ
    intro s x hx
    change rightBit s x = 1 at hx
    change rightBit (s + 1) x = 1
    rw [right_bit_succ]
    split_ifs <;> simp_all

theorem acted_witness {i s : ℕ} (h : Acts i s) :
    i ≤ s ∧ witnessAt s ≤ s ∧ witnessAt s ∈ reservoir i ∧
      flag (stage s) i = 0 ∧ witnessAt s ∉ targetStage i s ∧
      (∀ j < i, restraint (stage s) j ≤ witnessAt s) ∧
      finiteValue (oracleCode (stage s) i) (s + 1) (i / 2) (witnessAt s) = 1 := by
  rcases acted_eligible h with ⟨hi, hx, hn, hd, ht, hr, hv⟩
  refine ⟨hi, hx, hn, hd, ?_, hr, hv⟩
  intro hm
  have hm' := (target_mem i s (witnessAt s)).mp hm
  omega


private theorem left_stage_step (s : ℕ) :
    leftStage (s + 1) =
      if HasAction s (stage s) ∧ priority s (stage s) % 2 = 0
      then insert (witnessAt s) (leftStage s) else leftStage s := by
  ext x
  change (leftBit (s + 1) x = 1) ↔ _
  rw [left_bit_succ]
  by_cases ha : HasAction s (stage s)
  · by_cases hp : priority s (stage s) % 2 = 0
    · by_cases hx : x = witnessAt s <;>
        simp_all [leftStage, finiteOracle, leftBit]
    · simp_all [leftStage, finiteOracle, leftBit]
  · simp_all [leftStage, finiteOracle, leftBit]

private theorem right_stage_step (s : ℕ) :
    rightStage (s + 1) =
      if HasAction s (stage s) ∧ priority s (stage s) % 2 ≠ 0
      then insert (witnessAt s) (rightStage s) else rightStage s := by
  ext x
  change (rightBit (s + 1) x = 1) ↔ _
  rw [right_bit_succ]
  by_cases ha : HasAction s (stage s)
  · by_cases hp : priority s (stage s) % 2 = 0
    · simp_all [rightStage, finiteOracle, rightBit]
    · by_cases hx : x = witnessAt s <;>
        simp_all [rightStage, finiteOracle, rightBit]
  · simp_all [rightStage, finiteOracle, rightBit]

private theorem source_of_updates (S : ℕ → Set ℕ) (P : ℕ → Prop)
    (hzero : S 0 = ∅)
    (hstep : ∀ s, S (s + 1) =
      if HasAction s (stage s) ∧ P (priority s (stage s))
      then insert (witnessAt s) (S s) else S s) (s x : ℕ) :
    x ∈ S s ↔ ∃ t < s, ∃ i, Acts i t ∧ P i ∧ witnessAt t = x := by
  induction s generalizing x with
  | zero => simp [hzero]
  | succ s ih =>
    rw [hstep s]
    by_cases hc : HasAction s (stage s) ∧ P (priority s (stage s))
    · rw [ite_eq_left hc]
      constructor
      · intro hm
        rcases Set.mem_insert_iff.mp hm with hx | hm
        · exact ⟨s, Nat.lt_succ_self s, priority s (stage s),
            (acts_iff _ _).mpr ⟨hc.1, rfl⟩, hc.2, hx.symm⟩
        · rcases (ih x).mp hm with ⟨t, ht, i, hai, hPi, hw⟩
          exact ⟨t, Nat.lt_succ_of_lt ht, i, hai, hPi, hw⟩
      · rintro ⟨t, ht, i, hai, hPi, hw⟩
        by_cases hts : t < s
        · exact Set.mem_insert_of_mem _ ((ih x).mpr ⟨t, hts, i, hai, hPi, hw⟩)
        · have he : t = s := by omega
          subst t
          exact Set.mem_insert_iff.mpr (Or.inl hw.symm)
    · rw [ite_eq_right hc]
      constructor
      · intro hm
        rcases (ih x).mp hm with ⟨t, ht, i, hai, hPi, hw⟩
        exact ⟨t, Nat.lt_succ_of_lt ht, i, hai, hPi, hw⟩
      · rintro ⟨t, ht, i, hai, hPi, hw⟩
        by_cases hts : t < s
        · exact (ih x).mpr ⟨t, hts, i, hai, hPi, hw⟩
        · have he : t = s := by omega
          subst t
          rcases (acts_iff i s).mp hai with ⟨ha, hp⟩
          exact False.elim (hc ⟨ha, by simpa only [hp] using hPi⟩)

theorem acted_stage_updates {i s : ℕ} (h : Acts i s) :
    targetStage i (s + 1) = insert (witnessAt s) (targetStage i s) ∧
      oracleStage i (s + 1) = oracleStage i s := by
  rcases (acts_iff i s).mp h with ⟨ha, hp⟩
  by_cases hi : i % 2 = 0
  · have hl : leftStage (s + 1) = insert (witnessAt s) (leftStage s) := by
      rw [left_stage_step]
      simp only [ha, hp, hi, and_self, ite_true]
    have hr : rightStage (s + 1) = rightStage s := by
      rw [right_stage_step]
      simp [hp, hi]
    simpa only [targetStage, oracleStage, ite_eq_left hi] using And.intro hl hr
  · have hr : rightStage (s + 1) = insert (witnessAt s) (rightStage s) := by
      rw [right_stage_step]
      simp only [ha, hp]
      simp [hi]
    have hl : leftStage (s + 1) = leftStage s := by
      rw [left_stage_step]
      simp [hp, hi]
    simpa only [targetStage, oracleStage, ite_eq_right hi] using And.intro hr hl

theorem left_stage_source (s x : ℕ) : x ∈ leftStage s ↔
    ∃ t < s, ∃ i, Acts i t ∧ i % 2 = 0 ∧ witnessAt t = x := by
  exact source_of_updates leftStage (fun i => i % 2 = 0)
    (by ext q; simp [leftStage, stage, aCode, finiteOracle, beta, FiniteSequenceCoding.entry])
    (fun u => by
      by_cases hu : HasAction u (stage u) ∧ priority u (stage u) % 2 = 0 <;>
        simpa only [hu, ite_true, ite_false] using left_stage_step u) s x

theorem right_stage_source (s x : ℕ) : x ∈ rightStage s ↔
    ∃ t < s, ∃ i, Acts i t ∧ i % 2 ≠ 0 ∧ witnessAt t = x := by
  exact source_of_updates rightStage (fun i => i % 2 ≠ 0)
    (by ext q; simp [rightStage, stage, bCode, finiteOracle, beta, FiniteSequenceCoding.entry])
    (fun s => by simpa using right_stage_step s) s x

theorem private_target_source {i x : ℕ} (hx : x ∈ reservoir i) (s : ℕ) :
    x ∈ targetStage i s ↔ ∃ t < s, Acts i t ∧ witnessAt t = x := by
  have own (t j : ℕ) (hj : Acts j t) (hw : witnessAt t = x) : j = i := by
    have hn := (acted_witness hj).2.2.1
    rw [hw] at hn
    change x.unpair.1 = j at hn
    change x.unpair.1 = i at hx
    exact hn.symm.trans hx
  by_cases hi : i % 2 = 0
  · simp only [targetStage, ite_eq_left hi]
    rw [left_stage_source]
    constructor
    · rintro ⟨t, ht, j, hj, _, hw⟩
      have he := own t j hj hw
      subst j
      exact ⟨t, ht, hj, hw⟩
    · rintro ⟨t, ht, hai, hw⟩
      exact ⟨t, ht, i, hai, hi, hw⟩
  · simp only [targetStage, ite_eq_right hi]
    rw [right_stage_source]
    constructor
    · rintro ⟨t, ht, j, hj, _, hw⟩
      have he := own t j hj hw
      subst j
      exact ⟨t, ht, hj, hw⟩
    · rintro ⟨t, ht, hai, hw⟩
      exact ⟨t, ht, i, hai, hi, hw⟩

theorem private_union_source {i x : ℕ} (hx : x ∈ reservoir i) :
    x ∈ targetSet i ↔ ∃ t, Acts i t ∧ witnessAt t = x := by
  have hu : x ∈ targetSet i ↔ ∃ s, x ∈ targetStage i s := by
    by_cases hi : i % 2 = 0 <;> simp [targetSet, targetStage, leftSet, rightSet, hi]
  rw [hu]
  constructor
  · rintro ⟨s, hs⟩
    rcases (private_target_source hx s).mp hs with ⟨t, _, ht, hw⟩
    exact ⟨t, ht, hw⟩
  · rintro ⟨t, ht, hw⟩
    exact ⟨t + 1, (private_target_source hx (t + 1)).mpr ⟨t, Nat.lt_succ_self t, ht, hw⟩⟩

theorem flag_succ (s i : ℕ) :
    flag (stage (s + 1)) i =
      if HasAction s (stage s) then
        if i < priority s (stage s) then flag (stage s) i
        else if i = priority s (stage s) then 1 else 0
      else flag (stage s) i := by
  let f := fun j => if HasAction s (stage s) then
    if j < priority s (stage s) then flag (stage s) j
    else if j = priority s (stage s) then 1 else 0
    else flag (stage s) j
  have hf : ∀ j, f j = 0 ∨ f j = 1 := by
    intro j
    dsimp [f]
    split_ifs <;> simp [flag, beta_bits]
  have he := beta_tabulate (s + 1) f hf i
  change flag (stage (s + 1)) i = if i < s + 1 then f i else 0 at he
  rw [he]
  by_cases hi : i < s + 1
  · simp only [hi, ite_true, f]
  · have hz : flag (stage s) i = 0 :=
      beta_outside _ _ (by rw [(state_lengths s).2.2.1]; omega)
    have hp := priority_bound s (stage s)
    dsimp [f]
    split_ifs <;> simp_all [HasAction]
    omega

theorem restraint_succ (s i : ℕ) :
    restraint (stage (s + 1)) i =
      if HasAction s (stage s) then
        if i < priority s (stage s) then restraint (stage s) i
        else if i = priority s (stage s) then s + 1 else 0
      else restraint (stage s) i := by
  have he := tabulate_entry (s + 1)
    (fun j => if HasAction s (stage s) then
      if j < priority s (stage s) then restraint (stage s) j
      else if j = priority s (stage s) then s + 1 else 0
      else restraint (stage s) j) i
  change restraint (stage (s + 1)) i = _ at he
  rw [he]
  by_cases hi : i < s + 1
  · simp only [hi, ite_true]
  · have hz : restraint (stage s) i = 0 :=
      FiniteSequenceCoding.entry_out_of_range _ _ (by rw [(state_lengths s).2.2.2]; omega)
    have hp := priority_bound s (stage s)
    split_ifs <;> simp_all [HasAction]
    omega

theorem flag_binary (s i : ℕ) : flag (stage s) i = 0 ∨ flag (stage s) i = 1 := by
  exact beta_bits _ _

theorem restraints_bounded (s i : ℕ) : restraint (stage s) i ≤ s := by
  induction s with
  | zero => simp [stage, restraint, rCode, FiniteSequenceCoding.entry]
  | succ s ih =>
    rw [restraint_succ]
    split_ifs <;> omega

theorem zero_flag_zero_restraint (s i : ℕ) (h : flag (stage s) i = 0) :
    restraint (stage s) i = 0 := by
  induction s with
  | zero => simp [stage, restraint, rCode, FiniteSequenceCoding.entry]
  | succ s ih =>
    rw [flag_succ] at h
    rw [restraint_succ]
    split_ifs at h ⊢ <;> simp_all

theorem acted_data {i s : ℕ} (h : Acts i s) :
    flag (stage (s + 1)) i = 1 ∧ restraint (stage (s + 1)) i = s + 1 := by
  rcases (acts_iff i s).mp h with ⟨ha, hp⟩
  simp [flag_succ, restraint_succ, ha, hp]

theorem preserve_data {s i : ℕ} (h : ∀ j ≤ i, ¬ Acts j s) :
    flag (stage (s + 1)) i = flag (stage s) i ∧
      restraint (stage (s + 1)) i = restraint (stage s) i := by
  by_cases ha : HasAction s (stage s)
  · have hp : i < priority s (stage s) := by
      by_contra hn
      have ha' : Acts (priority s (stage s)) s :=
        (acts_iff _ _).mpr ⟨ha, rfl⟩
      exact h _ (by omega) ha'
    simp [flag_succ, restraint_succ, ha, hp]
  · simp [flag_succ, restraint_succ, ha]

theorem reset_data {s i j : ℕ} (hj : Acts j s) (hji : j < i) :
    flag (stage (s + 1)) i = 0 ∧ restraint (stage (s + 1)) i = 0 := by
  rcases (acts_iff j s).mp hj with ⟨ha, hp⟩
  simp [flag_succ, restraint_succ, ha, hp, show ¬ i < j by omega,
    show i ≠ j by omega]

theorem flag_provenance (s i : ℕ) (h : flag (stage s) i = 1) :
    ∃ t < s, Acts i t ∧ restraint (stage s) i = t + 1 ∧
      ∀ u, t < u → u < s → ∀ j < i, ¬ Acts j u := by
  induction s with
  | zero => simp [stage, flag, dCode, beta, FiniteSequenceCoding.entry] at h
  | succ s ih =>
    by_cases hai : Acts i s
    · refine ⟨s, by omega, hai, (acted_data hai).2, ?_⟩
      intro u hsu hus j hji
      omega
    · have hn : ∀ j ≤ i, ¬ Acts j s := by
        intro j hji hj
        by_cases heq : j = i
        · subst j; exact hai hj
        · have hz := (reset_data hj (by omega : j < i)).1
          omega
      have hd := preserve_data hn
      have ho : flag (stage s) i = 1 := hd.1.symm.trans h
      obtain ⟨t, hts, ht, hr, hno⟩ := ih ho
      refine ⟨t, by omega, ht, hd.2.trans hr, ?_⟩
      intro u htu hus j hji
      by_cases hu : u < s
      · exact hno u htu hu j hji
      · have he : u = s := by omega
        subst u
        exact hn j (by omega)

theorem target_stage_union (i x : ℕ) :
    x ∈ targetSet i ↔ ∃ s, x ∈ targetStage i s := by
  by_cases h : i % 2 = 0 <;> simp [targetSet, targetStage, leftSet, rightSet, h]

theorem oracle_stage_union (i x : ℕ) :
    x ∈ oracleSet i ↔ ∃ s, x ∈ oracleStage i s := by
  by_cases h : i % 2 = 0 <;> simp [oracleSet, oracleStage, leftSet, rightSet, h]

theorem target_stage_monotone (i : ℕ) : Monotone (targetStage i) := by
  by_cases h : i % 2 = 0
  · intro s t hst
    simpa [targetStage, h] using stage_monotone.1 hst
  · intro s t hst
    simpa [targetStage, h] using stage_monotone.2 hst

theorem oracle_stage_monotone (i : ℕ) : Monotone (oracleStage i) := by
  by_cases h : i % 2 = 0
  · intro s t hst
    simpa [oracleStage, h] using stage_monotone.2 hst
  · intro s t hst
    simpa [oracleStage, h] using stage_monotone.1 hst

end
end Lemmatheca.ComputabilityTheory.FiniteInjury
