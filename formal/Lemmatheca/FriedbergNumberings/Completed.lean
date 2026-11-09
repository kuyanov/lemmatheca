import Lemmatheca.FriedbergNumberings.Endpoints

namespace Lemmatheca.ComputabilityTheory.FriedbergNumberings

open UniversalComputation EffectiveEnumerations

noncomputable section
attribute [local instance] Classical.propDecidable

def completedRow (e : ℕ) : Set ℕ :=
  if e = 0 then Set.univ
  else if e = 2 then ∅
  else if e % 2 = 1 then preliminaryRow (e / 2)
  else Set.Iic (omittedEndpoint ((e - 4) / 2))

def recognizer (e y : ℕ) : Part ℕ :=
  if e = 0 then Part.some 0
  else if e = 2 then Part.none
  else if e % 2 = 1 then preliminaryRecognizer (e / 2) y
  else if y ≤ omittedEndpoint ((e - 4) / 2) then Part.some 0 else Part.none

theorem completed_rows_equations : completedRow 0 = Set.univ ∧ completedRow 2 = ∅ ∧
    (∀ n, completedRow (2 * n + 1) = preliminaryRow n) ∧
      ∀ n, completedRow (2 * n + 4) = Set.Iic (omittedEndpoint n) := by
  refine ⟨by simp [completedRow], by simp [completedRow], ?_, ?_⟩
  · intro n
    have h0 : 2 * n + 1 ≠ 0 := by omega
    have h2 : 2 * n + 1 ≠ 2 := by omega
    have hm : (2 * n + 1) % 2 = 1 := by omega
    have hd : (2 * n + 1) / 2 = n := by omega
    simp [completedRow, h2, hm, hd]
  · intro n
    have h0 : 2 * n + 4 ≠ 0 := by omega
    have h2 : 2 * n + 4 ≠ 2 := by omega
    have hm : (2 * n + 4) % 2 = 0 := by omega
    have hd : (2 * n + 4 - 4) / 2 = n := by omega
    simp [completedRow, h2, hm]

theorem recognizer_partial : Partrec₂ recognizer := by
  have h0 : Computable (fun p : ℕ × ℕ => decide (p.1 = 0)) :=
    Primrec.eq.decide.to_comp.comp Computable.fst (Computable.const 0)
  have h2 : Computable (fun p : ℕ × ℕ => decide (p.1 = 2)) :=
    Primrec.eq.decide.to_comp.comp Computable.fst (Computable.const 2)
  have hdiv : Computable (fun p : ℕ × ℕ => p.1 / 2) :=
    Primrec.nat_div.to_comp.comp Computable.fst (Computable.const 2)
  have hodd : Computable (fun p : ℕ × ℕ => decide (p.1 % 2 = 1)) :=
    Primrec.eq.decide.to_comp.comp
      (Primrec.nat_mod.to_comp.comp Computable.fst (Computable.const 2)) (Computable.const 1)
  have hb : Computable (fun p : ℕ × ℕ => omittedEndpoint ((p.1 - 4) / 2)) :=
    omitted_endpoint_computable.comp (Primrec.nat_div.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.fst (Computable.const 4)) (Computable.const 2))
  have hy : Computable (fun p : ℕ × ℕ => decide (p.2 ≤ omittedEndpoint ((p.1 - 4) / 2))) :=
    Primrec.nat_le.decide.to_comp.comp Computable.snd hb
  have hp : Partrec (fun p : ℕ × ℕ => recognizer p.1 p.2) :=
    (Partrec.cond h0 (Computable.const 0).partrec
      (Partrec.cond h2 Partrec.none
        (Partrec.cond hodd (preliminary_recognizer_partial.comp hdiv Computable.snd)
          (Partrec.cond hy (Computable.const 0).partrec Partrec.none)))).of_eq
      (fun p => by simp only [recognizer, Bool.cond_decide]; rfl)
  exact hp

theorem recognizer_spec (e y : ℕ) :
    recognizer e y = if y ∈ completedRow e then Part.some 0 else Part.none := by
  classical
  classical
  by_cases h0 : e = 0
  · simp [recognizer, completedRow, h0]
  by_cases h2 : e = 2
  · simp [recognizer, completedRow, h2]
  by_cases ho : e % 2 = 1
  · simp [recognizer, completedRow, h0, h2, ho, preliminary_recognizer_spec]
  · simp [recognizer, completedRow, h0, h2, ho]

theorem completed_uniform : UniformCE completedRow := by
  have hp : Partrec (fun z : ℕ => recognizer z.unpair.1 z.unpair.2) :=
    recognizer_partial.comp (Computable.fst.comp Computable.unpair)
      (Computable.snd.comp Computable.unpair)
  apply hp.dom_re.of_eq
  intro z
  rw [recognizer_spec]
  by_cases hz : z.unpair.2 ∈ completedRow z.unpair.1 <;> simp [hz]

private theorem row_index_cases (e : ℕ) :
    e = 0 ∨ e = 2 ∨ (∃ n, e = 2 * n + 1) ∨ ∃ n, e = 2 * n + 4 := by
  by_cases h0 : e = 0
  · exact Or.inl h0
  by_cases h2 : e = 2
  · exact Or.inr (Or.inl h2)
  by_cases ho : e % 2 = 1
  · exact Or.inr (Or.inr (Or.inl ⟨e / 2, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨(e - 4) / 2, by omega⟩))

private theorem initial_row_ne_empty (k : ℕ) : Set.Iic k ≠ (∅ : Set ℕ) := by
  intro h
  have hk : k ∈ Set.Iic k := Set.mem_Iic.mpr le_rfl
  simp only [h, Set.mem_empty_iff_false] at hk

private theorem initial_row_ne_univ (k : ℕ) : Set.Iic k ≠ (Set.univ : Set ℕ) := by
  intro h
  have hk : k + 1 ∈ Set.Iic k := h.symm ▸ Set.mem_univ _
  exact Nat.not_succ_le_self k hk

private theorem preliminary_ne_omitted (x n : ℕ) :
    preliminaryRow x ≠ Set.Iic (omittedEndpoint n) := by
  intro h
  rcases (preliminary_range (preliminaryRow x)).mp ⟨x, rfl⟩ with ⟨_, hi⟩ | ⟨k, hk, he⟩
  · exact hi (h.symm ▸ isLowerSet_Iic _)
  · have heq : k = omittedEndpoint n := Set.Iic_inj.mp (he.symm.trans h)
    have hn : omittedEndpoint n ∈ retirementEndpointsᶜ := by
      rw [← omitted_endpoint_enumerates.2]
      exact ⟨n, rfl⟩
    exact hn (heq ▸ hk)

theorem completed_injective : Function.Injective completedRow := by
  intro e f he
  rcases row_index_cases e with rfl | rfl | ⟨n, rfl⟩ | ⟨n, rfl⟩ <;>
    rcases row_index_cases f with rfl | rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩ <;>
    simp only [completed_rows_equations.1, completed_rows_equations.2.1,
      completed_rows_equations.2.2.1, completed_rows_equations.2.2.2] at he
  · rfl
  · exact False.elim (Set.univ_nonempty.ne_empty he)
  · exact False.elim ((preliminary_nonempty_proper m).2 he.symm)
  · exact False.elim (initial_row_ne_univ _ he.symm)
  · exact False.elim (Set.univ_nonempty.ne_empty he.symm)
  · rfl
  · exact False.elim ((preliminary_nonempty_proper m).1 he.symm)
  · exact False.elim (initial_row_ne_empty _ he.symm)
  · exact False.elim ((preliminary_nonempty_proper n).2 he)
  · exact False.elim ((preliminary_nonempty_proper n).1 he)
  · have h := preliminary_injective he; omega
  · exact False.elim (preliminary_ne_omitted n m he)
  · exact False.elim (initial_row_ne_univ _ he)
  · exact False.elim (initial_row_ne_empty _ he)
  · exact False.elim (preliminary_ne_omitted m n he.symm)
  · have h := omitted_endpoint_enumerates.1.injective (Set.Iic_inj.mp he); omega

theorem completed_surjective (e : ℕ) : ∃ n, completedRow n = indexSet e := by
  classical
  by_cases hi : IsLowerSet (indexSet e)
  · rcases (initial_segment_classification (indexSet e)).mp hi with h | h | ⟨k, h⟩
    · exact ⟨2, completed_rows_equations.2.1.trans h.symm⟩
    · exact ⟨0, completed_rows_equations.1.trans h.symm⟩
    · by_cases hk : k ∈ retirementEndpoints
      · obtain ⟨x, hx⟩ := (preliminary_range (Set.Iic k)).mpr (Or.inr ⟨k, hk, rfl⟩)
        exact ⟨2 * x + 1, (completed_rows_equations.2.2.1 x).trans (hx.trans h.symm)⟩
      · have hm : k ∈ Set.range omittedEndpoint := by
          rw [omitted_endpoint_enumerates.2]
          exact hk
        obtain ⟨n, hn⟩ := hm
        refine ⟨2 * n + 4, ?_⟩
        rw [completed_rows_equations.2.2.2, hn, h]
  · have hr : REPred (indexSet e) := (enumerable_iff_index _).mpr ⟨e, fun _ => Iff.rfl⟩
    obtain ⟨x, hx⟩ := (preliminary_range (indexSet e)).mpr (Or.inl ⟨hr, hi⟩)
    exact ⟨2 * x + 1, (completed_rows_equations.2.2.1 x).trans hx⟩

theorem completed_friedberg : FriedbergNumbering completedRow := by
  exact ⟨completed_uniform, completed_injective, completed_surjective⟩

end
end Lemmatheca.ComputabilityTheory.FriedbergNumberings
