import Lemmatheca.ForcingAndGenericFilters.Orders

/-! Rasiowa–Sikorski on arbitrary forcing orders, with the refinement selector
fixed before the descending recursion. No countability of the order is used. -/
namespace Lemmatheca.SetTheory.ForcingAndGenericFilters
open Set Order
universe u
variable {P : Type u} [PartialOrder P]
noncomputable section

/-- A selector chooses a member of each dense requirement below any condition. -/
def RefinementSelector (D : ℕ → Set P) (s : ℕ → P → P) : Prop :=
  ∀ n q, s n q ∈ D n ∧ s n q ≤ q

theorem refinement_selector_exists (D : ℕ → Set P) (hD : ∀ n, Dense (D n)) :
    ∃ s : ℕ → P → P, RefinementSelector D s := by
  classical
  exact ⟨fun n q => Classical.choose (hD n q),
    fun n q => Classical.choose_spec (hD n q)⟩

/-- The specified sequence from a supplied selector and starting condition. -/
def selectedSequence (s : ℕ → P → P) (p : P) : ℕ → P
  | 0 => p
  | n + 1 => s n (selectedSequence s p n)

theorem selected_sequence_spec {D : ℕ → Set P} {s : ℕ → P → P}
    (hs : RefinementSelector D s) (p : P) :
    selectedSequence s p 0 = p ∧
      (∀ n, selectedSequence s p (n + 1) ∈ D n ∧
        selectedSequence s p (n + 1) ≤ selectedSequence s p n) ∧
      Antitone (selectedSequence s p) := by
  refine ⟨rfl, fun n => hs n _, ?_⟩
  exact antitone_nat_of_succ_le (fun n => (hs n _).2)

/-- The upward closure of this exact descending sequence. -/
def selectedClosure (s : ℕ → P → P) (p : P) : Set P :=
  {q | ∃ n, selectedSequence s p n ≤ q}

theorem selected_closure_isPFilter {D : ℕ → Set P} {s : ℕ → P → P}
    (hs : RefinementSelector D s) (p : P) : IsPFilter (selectedClosure s p) := by
  have hanti := (selected_sequence_spec hs p).2.2
  apply IsPFilter.of_def
  · exact ⟨p, 0, le_rfl⟩
  · rintro q ⟨i, hi⟩ r ⟨j, hj⟩
    exact ⟨selectedSequence s p (max i j), ⟨max i j, le_rfl⟩,
      (hanti (le_max_left i j)).trans hi, (hanti (le_max_right i j)).trans hj⟩
  · rintro q r hqr ⟨i, hi⟩
    exact ⟨i, hi.trans hqr⟩

/-- The filter supplied by the chosen refinement sequence. -/
def selectedFilter {D : ℕ → Set P} {s : ℕ → P → P}
    (hs : RefinementSelector D s) (p : P) : PFilter P :=
  (selected_closure_isPFilter hs p).toPFilter

theorem selected_filter_spec {D : ℕ → Set P} {s : ℕ → P → P}
    (hs : RefinementSelector D s) (p : P) :
    (∀ q, q ∈ selectedFilter hs p ↔ ∃ n, selectedSequence s p n ≤ q) ∧
      p ∈ selectedFilter hs p ∧
      ∀ n, selectedSequence s p (n + 1) ∈ selectedFilter hs p ∧
        selectedSequence s p (n + 1) ∈ D n := by
  refine ⟨fun _ => Iff.rfl, ⟨0, le_rfl⟩, ?_⟩
  intro n
  exact ⟨⟨n + 1, le_rfl⟩, (selected_sequence_spec hs p).2.1 n |>.1⟩

/-- The family may be empty, and the forcing order need not be countable. -/
theorem generic_through_arbitrary_countable_family (S : Set (Set P))
    (hS : S.Countable) (p : P) :
    ∃ G : PFilter P, p ∈ G ∧ GenericFor G S := by
  classical
  let T : Set (Set P) := {D | D ∈ insert Set.univ S ∧ Dense D}
  have hT : T.Countable := (hS.insert Set.univ).mono (fun _ h => h.1)
  have hTne : T.Nonempty :=
    ⟨Set.univ, Or.inl rfl, fun q => ⟨q, Set.mem_univ q, le_rfl⟩⟩
  obtain ⟨d, hd⟩ := hT.exists_surjective hTne
  let D : ℕ → Set P := fun n => (d n).val
  have hD : ∀ n, Dense (D n) := fun n => (d n).property.2
  obtain ⟨s, hs⟩ := refinement_selector_exists D hD
  refine ⟨selectedFilter hs p, (selected_filter_spec hs p).2.1, ?_⟩
  intro A hA hAd
  let a : T := ⟨A, Or.inr hA, hAd⟩
  obtain ⟨n, hn⟩ := hd a
  refine ⟨selectedSequence s p (n + 1),
    (selected_filter_spec hs p).2.2 n |>.1, ?_⟩
  have hnA : D n = A := congrArg Subtype.val hn
  exact hnA ▸ ((selected_sequence_spec hs p).2.1 n).1

end
end Lemmatheca.SetTheory.ForcingAndGenericFilters
