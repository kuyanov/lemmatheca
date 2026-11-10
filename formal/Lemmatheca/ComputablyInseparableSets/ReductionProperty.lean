import Lemmatheca.ComputablyInseparableSets.NegativeSearch
import Lemmatheca.EffectiveEnumerations.Stages

namespace Lemmatheca.ComputabilityTheory.ComputableSeparation
open UniversalComputation EffectiveEnumerations

/-- A disjoint pair of positive refinements retaining the original union. -/
def DisjointRefinement (A B A₀ B₀ : Set ℕ) : Prop :=
  REPred A₀ ∧ REPred B₀ ∧ A₀ ⊆ A ∧ B₀ ⊆ B ∧
    Disjoint A₀ B₀ ∧ A₀ ∪ B₀ = A ∪ B

def leftRefinement (e d : ℕ) : Set ℕ :=
  {x | ∃ s, x ∈ stage e s ∧ ∀ t < s, x ∉ stage d t}

def rightRefinement (e d : ℕ) : Set ℕ :=
  {x | ∃ s, x ∈ stage d s ∧ ∀ t ≤ s, x ∉ stage e t}

/-- The common first-arrival race returns zero on the left, including ties. -/
noncomputable def positiveRace (e d x : ℕ) : Part ℕ :=
  negativeRace (fun x s => x ∈ stage e s) (fun x s => x ∈ stage d s) x

/-- Each recognizer runs the same race, then diverges on the other side. -/
noncomputable def refinementRecognizer (side e d x : ℕ) : Part ℕ := by
  classical
  exact (positiveRace e d x).bind fun b => if b = side then Part.some 0 else Part.none

private theorem positive_race_mem (e d x side : ℕ) :
    side ∈ positiveRace e d x ↔ ∃ s,
      (x ∈ stage e s ∨ x ∈ stage d s) ∧
      (∀ t < s, x ∉ stage e t ∧ x ∉ stage d t) ∧
      (@ite ℕ (x ∈ stage e s) (Classical.propDecidable _) 0 1) = side := by
  classical
  simp only [positiveRace, negativeRace, Part.mem_map_iff]
  constructor
  · rintro ⟨s, hs, hv⟩
    have h := (raceStage_spec (fun x s => x ∈ stage e s)
      (fun x s => x ∈ stage d s) x s).mp hs
    exact ⟨s, h.1, h.2, hv⟩
  · rintro ⟨s, h, hp, hv⟩
    exact ⟨s, (raceStage_spec _ _ x s).mpr ⟨h, hp⟩, hv⟩

private theorem first_arrival_exists (e d x : ℕ)
    (h : ∃ s, x ∈ stage e s ∨ x ∈ stage d s) :
    ∃ s, (x ∈ stage e s ∨ x ∈ stage d s) ∧
      ∀ t < s, x ∉ stage e t ∧ x ∉ stage d t := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun t ht => not_or.mp (Nat.find_min h ht)⟩

private theorem positive_left (e d x : ℕ) :
    0 ∈ positiveRace e d x ↔ x ∈ leftRefinement e d := by
  classical
  constructor
  · intro h
    obtain ⟨s, _, hp, hv⟩ := (positive_race_mem e d x 0).mp h
    have ha : x ∈ stage e s := by by_contra hn; simp [hn] at hv
    exact ⟨s, ha, fun t ht => (hp t ht).2⟩
  · rintro ⟨s, ha, hb⟩
    obtain ⟨t, ht, hp⟩ := first_arrival_exists e d x ⟨s, Or.inl ha⟩
    have hts : t ≤ s := by
      by_contra hn
      exact (hp s (by omega)).1 ha
    have hat : x ∈ stage e t := by
      rcases ht with ht | ht
      · exact ht
      · by_contra hn
        have hlt : t < s := by
          by_contra hnlt
          have he : t = s := by omega
          exact hn (he ▸ ha)
        exact hb t hlt ht
    exact (positive_race_mem e d x 0).mpr ⟨t, ht, hp, by simp [hat]⟩

private theorem positive_right (e d x : ℕ) :
    1 ∈ positiveRace e d x ↔ x ∈ rightRefinement e d := by
  classical
  constructor
  · intro h
    obtain ⟨s, ht, hp, hv⟩ := (positive_race_mem e d x 1).mp h
    have ha : x ∉ stage e s := by intro ha; simp [ha] at hv
    refine ⟨s, ht.resolve_left ha, ?_⟩
    intro t hts
    rcases lt_or_eq_of_le hts with hlt | rfl
    · exact (hp t hlt).1
    · exact ha
  · rintro ⟨s, hb, ha⟩
    obtain ⟨t, ht, hp⟩ := first_arrival_exists e d x ⟨s, Or.inr hb⟩
    have hts : t ≤ s := by
      by_contra hn
      exact (hp s (by omega)).2 hb
    have hna := ha t hts
    exact (positive_race_mem e d x 1).mpr ⟨t, ht, hp, by simp [hna]⟩

set_option maxHeartbeats 800000 in
theorem refinement_recognizer_joint_partial :
    Nat.Partrec (fun n => refinementRecognizer n.unpair.1 n.unpair.2.unpair.1
      n.unpair.2.unpair.2.unpair.1 n.unpair.2.unpair.2.unpair.2) := by
  classical
  let E (n : ℕ) := n.unpair.2.unpair.1
  let D (n : ℕ) := n.unpair.2.unpair.2.unpair.1
  let X (n : ℕ) := n.unpair.2.unpair.2.unpair.2
  have hE : Primrec E := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hD : Primrec D := Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hX : Primrec X := Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hL : PrimrecPred (fun p : ℕ × ℕ => X p.1 ∈ stage (E p.1) p.2) :=
    stage_predicate_primitive.comp (((hE.comp Primrec.fst).pair Primrec.snd).pair
      (hX.comp Primrec.fst))
  have hR : PrimrecPred (fun p : ℕ × ℕ => X p.1 ∈ stage (D p.1) p.2) :=
    stage_predicate_primitive.comp (((hD.comp Primrec.fst).pair Primrec.snd).pair
      (hX.comp Primrec.fst))
  have hc : Computable₂ (fun (n s : ℕ) => decide
      (X n ∈ stage (E n) s ∨ X n ∈ stage (D n) s)) := (hL.or hR).decide.to_comp
  have hs := Partrec.rfind hc.partrec₂
  have hv : Computable₂ (fun (n s : ℕ) => if X n ∈ stage (E n) s then 0 else 1) :=
    (Primrec.ite hL (Primrec.const 0) (Primrec.const 1)).to_comp.to₂
  have hr := hs.map hv
  have ht : ComputablePred (fun p : ℕ × ℕ => p.2 = p.1.unpair.1) :=
    (Primrec.eq.comp Primrec.snd (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))).computablePred
  have hb : Partrec₂ (fun n b : ℕ => if b = n.unpair.1 then Part.some 0 else Part.none) :=
    (Partrec.cond ht.decide (Partrec.const' (Part.some 0)) Partrec.none).of_eq
      (fun _ => by simp only [Bool.cond_decide])
  exact Partrec.nat_iff.mp (hr.bind hb)

noncomputable def refinementMaster : ℕ :=
  (phi_complete refinement_recognizer_joint_partial).choose

noncomputable def refinementIndex (side e d : ℕ) : ℕ :=
  specialize (specialize (specialize refinementMaster side) e) d

theorem refinement_index_primitive (side : ℕ) : Primrec₂ (refinementIndex side) := by
  exact specialize_primitive.comp₂
    (specialize_primitive.comp₂ (Primrec₂.const (specialize refinementMaster side)) Primrec₂.left)
    Primrec₂.right

theorem refinement_index_eval (side e d x : ℕ) :
    phi (refinementIndex side e d) x = refinementRecognizer side e d x := by
  simp only [refinementIndex, specialize_eval]
  have h := congrFun (Exists.choose_spec (phi_complete refinement_recognizer_joint_partial))
    (Nat.pair side (Nat.pair e (Nat.pair d x)))
  simpa [refinementMaster] using h

theorem refinement_index_domains (e d : ℕ) :
    indexSet (refinementIndex 0 e d) = leftRefinement e d ∧
      indexSet (refinementIndex 1 e d) = rightRefinement e d := by
  classical
  have hd (side x : ℕ) : (refinementRecognizer side e d x).Dom ↔ side ∈ positiveRace e d x := by
    simp only [refinementRecognizer, Part.bind_dom]
    constructor
    · rintro ⟨h, ht⟩
      split_ifs at ht with hv
      · exact hv ▸ Part.get_mem h
      · exact False.elim ht
    · intro h
      refine ⟨h.1, ?_⟩
      simp [h.2]
  constructor
  · ext x
    change (phi (refinementIndex 0 e d) x).Dom ↔ _
    rw [refinement_index_eval, hd, positive_left]
  · ext x
    change (phi (refinementIndex 1 e d) x).Dom ↔ _
    rw [refinement_index_eval, hd, positive_right]

theorem specified_disjoint_refinement (e d : ℕ) :
    DisjointRefinement (indexSet e) (indexSet d) (leftRefinement e d) (rightRefinement e d) := by
  have hce (i : ℕ) : REPred (indexSet (refinementIndex i e d)) :=
    (Partrec.nat_iff.mpr (Partrec.nat_iff.mp
      (phi_recursive.comp (Computable.const (refinementIndex i e d)) Computable.id))).dom_re
  have hleft : REPred (leftRefinement e d) := (refinement_index_domains e d).1 ▸ hce 0
  have hright : REPred (rightRefinement e d) := (refinement_index_domains e d).2 ▸ hce 1
  have hsubL : leftRefinement e d ⊆ indexSet e := fun x ⟨s, hs, _⟩ =>
    (stage_union e x).mpr ⟨s, hs⟩
  have hsubR : rightRefinement e d ⊆ indexSet d := fun x ⟨s, hs, _⟩ =>
    (stage_union d x).mpr ⟨s, hs⟩
  refine ⟨hleft, hright, hsubL, hsubR, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    rintro x ⟨s, hs, hprevB⟩ ⟨t, ht, hprevA⟩
    by_cases hst : s ≤ t
    · exact hprevA s hst hs
    · exact hprevB t (by omega) ht
  · apply Set.Subset.antisymm
    · exact Set.union_subset_union hsubL hsubR
    · intro x hx
      have hex : ∃ s, x ∈ stage e s ∨ x ∈ stage d s := by
        rcases hx with hx | hx
        · obtain ⟨s, hs⟩ := (stage_union e x).mp hx
          exact ⟨s, Or.inl hs⟩
        · obtain ⟨s, hs⟩ := (stage_union d x).mp hx
          exact ⟨s, Or.inr hs⟩
      obtain ⟨s, hs, hp⟩ := first_arrival_exists e d x hex
      by_cases ha : x ∈ stage e s
      · exact Or.inl ⟨s, ha, fun t ht => (hp t ht).2⟩
      · refine Or.inr ⟨s, hs.resolve_left ha, ?_⟩
        intro t ht
        rcases lt_or_eq_of_le ht with hlt | rfl
        · exact (hp t hlt).1
        · exact ha

theorem ce_reduction_property (A B : Set ℕ) (hA : REPred A) (hB : REPred B) :
    ∃ A₀ B₀, DisjointRefinement A B A₀ B₀ := by
  obtain ⟨e, he⟩ := (enumerable_iff_index A).mp hA
  obtain ⟨d, hd⟩ := (enumerable_iff_index B).mp hB
  have hAe : A = indexSet e := Set.ext he
  have hBd : B = indexSet d := Set.ext hd
  exact ⟨leftRefinement e d, rightRefinement e d, hAe ▸ hBd ▸ specified_disjoint_refinement e d⟩

theorem refinement_disjoint_inputs (A B A₀ B₀ : Set ℕ)
    (hr : DisjointRefinement A B A₀ B₀) (hd : Disjoint A B) :
    A₀ = A ∧ B₀ = B := by
  have hA := hr.2.2.1
  have hB := hr.2.2.2.1
  have hu := hr.2.2.2.2.2
  constructor
  · apply Set.Subset.antisymm hA
    intro x hx
    have hxu : x ∈ A₀ ∪ B₀ := hu ▸ Or.inl hx
    exact hxu.resolve_right (fun hb => Set.disjoint_left.mp hd hx (hB hb))
  · apply Set.Subset.antisymm hB
    intro x hx
    have hxu : x ∈ A₀ ∪ B₀ := hu ▸ Or.inr hx
    exact hxu.resolve_left (fun ha => Set.disjoint_left.mp hd (hA ha) hx)

theorem refinement_full_union (A B A₀ B₀ : Set ℕ)
    (hr : DisjointRefinement A B A₀ B₀) (hu : A ∪ B = Set.univ) :
    ComputablePred A₀ ∧ ComputablePred B₀ := by
  have hdis := hr.2.2.2.2.1
  have hcover : A₀ ∪ B₀ = Set.univ := hr.2.2.2.2.2.trans hu
  have hc : B₀ = A₀ᶜ := by
    ext x
    constructor
    · intro hb ha
      exact Set.disjoint_left.mp hdis ha hb
    · intro ha
      have hx : x ∈ A₀ ∪ B₀ := hcover ▸ Set.mem_univ x
      exact hx.resolve_left ha
  have hdec : ComputablePred A₀ := ComputablePred.computable_iff_re_compl_re'.mpr
    ⟨hr.1, hr.2.1.of_eq (fun x => by change x ∈ B₀ ↔ x ∉ A₀; rw [hc]; rfl)⟩
  exact ⟨hdec, hc.symm ▸ hdec.not⟩

theorem refinement_empty_inputs (A₀ B₀ : Set ℕ)
    (hr : DisjointRefinement ∅ ∅ A₀ B₀) : A₀ = ∅ ∧ B₀ = ∅ := by
  exact ⟨Set.eq_empty_iff_forall_notMem.mpr (fun _ hx => hr.2.2.1 hx),
    Set.eq_empty_iff_forall_notMem.mpr (fun _ hx => hr.2.2.2.1 hx)⟩

end Lemmatheca.ComputabilityTheory.ComputableSeparation
