import Lemmatheca.IntuitionisticPropositionalTerminatingProofSearch.Goals

namespace Lemmatheca.ProofTheory.Intuitionistic.G4ip.Search
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
universe u
variable {α : Type u} [DecidableEq α]

/-- A specified primitive nonleaf rule choice, with its real list-membership conditions. -/
inductive Move (H : List (PropFormula α)) : PropFormula α → Type u
  | conjRight (A B) : Move H (conj A B)
  | disjRightLeft (A B) : Move H (disj A B)
  | disjRightRight (A B) : Move H (disj A B)
  | implRight (A B) : Move H (impl A B)
  | conjLeft (A B E) (h : conj A B ∈ H) : Move H E
  | disjLeft (A B E) (h : disj A B ∈ H) : Move H E
  | atomImplLeft (a : α) (B E) (h : impl (atom a) B ∈ H) (ha : atom a ∈ H) : Move H E
  | botImplLeft (B E) (h : impl falsum B ∈ H) : Move H E
  | conjImplLeft (A B C E) (h : impl (conj A B) C ∈ H) : Move H E
  | disjImplLeft (A B C E) (h : impl (disj A B) C ∈ H) : Move H E
  | implImplLeft (A B C E) (h : impl (impl A B) C ∈ H) : Move H E

def Move.premises {H : List (PropFormula α)} {E : PropFormula α} :
    Move H E → List (PresentedGoal α)
  | .conjRight A B => [(H, A), (H, B)]
  | .disjRightLeft A _ => [(H, A)]
  | .disjRightRight _ B => [(H, B)]
  | .implRight A B => [(A :: H, B)]
  | .conjLeft A B E _ => [(A :: B :: removePrincipal (conj A B) H, E)]
  | .disjLeft A B E _ => [(A :: removePrincipal (disj A B) H, E),
      (B :: removePrincipal (disj A B) H, E)]
  | .atomImplLeft a B E _ _ => [(B :: removePrincipal (impl (atom a) B) H, E)]
  | .botImplLeft B E _ => [(removePrincipal (impl falsum B) H, E)]
  | .conjImplLeft A B C E _ =>
      [(impl A (impl B C) :: removePrincipal (impl (conj A B) C) H, E)]
  | .disjImplLeft A B C E _ =>
      [(impl A C :: impl B C :: removePrincipal (impl (disj A B) C) H, E)]
  | .implImplLeft A B C E _ =>
      [(impl B C :: removePrincipal (impl (impl A B) C) H, impl A B),
        (C :: removePrincipal (impl (impl A B) C) H, E)]

/-- Reconstruction is the actual recorded G4ip constructor, with only context casts. -/
def Move.rebuild {H : List (PropFormula α)} {E : PropFormula α} (m : Move H E)
    (ps : Certificates m.premises) : Certificate (H, E) := by
  cases m with
  | conjRight A B => exact .conjRight ps.1 ps.2.1
  | disjRightLeft A B => exact .disjRightLeft ps.1
  | disjRightRight A B => exact .disjRightRight ps.1
  | implRight A B =>
      exact .implRight (by simpa only [Certificate, List.toFinset_cons] using ps.1)
  | conjLeft A B E h =>
      exact .conjLeft (List.mem_toFinset.mpr h)
        (by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using ps.1)
  | disjLeft A B E h =>
      exact .disjLeft (List.mem_toFinset.mpr h)
        (by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using ps.1)
        (by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using ps.2.1)
  | atomImplLeft a B E h ha =>
      exact .atomImplLeft (List.mem_toFinset.mpr h) (List.mem_toFinset.mpr ha)
        (by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using ps.1)
  | botImplLeft B E h =>
      exact .botImplLeft (List.mem_toFinset.mpr h)
        (by simpa only [Certificate, removePrincipal_toFinset] using ps.1)
  | conjImplLeft A B C E h =>
      exact .conjImplLeft (List.mem_toFinset.mpr h)
        (by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using ps.1)
  | disjImplLeft A B C E h =>
      exact .disjImplLeft (List.mem_toFinset.mpr h)
        (by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using ps.1)
  | implImplLeft A B C E h =>
      exact .implImplLeft (List.mem_toFinset.mpr h)
        (by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using ps.1)
        (by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using ps.2.1)

def rightMoves (H : List (PropFormula α)) : (E : PropFormula α) → List (Move H E)
  | .conj A B => [.conjRight A B]
  | .disj A B => [.disjRightLeft A B, .disjRightRight A B]
  | .impl A B => [.implRight A B]
  | _ => []

def leftMoves (H : List (PropFormula α)) (E : PropFormula α)
    (F : PropFormula α) (h : F ∈ H) : List (Move H E) :=
  match F, h with
  | .conj A B, h => [.conjLeft A B E h]
  | .disj A B, h => [.disjLeft A B E h]
  | .impl (.atom a) B, h =>
      if ha : atom a ∈ H then [.atomImplLeft a B E h ha] else []
  | .impl .falsum B, h => [.botImplLeft B E h]
  | .impl (.conj A B) C, h => [.conjImplLeft A B C E h]
  | .impl (.disj A B) C, h => [.disjImplLeft A B C E h]
  | .impl (.impl A B) C, h => [.implImplLeft A B C E h]
  | _, _ => []

/-- Right choices first, then one left choice per eligible presented assumption. -/
def moves (H : List (PropFormula α)) (E : PropFormula α) : List (Move H E) :=
  rightMoves H E ++ H.attach.flatMap (fun F => leftMoves H E F.1 F.2)

theorem Move.mem_moves {H : List (PropFormula α)} {E : PropFormula α} (m : Move H E) :
    m ∈ moves H E := by
  cases m with
  | conjRight A B => exact List.mem_append_left _ (by simp [rightMoves])
  | disjRightLeft A B => exact List.mem_append_left _ (by simp [rightMoves])
  | disjRightRight A B => exact List.mem_append_left _ (by simp [rightMoves])
  | implRight A B => exact List.mem_append_left _ (by simp [rightMoves])
  | conjLeft A B E h =>
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨_, h⟩, by simp, by simp [leftMoves]⟩)
  | disjLeft A B E h =>
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨_, h⟩, by simp, by simp [leftMoves]⟩)
  | atomImplLeft a B E h ha =>
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨_, h⟩, by simp, by simp [leftMoves, ha]⟩)
  | botImplLeft B E h =>
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨_, h⟩, by simp, by simp [leftMoves]⟩)
  | conjImplLeft A B C E h =>
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨_, h⟩, by simp, by simp [leftMoves]⟩)
  | disjImplLeft A B C E h =>
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨_, h⟩, by simp, by simp [leftMoves]⟩)
  | implImplLeft A B C E h =>
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨_, h⟩, by simp, by simp [leftMoves]⟩)

theorem moves_length_le (H : List (PropFormula α)) (E : PropFormula α) :
    (moves H E).length ≤ H.length + 2 := by
  have rightBound : (rightMoves H E).length ≤ 2 := by cases E <;> simp [rightMoves]
  have leftBound (F : PropFormula α) (h : F ∈ H) : (leftMoves H E F h).length ≤ 1 := by
    cases F with
    | atom _ | falsum | neg _ | conj _ _ | disj _ _ => simp [leftMoves]
    | impl A B => cases A <;> simp [leftMoves]; split <;> simp_all
  have listBound (xs : List {F // F ∈ H}) :
      (xs.flatMap (fun F => leftMoves H E F.1 F.2)).length ≤ xs.length := by
    induction xs with
    | nil => simp
    | cons F fs ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have hF := leftBound F.1 F.2
        omega
  have h := listBound H.attach
  simp only [List.length_attach] at h
  simp only [moves, List.length_append]
  omega

theorem Move.premises_length_le_two {H : List (PropFormula α)} {E : PropFormula α}
    (m : Move H E) : m.premises.length ≤ 2 := by
  cases m <;> simp [premises]

theorem Move.premise_backward {H : List (PropFormula α)} {E : PropFormula α}
    (m : Move H E) {g : PresentedGoal α} (hg : g ∈ m.premises) :
    G4ip.Backward (underlying g) (H.toFinset, E) := by
  cases m with
  | conjRight A B =>
      simp only [premises, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact .conjRightLeft H.toFinset A B
      · exact .conjRightRight H.toFinset A B
  | disjRightLeft A B =>
      simp only [premises, List.mem_singleton] at hg
      subst g
      exact .disjRightLeft H.toFinset A B
  | disjRightRight A B =>
      simp only [premises, List.mem_singleton] at hg
      subst g
      exact .disjRightRight H.toFinset A B
  | implRight A B =>
      simp only [premises, List.mem_singleton] at hg
      subst g
      simpa only [underlying, List.toFinset_cons] using G4ip.Backward.implRight H.toFinset A B
  | conjLeft A B E h =>
      simp only [premises, List.mem_singleton] at hg
      subst g
      simpa only [underlying, List.toFinset_cons, removePrincipal_toFinset] using
        G4ip.Backward.conjLeft (E := E) (List.mem_toFinset.mpr h)
  | disjLeft A B E h =>
      simp only [premises, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · simpa only [underlying, List.toFinset_cons, removePrincipal_toFinset] using
          G4ip.Backward.disjLeftLeft (E := E) (List.mem_toFinset.mpr h)
      · simpa only [underlying, List.toFinset_cons, removePrincipal_toFinset] using
          G4ip.Backward.disjLeftRight (E := E) (List.mem_toFinset.mpr h)
  | atomImplLeft a B E h ha =>
      simp only [premises, List.mem_singleton] at hg
      subst g
      simpa only [underlying, List.toFinset_cons, removePrincipal_toFinset] using
        G4ip.Backward.atomImplLeft (E := E) (List.mem_toFinset.mpr h) (List.mem_toFinset.mpr ha)
  | botImplLeft B E h =>
      simp only [premises, List.mem_singleton] at hg
      subst g
      simpa only [underlying, removePrincipal_toFinset] using
        G4ip.Backward.botImplLeft (E := E) (List.mem_toFinset.mpr h)
  | conjImplLeft A B C E h =>
      simp only [premises, List.mem_singleton] at hg
      subst g
      simpa only [underlying, List.toFinset_cons, removePrincipal_toFinset] using
        G4ip.Backward.conjImplLeft (E := E) (List.mem_toFinset.mpr h)
  | disjImplLeft A B C E h =>
      simp only [premises, List.mem_singleton] at hg
      subst g
      simpa only [underlying, List.toFinset_cons, removePrincipal_toFinset] using
        G4ip.Backward.disjImplLeft (E := E) (List.mem_toFinset.mpr h)
  | implImplLeft A B C E h =>
      simp only [premises, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · simpa only [underlying, List.toFinset_cons, removePrincipal_toFinset] using
          G4ip.Backward.implImplLeftFirst (E := E) (List.mem_toFinset.mpr h)
      · simpa only [underlying, List.toFinset_cons, removePrincipal_toFinset] using
          G4ip.Backward.implImplLeftSecond (E := E) (List.mem_toFinset.mpr h)

theorem Move.premise_weight_lt {H : List (PropFormula α)} {E : PropFormula α}
    (m : Move H E) {g : PresentedGoal α} (hg : g ∈ m.premises) :
    problemWeight g < problemWeight (H, E) :=
  rule_decrease (m.premise_backward hg)

private theorem reducedInsert {Γ : Context α} {A : PropFormula α}
    (hA : NegationFree A) (hΓ : ReducedContext Γ) : ReducedContext (insert A Γ) := by
  intro X hX
  rcases Finset.mem_insert.mp hX with rfl | hX
  · exact hA
  · exact hΓ X hX

private theorem reducedErase {Γ : Context α} (hΓ : ReducedContext Γ) (F : PropFormula α) :
    ReducedContext (remainder Γ F) := by
  intro X hX
  exact hΓ X (Finset.mem_of_mem_erase hX)

private theorem backwardReduced {child parent : G4ip.Goal α}
    (h : G4ip.Backward child parent) (hΓ : ReducedContext parent.1) (hE : NegationFree parent.2) :
    ReducedContext child.1 ∧ NegationFree child.2 := by
  cases h with
  | conjRightLeft Γ A B => exact ⟨hΓ, hE.1⟩
  | conjRightRight Γ A B => exact ⟨hΓ, hE.2⟩
  | disjRightLeft Γ A B => exact ⟨hΓ, hE.1⟩
  | disjRightRight Γ A B => exact ⟨hΓ, hE.2⟩
  | implRight Γ A B => exact ⟨reducedInsert hE.1 hΓ, hE.2⟩
  | @conjLeft Γ A B E hf =>
      have hr := hΓ _ hf
      exact ⟨reducedInsert hr.1 (reducedInsert hr.2 (reducedErase hΓ _)), hE⟩
  | @disjLeftLeft Γ A B E hf =>
      exact ⟨reducedInsert (hΓ _ hf).1 (reducedErase hΓ _), hE⟩
  | @disjLeftRight Γ A B E hf =>
      exact ⟨reducedInsert (hΓ _ hf).2 (reducedErase hΓ _), hE⟩
  | @atomImplLeft Γ a B E hf _ =>
      exact ⟨reducedInsert (hΓ _ hf).2 (reducedErase hΓ _), hE⟩
  | @botImplLeft Γ B E hf => exact ⟨reducedErase hΓ _, hE⟩
  | @conjImplLeft Γ A B C E hf =>
      have hr := hΓ _ hf
      exact ⟨reducedInsert ⟨hr.1.1, hr.1.2, hr.2⟩ (reducedErase hΓ _), hE⟩
  | @disjImplLeft Γ A B C E hf =>
      have hr := hΓ _ hf
      exact ⟨reducedInsert ⟨hr.1.1, hr.2⟩
        (reducedInsert ⟨hr.1.2, hr.2⟩ (reducedErase hΓ _)), hE⟩
  | @implImplLeftFirst Γ A B C E hf =>
      have hr := hΓ _ hf
      exact ⟨reducedInsert ⟨hr.1.2, hr.2⟩ (reducedErase hΓ _), hr.1⟩
  | @implImplLeftSecond Γ A B C E hf =>
      exact ⟨reducedInsert (hΓ _ hf).2 (reducedErase hΓ _), hE⟩

theorem Move.premise_reduced {H : List (PropFormula α)} {E : PropFormula α}
    (m : Move H E) (hred : ReducedGoal (H, E)) {g : PresentedGoal α}
    (hg : g ∈ m.premises) : ReducedGoal g := by
  have hp := (reducedGoal_iff (H, E)).mp hred
  exact (reducedGoal_iff g).mpr (backwardReduced (m.premise_backward hg) hp.1 hp.2)

end Lemmatheca.ProofTheory.Intuitionistic.G4ip.Search
