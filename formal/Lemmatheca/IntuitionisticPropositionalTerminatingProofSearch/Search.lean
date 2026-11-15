import Lemmatheca.IntuitionisticPropositionalTerminatingProofSearch.Moves

namespace Lemmatheca.ProofTheory.Intuitionistic.G4ip.Search
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
universe u
variable {α : Type u} [DecidableEq α]

/-- Literal primitive certificates at the two kinds of closing leaf. -/
def leaf (H : List (PropFormula α)) (E : PropFormula α) : Option (Certificate (H, E)) :=
  if hb : falsum ∈ H then some (.falsumLeft (List.mem_toFinset.mpr hb))
  else match E with
    | .atom a => if ha : atom a ∈ H then some (.atom (List.mem_toFinset.mpr ha)) else none
    | _ => none

def solveAll (solver : (g : PresentedGoal α) → Option (Certificate g)) :
    (gs : List (PresentedGoal α)) → Option (Certificates gs)
  | [] => some PUnit.unit
  | g :: gs => do
      let p ← solver g
      let ps ← solveAll solver gs
      pure (p, ps)

def tryMoves {H : List (PropFormula α)} {E : PropFormula α}
    (solver : (g : PresentedGoal α) → Option (Certificate g)) :
    List (Move H E) → Option (Certificate (H, E))
  | [] => none
  | m :: ms => match solveAll solver m.premises with
      | some ps => some (m.rebuild ps)
      | none => tryMoves solver ms

/-- Structural fuel recursion; success contains a reconstructed primitive tree. -/
def solveFuel : ℕ → (g : PresentedGoal α) → Option (Certificate g)
  | 0, _ => none
  | n + 1, (H, E) => match leaf H E with
      | some p => some p
      | none => tryMoves (solveFuel n) (moves H E)

def solve (g : PresentedGoal α) : Option (Certificate g) := solveFuel (problemWeight g) g

/-- A listed root inference with its actual child certificates. -/
structure RootMove (H : List (PropFormula α)) (E : PropFormula α) where
  move : Move H E
  listed : move ∈ moves H E
  children : Certificates move.premises

/-- Inspect the supplied primitive tree after the actual closing-leaf test has failed. -/
def rootMove {H : List (PropFormula α)} {E : PropFormula α}
    (p : Certificate (H, E)) (hleaf : leaf H E = none) : RootMove H E := by
  have hb : falsum ∉ H := by
    intro hb
    simp [leaf, hb] at hleaf
  cases p with
  | atom ha => simp [leaf, hb, List.mem_toFinset.mp ha] at hleaf
  | falsumLeft hf => exact (hb (List.mem_toFinset.mp hf)).elim
  | @conjRight Γ A B p q =>
      let m : Move H (conj A B) := .conjRight A B
      exact ⟨m, m.mem_moves, ⟨p, q, PUnit.unit⟩⟩
  | @disjRightLeft Γ A B p =>
      let m : Move H (disj A B) := .disjRightLeft A B
      exact ⟨m, m.mem_moves, ⟨p, PUnit.unit⟩⟩
  | @disjRightRight Γ A B p =>
      let m : Move H (disj A B) := .disjRightRight A B
      exact ⟨m, m.mem_moves, ⟨p, PUnit.unit⟩⟩
  | @implRight Γ A B p =>
      let m : Move H (impl A B) := .implRight A B
      exact ⟨m, m.mem_moves, ⟨by simpa only [Certificate, List.toFinset_cons] using p, PUnit.unit⟩⟩
  | @conjLeft Γ A B E hf p =>
      let m : Move H E := .conjLeft A B E (List.mem_toFinset.mp hf)
      refine ⟨m, m.mem_moves, ?_⟩
      exact ⟨by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using p,
        PUnit.unit⟩
  | @disjLeft Γ A B E hf p q =>
      let m : Move H E := .disjLeft A B E (List.mem_toFinset.mp hf)
      refine ⟨m, m.mem_moves, ?_⟩
      exact ⟨by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using p,
        by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using q,
        PUnit.unit⟩
  | @atomImplLeft Γ a B E hf ha p =>
      let m : Move H E := .atomImplLeft a B E (List.mem_toFinset.mp hf) (List.mem_toFinset.mp ha)
      refine ⟨m, m.mem_moves, ?_⟩
      exact ⟨by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using p,
        PUnit.unit⟩
  | @botImplLeft Γ B E hf p =>
      let m : Move H E := .botImplLeft B E (List.mem_toFinset.mp hf)
      refine ⟨m, m.mem_moves, ?_⟩
      exact ⟨by simpa only [Certificate, removePrincipal_toFinset] using p, PUnit.unit⟩
  | @conjImplLeft Γ A B C E hf p =>
      let m : Move H E := .conjImplLeft A B C E (List.mem_toFinset.mp hf)
      refine ⟨m, m.mem_moves, ?_⟩
      exact ⟨by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using p,
        PUnit.unit⟩
  | @disjImplLeft Γ A B C E hf p =>
      let m : Move H E := .disjImplLeft A B C E (List.mem_toFinset.mp hf)
      refine ⟨m, m.mem_moves, ?_⟩
      exact ⟨by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using p,
        PUnit.unit⟩
  | @implImplLeft Γ A B C E hf p q =>
      let m : Move H E := .implImplLeft A B C E (List.mem_toFinset.mp hf)
      refine ⟨m, m.mem_moves, ?_⟩
      exact ⟨by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using p,
        by simpa only [Certificate, removePrincipal_toFinset, List.toFinset_cons] using q,
        PUnit.unit⟩

/-- Root decomposition stores the supplied constructor and its actual children. -/
theorem rootMove_rebuild {H : List (PropFormula α)} {E : PropFormula α}
    (p : Certificate (H, E)) (hleaf : leaf H E = none) :
    (rootMove p hleaf).move.rebuild (rootMove p hleaf).children = p := by
  have hb : falsum ∉ H := by
    intro hb
    simp [leaf, hb] at hleaf
  cases p with
  | atom ha => simp [leaf, hb, List.mem_toFinset.mp ha] at hleaf
  | falsumLeft hf => exact (hb (List.mem_toFinset.mp hf)).elim
  | _ => simp_all [rootMove, Move.rebuild, Certificate, Move.premises, Certificates]

theorem solveAll_isSome (solver : (g : PresentedGoal α) → Option (Certificate g))
    (gs : List (PresentedGoal α)) :
    (solveAll solver gs).isSome = true ↔ ∀ g ∈ gs, (solver g).isSome = true := by
  induction gs with
  | nil => simp [solveAll, Option.isSome]
  | cons g gs ih =>
      cases hp : solver g with
      | none => simp [solveAll, hp]
      | some p =>
          cases hps : solveAll solver gs <;> simp_all [solveAll, Option.isSome]

theorem tryMoves_isSome {H : List (PropFormula α)} {E : PropFormula α}
    (solver : (g : PresentedGoal α) → Option (Certificate g)) (ms : List (Move H E)) :
    (tryMoves solver ms).isSome = true ↔
      ∃ m ∈ ms, ∀ g ∈ m.premises, (solver g).isSome = true := by
  induction ms with
  | nil => simp [tryMoves]
  | cons m ms ih =>
      cases hp : solveAll solver m.premises with
      | none =>
          have hn : ¬ ∀ g ∈ m.premises, (solver g).isSome = true := by
            rw [← solveAll_isSome, hp]
            simp
          simp only [tryMoves, hp]
          constructor
          · intro h
            obtain ⟨k, hk, hs⟩ := ih.mp h
            exact ⟨k, List.mem_cons_of_mem m hk, hs⟩
          · rintro ⟨k, hk, hs⟩
            rcases List.mem_cons.mp hk with he | he
            · subst k
              exact (hn hs).elim
            · exact ih.mpr ⟨k, he, hs⟩
      | some ps =>
          have hs : ∀ g ∈ m.premises, (solver g).isSome = true := by
            rw [← solveAll_isSome, hp]
            rfl
          simp only [tryMoves, hp, Option.isSome]
          exact iff_of_true True.intro ⟨m, List.mem_cons_self, hs⟩

theorem solveFuel_sound {n : ℕ} {g : PresentedGoal α}
    (h : (solveFuel n g).isSome = true) :
    Derives (g.1.toFinset : Set (PropFormula α)) g.2 := by
  cases hp : solveFuel n g with
  | none => simp [hp] at h
  | some p => exact p.toCutFree.to_natural

private def certificateAt {gs : List (PresentedGoal α)} (ps : Certificates gs)
    {g : PresentedGoal α} (hg : g ∈ gs) : Certificate g := by
  cases gs with
  | nil => simp at hg
  | cons k ks =>
      by_cases h : g = k
      · subst g
        exact ps.1
      · exact certificateAt ps.2 ((List.mem_cons.mp hg).resolve_left h)

theorem solveFuel_complete (n : ℕ) (g : PresentedGoal α) (p : Certificate g)
    (hw : problemWeight g ≤ n) : (solveFuel n g).isSome = true := by
  induction n generalizing g with
  | zero =>
      have he := weight_two_le g.2
      simp only [problemWeight, underlying, goalWeight] at hw
      omega
  | succ n ih =>
      rcases g with ⟨H, E⟩
      cases hl : leaf H E with
      | some q => simp [solveFuel, hl]
      | none =>
          let r := rootMove p hl
          simp only [solveFuel, hl]
          apply (tryMoves_isSome _ _).mpr
          refine ⟨r.move, r.listed, ?_⟩
          intro g hg
          apply ih g (certificateAt r.children hg)
          have hd := r.move.premise_weight_lt hg
          omega

theorem solve_iff_certificate (g : PresentedGoal α) :
    (solve g).isSome = true ↔ Nonempty (Certificate g) := by
  constructor
  · intro h
    cases hp : solve g with
    | none => simp [hp] at h
    | some p => exact ⟨p⟩
  · rintro ⟨p⟩
    exact solveFuel_complete (problemWeight g) g p (Nat.le_refl _)

theorem solve_none_iff (g : PresentedGoal α) :
    solve g = none ↔ ¬ Nonempty (Certificate g) := by
  rw [← solve_iff_certificate]
  cases solve g <;> simp

end Lemmatheca.ProofTheory.Intuitionistic.G4ip.Search
