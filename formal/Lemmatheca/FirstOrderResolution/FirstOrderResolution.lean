import Lemmatheca.TermUnification.TermUnification
import Lemmatheca.HerbrandModels.HerbrandModels

/-! Generalized first-order resolution on the shared actual relation clauses.
Each inference makes two disjoint variable copies and uses a most general
unifier of complete selected positive/negative families. -/
namespace Lemmatheca.MathematicalLogic.FirstOrderResolution

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.Propositional
open HerbrandModels


universe u v w w' z
variable {L : Language.{u, v}} {α : Type w} {β : Type w'}

noncomputable section

/-- The same clause substitution obeys simultaneous composition. -/
theorem clause_subst_subst (C : FOClause L α) (σ : α → L.Term β)
    {δ : Type*} (τ : β → L.Term δ) :
    clauseSubst τ (clauseSubst σ C) = clauseSubst (TermUnification.compose τ σ) C := by
  classical
  simp only [clauseSubst, Finset.image_image]
  apply Finset.image_congr
  intro l _
  exact congrArg (fun a : Atom L δ => (⟨a, l.positive⟩ : FOLiteral L δ))
    (Atom.subst_subst l.atom σ τ)

theorem clause_subst_id (C : FOClause L α) : clauseSubst Term.var C = C := by
  classical
  change C.image (literalSubst Term.var) = C
  calc
    C.image (literalSubst Term.var) = C.image id := by
      apply Finset.image_congr
      intro l _
      cases l
      simp [literalSubst, Atom.subst_var]
    _ = C := Finset.image_id

/-- Truth uses the same assignment to the actual resulting clause. -/
theorem clause_subst_realize {M : Type z} [L.Structure M]
    (C : FOClause L α) (σ : α → L.Term β) (v : β → M) :
    ClauseRealize (clauseSubst σ C) v ↔
      ClauseRealize C (fun x => (σ x).realize v) := by
  classical
  have hl (l : FOLiteral L α) :
      (if (literalSubst σ l).positive then (literalSubst σ l).atom.Realize v
        else ¬ (literalSubst σ l).atom.Realize v) ↔
      (if l.positive then l.atom.Realize (fun x => (σ x).realize v)
        else ¬ l.atom.Realize (fun x => (σ x).realize v)) := by
    cases h : l.positive <;> simp [literalSubst, h, Atom.subst_realize]
  simp only [ClauseRealize, clauseSubst, Finset.mem_image, exists_exists_and_eq_and, hl]

/-- Disjoint injections, applied anew at each inference. -/
def even (n : ℕ) : ℕ := 2 * n
def odd (n : ℕ) : ℕ := 2 * n + 1

def renameClause (r : ℕ → ℕ) (C : FOClause L ℕ) : FOClause L ℕ :=
  clauseSubst (fun x => Term.var (r x)) C

def leftCopy (C : FOClause L ℕ) : FOClause L ℕ := renameClause even C
def rightCopy (C : FOClause L ℕ) : FOClause L ℕ := renameClause odd C

/-- Merge independent substitutions, using parity to recover their source. -/
def combine (σ τ : ℕ → L.Term α) (n : ℕ) : L.Term α :=
  if n % 2 = 0 then σ (n / 2) else τ (n / 2)

theorem copies_disjoint : Function.Injective even ∧ Function.Injective odd ∧
    Disjoint (Set.range even) (Set.range odd) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b h
    dsimp [even] at h
    omega
  · intro a b h
    dsimp [odd] at h
    omega
  · apply Set.disjoint_left.mpr
    rintro n ⟨a, rfl⟩ ⟨b, h⟩
    dsimp [even, odd] at h
    omega

theorem combine_even_odd (σ τ : ℕ → L.Term α) (n : ℕ) :
    combine σ τ (even n) = σ n ∧ combine σ τ (odd n) = τ n := by
  constructor <;> simp [combine, even, odd, Nat.add_div]

theorem copies_substitute (C D : FOClause L ℕ) (σ τ : ℕ → L.Term α) :
    clauseSubst (combine σ τ) (leftCopy C) = clauseSubst σ C ∧
      clauseSubst (combine σ τ) (rightCopy D) = clauseSubst τ D := by
  constructor
  · change clauseSubst (combine σ τ) (clauseSubst (fun x => Term.var (even x)) C) = _
    rw [clause_subst_subst]
    congr 1
    funext n
    exact (combine_even_odd σ τ n).1
  · change clauseSubst (combine σ τ) (clauseSubst (fun x => Term.var (odd x)) D) = _
    rw [clause_subst_subst]
    congr 1
    funext n
    exact (combine_even_odd σ τ n).2

/-- All atoms in a finite family have one identical substitution image. -/
def AtomUnifies (σ : ℕ → L.Term α) (A : Finset (Atom L ℕ)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a.subst σ = b.subst σ

/-- All-variable factorization allows every residual alphabet in this universe. -/
def AtomMGU (A : Finset (Atom L ℕ)) (μ : ℕ → L.Term ℕ) : Prop :=
  AtomUnifies μ A ∧ ∀ (β : Type w) (σ : ℕ → L.Term β),
    AtomUnifies σ A → TermUnification.Factors σ μ

/-- Substitution cannot change the relation symbol or its arity. -/
def SameHead (a b : Atom L ℕ) : Prop :=
  ∃ h : a.arity = b.arity, a.relation = h ▸ b.relation

def HeadCompatible (A : Finset (Atom L ℕ)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, SameHead a b

/-- The exact shared term equations for a matching pair of relation heads.
Mismatched heads return no equations and are excluded by HeadCompatible. -/
def pairProblem (a b : Atom L ℕ) : TermUnification.Problem L := by
  classical
  exact if h : a.arity = b.arity then
    if a.relation = h ▸ b.relation then
      List.ofFn (fun i : Fin a.arity => (a.terms i, b.terms (Fin.cast h i)))
    else []
  else []

/-- A finite shared term problem comparing all pairs of family members. -/
def atomProblem (A : Finset (Atom L ℕ)) : TermUnification.Problem L :=
  A.toList.flatMap (fun a => A.toList.flatMap (pairProblem a))

private theorem pair_problem_unifies (a b : Atom L ℕ) (h : SameHead a b)
    (σ : ℕ → L.Term α) :
    TermUnification.Unifies σ (pairProblem a b) ↔ a.subst σ = b.subst σ := by
  classical
  rcases a with ⟨n, r, ts⟩
  rcases b with ⟨m, t, us⟩
  rcases h with ⟨hn, hr⟩
  dsimp at hn
  cases hn
  change r = t at hr
  cases hr
  simp [pairProblem, TermUnification.Unifies, List.mem_ofFn, Atom.subst,
    Atom.mk.injEq, funext_iff]

theorem atom_unifier_heads (A : Finset (Atom L ℕ)) (σ : ℕ → L.Term α)
    (h : AtomUnifies σ A) : HeadCompatible A := by
  intro a ha b hb
  have e := h a ha b hb
  rcases a with ⟨n, r, ts⟩
  rcases b with ⟨m, t, us⟩
  simp only [Atom.subst, Atom.mk.injEq] at e
  rcases e with ⟨hn, hr, _⟩
  cases hn
  have hr' : r = t := eq_of_heq hr
  cases hr'
  exact ⟨rfl, rfl⟩

theorem atom_problem_unifies (A : Finset (Atom L ℕ)) (h : HeadCompatible A)
    (σ : ℕ → L.Term α) :
    TermUnification.Unifies σ (atomProblem A) ↔ AtomUnifies σ A := by
  constructor
  · intro hP a ha b hb
    apply (pair_problem_unifies a b (h a ha b hb) σ).mp
    intro e he
    apply hP e
    exact List.mem_flatMap.mpr ⟨a, Finset.mem_toList.mpr ha,
      List.mem_flatMap.mpr ⟨b, Finset.mem_toList.mpr hb, he⟩⟩
  · intro hA e he
    obtain ⟨a, ha, he⟩ := List.mem_flatMap.mp he
    obtain ⟨b, hb, he⟩ := List.mem_flatMap.mp he
    have ha' := Finset.mem_toList.mp ha
    have hb' := Finset.mem_toList.mp hb
    exact (pair_problem_unifies a b (h a ha' b hb') σ).mpr (hA a ha' b hb') e he

/-- The actual solver returns the selected most general atom unifier. -/
theorem atom_unify_success (A : Finset (Atom L ℕ)) (σ : ℕ → L.Term α)
    (h : AtomUnifies σ A) :
    ∃ μ, @TermUnification.unify L (fun _ => Classical.decEq _) (atomProblem A) = some μ ∧
      AtomMGU.{u, v, w'} A μ := by
  classical
  let : ∀ n, DecidableEq (L.Functions n) := fun _ => Classical.decEq _
  have hA := atom_unifier_heads A σ h
  have hP := (atom_problem_unifies A hA σ).mpr h
  obtain ⟨μ, hμ⟩ := TermUnification.unify_complete (atomProblem A) σ hP
  refine ⟨μ, hμ, ?_, ?_⟩
  · exact (atom_problem_unifies A hA μ).mp (TermUnification.unify_sound _ μ hμ)
  · intro β τ hτ
    exact TermUnification.unify_factorization _ μ hμ τ
      ((atom_problem_unifies A hA τ).mpr hτ)

/-- Exact factorization for the same actual finite problem and solver answer. -/
theorem atom_unify_factorization (A : Finset (Atom L ℕ)) (hA : HeadCompatible A)
    (μ : ℕ → L.Term ℕ)
    (hμ : @TermUnification.unify L (fun _ => Classical.decEq _) (atomProblem A) = some μ)
    (σ : ℕ → L.Term α) (hσ : AtomUnifies σ A) :
    ∃ ρ : ℕ → L.Term α, ∀ x, (μ x).subst ρ = σ x := by
  classical
  let : ∀ n, DecidableEq (L.Functions n) := fun _ => Classical.decEq _
  exact TermUnification.unify_factorization _ μ hμ σ
    ((atom_problem_unifies A hA σ).mpr hσ)

/-- One inference's exact admissible selections, fresh copies, and chosen MGU. -/
structure InferenceData (C D : FOClause L ℕ) where
  positiveFamily : FOClause L ℕ
  negativeFamily : FOClause L ℕ
  positive_subset : positiveFamily ⊆ leftCopy C
  negative_subset : negativeFamily ⊆ rightCopy D
  positive_nonempty : positiveFamily.Nonempty
  negative_nonempty : negativeFamily.Nonempty
  positive_sign : ∀ l ∈ positiveFamily, l.positive = true
  negative_sign : ∀ l ∈ negativeFamily, l.positive = false
  unifier : ℕ → L.Term ℕ
  mostGeneral : AtomMGU.{u, v, 0}
    ((positiveFamily ∪ negativeFamily).image PropLiteral.atom) unifier

/-- Remove precisely the selected families and substitute by their chosen MGU. -/
def resolvent {C D : FOClause L ℕ} (d : InferenceData C D) : FOClause L ℕ :=
  clauseSubst d.unifier
    ((leftCopy C \ d.positiveFamily) ∪ (rightCopy D \ d.negativeFamily))

/-- Finite trees with only premise and the specified generalized inference. -/
inductive Derives (Γ : Set (FOClause L ℕ)) : FOClause L ℕ → Prop
  | premise {C} : C ∈ Γ → Derives Γ C
  | resolve {C D} (d : InferenceData C D) :
      Derives Γ C → Derives Γ D → Derives Γ (resolvent d)

/-- The exact singleton-family restriction, with no instantiation constructor. -/
inductive BinaryDerives (Γ : Set (FOClause L ℕ)) : FOClause L ℕ → Prop
  | premise {C} : C ∈ Γ → BinaryDerives Γ C
  | resolve {C D} (d : InferenceData C D) :
      d.positiveFamily.card = 1 → d.negativeFamily.card = 1 →
      BinaryDerives Γ C → BinaryDerives Γ D → BinaryDerives Γ (resolvent d)

theorem inference_sound {M : Type z} [L.Structure M] [Nonempty M]
    {C D : FOClause L ℕ} (d : InferenceData C D)
    (hC : ∀ v : ℕ → M, ClauseRealize C v)
    (hD : ∀ v : ℕ → M, ClauseRealize D v) (v : ℕ → M) :
    ClauseRealize (resolvent d) v := by
  classical
  have hCμ : ClauseRealize (clauseSubst d.unifier (leftCopy C)) v := by
    apply (clause_subst_realize _ _ _).mpr
    change ClauseRealize (clauseSubst (fun x => Term.var (even x)) C) _
    apply (clause_subst_realize _ _ _).mpr
    exact hC _
  have hDμ : ClauseRealize (clauseSubst d.unifier (rightCopy D)) v := by
    apply (clause_subst_realize _ _ _).mpr
    change ClauseRealize (clauseSubst (fun x => Term.var (odd x)) D) _
    apply (clause_subst_realize _ _ _).mpr
    exact hD _
  obtain ⟨s, hs⟩ := d.positive_nonempty
  let p := s.atom.subst d.unifier
  have hall (l : FOLiteral L ℕ) (hl : l ∈ d.positiveFamily ∪ d.negativeFamily) :
      l.atom.subst d.unifier = p := by
    exact d.mostGeneral.1 _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩) _
      (Finset.mem_image.mpr ⟨s, Finset.mem_union_left _ hs, rfl⟩)
  by_cases hp : p.Realize v
  · obtain ⟨l, hl, ht⟩ := hDμ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hl
    have hn : k ∉ d.negativeFamily := by
      intro hT
      have hsign := d.negative_sign k hT
      have he := hall k (Finset.mem_union_right _ hT)
      have hf : ¬ p.Realize v := by simpa [literalSubst, hsign, he] using ht
      exact hf hp
    exact ⟨literalSubst d.unifier k,
      Finset.mem_image.mpr ⟨k, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hk, hn⟩), rfl⟩, ht⟩
  · obtain ⟨l, hl, ht⟩ := hCμ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hl
    have hn : k ∉ d.positiveFamily := by
      intro hS
      have hsign := d.positive_sign k hS
      have he := hall k (Finset.mem_union_left _ hS)
      have hf : p.Realize v := by simpa [literalSubst, hsign, he] using ht
      exact hp hf
    exact ⟨literalSubst d.unifier k,
      Finset.mem_image.mpr ⟨k, Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hk, hn⟩), rfl⟩, ht⟩

theorem derivation_sound {M : Type z} [L.Structure M] [Nonempty M]
    {Γ : Set (FOClause L ℕ)} {C : FOClause L ℕ} (d : Derives Γ C)
    (hΓ : ∀ D ∈ Γ, ∀ v : ℕ → M, (clauseToFormula D).Realize v) :
    ∀ v : ℕ → M, (clauseToFormula C).Realize v := by
  induction d with
  | premise hC => exact hΓ _ hC
  | @resolve C D data _ _ ihC ihD =>
    intro v
    apply (clause_formula_realize _ _).mpr
    apply inference_sound data ?_ ?_ v
    · intro w
      exact (clause_formula_realize _ _).mp (ihC w)
    · intro w
      exact (clause_formula_realize _ _).mp (ihD w)

theorem refutation_unsatisfiable {Γ : Set (FOClause L ℕ)}
    (d : Derives Γ ∅) : ¬ ClauseSatisfiable Γ := by
  classical
  rintro ⟨M, hM⟩
  let v : ℕ → M := fun _ => Classical.choice inferInstance
  have h := (clause_formula_realize (∅ : FOClause L ℕ) v).mp (derivation_sound d hM v)
  simp [ClauseRealize] at h

/-- Exact fibers are necessary because a finite image may identify literals. -/
theorem image_delete_fiber {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (U : Finset X) (y : Y) :
    (U \ U.filter (fun x => f x = y)).image f = (U.image f).erase y := by
  classical
  ext z
  simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
    exact ⟨fun he => hn ⟨hx, he⟩, x, hx, rfl⟩
  · rintro ⟨hne, x, hx, rfl⟩
    exact ⟨x, ⟨hx, fun h => hne h.2⟩, rfl⟩

/-- Ground pivot selections include every preimage in the supplied parent. -/
def pivotFiber (γ : ℕ → GroundTerm L) (C : FOClause L ℕ)
    (l : FOLiteral L Empty) : FOClause L ℕ := C.filter (fun k => literalSubst γ k = l)

private theorem clause_subst_union (σ : α → L.Term β) (C D : FOClause L α) :
    clauseSubst σ (C ∪ D) = clauseSubst σ C ∪ clauseSubst σ D := by
  classical
  exact Finset.image_union _ _

private theorem clause_subst_fiber (γ : ℕ → GroundTerm L) (C : FOClause L ℕ)
    (l : FOLiteral L Empty) :
    clauseSubst γ (C \ pivotFiber γ C l) = (clauseSubst γ C).erase l := by
  exact image_delete_fiber (literalSubst γ) C l

/-- One step lifts to the exact resolvent using the specified full fibers. -/
theorem one_step_lifting (C D : FOClause L ℕ) (σ τ : ℕ → GroundTerm L)
    (p : GroundAtom L) (hp : Lemmatheca.ProofTheory.Resolution.pos p ∈ clauseSubst σ C)
    (hn : Lemmatheca.ProofTheory.Resolution.neg p ∈ clauseSubst τ D) :
    ∃ d : InferenceData C D,
      d.positiveFamily = pivotFiber (combine σ τ) (leftCopy C) (Lemmatheca.ProofTheory.Resolution.pos p) ∧
      d.negativeFamily = pivotFiber (combine σ τ) (rightCopy D) (Lemmatheca.ProofTheory.Resolution.neg p) ∧
      ∃ ρ : ℕ → GroundTerm L,
        clauseSubst ρ (resolvent d) = Lemmatheca.ProofTheory.Resolution.resolvent p (clauseSubst σ C) (clauseSubst τ D) := by
  classical
  let γ := combine σ τ
  let S := pivotFiber γ (leftCopy C) (Lemmatheca.ProofTheory.Resolution.pos p)
  let T := pivotFiber γ (rightCopy D) (Lemmatheca.ProofTheory.Resolution.neg p)
  have hc := (copies_substitute C D σ τ).1
  have hd := (copies_substitute C D σ τ).2
  have hp' : Lemmatheca.ProofTheory.Resolution.pos p ∈ clauseSubst γ (leftCopy C) := by
    rw [hc]
    exact hp
  have hn' : Lemmatheca.ProofTheory.Resolution.neg p ∈ clauseSubst γ (rightCopy D) := by
    rw [hd]
    exact hn
  have hSsub : S ⊆ leftCopy C := Finset.filter_subset _ _
  have hTsub : T ⊆ rightCopy D := Finset.filter_subset _ _
  have hSne : S.Nonempty := by
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hp'
    exact ⟨l, Finset.mem_filter.mpr ⟨hl, he⟩⟩
  have hTne : T.Nonempty := by
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hn'
    exact ⟨l, Finset.mem_filter.mpr ⟨hl, he⟩⟩
  have hSsign (l : FOLiteral L ℕ) (hl : l ∈ S) : l.positive = true := by
    have he := congrArg PropLiteral.positive (Finset.mem_filter.mp hl).2
    exact he
  have hTsign (l : FOLiteral L ℕ) (hl : l ∈ T) : l.positive = false := by
    have he := congrArg PropLiteral.positive (Finset.mem_filter.mp hl).2
    exact he
  let A := (S ∪ T).image PropLiteral.atom
  have hpivot (l : FOLiteral L ℕ) (hl : l ∈ S ∪ T) : l.atom.subst γ = p := by
    rcases Finset.mem_union.mp hl with hl | hl
    · exact congrArg PropLiteral.atom (Finset.mem_filter.mp hl).2
    · exact congrArg PropLiteral.atom (Finset.mem_filter.mp hl).2
  have hA : AtomUnifies γ A := by
    intro a ha b hb
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hb
    exact (hpivot l hl).trans (hpivot k hk).symm
  obtain ⟨μ, hμ, hMGU⟩ := atom_unify_success.{u, v, 0, 0} A γ hA
  obtain ⟨ρ, hρ⟩ := atom_unify_factorization A (atom_unifier_heads A γ hA) μ hμ γ hA
  let data : InferenceData C D :=
    ⟨S, T, hSsub, hTsub, hSne, hTne, hSsign, hTsign, μ, hMGU⟩
  refine ⟨data, rfl, rfl, ρ, ?_⟩
  change clauseSubst ρ (clauseSubst μ ((leftCopy C \ S) ∪ (rightCopy D \ T))) = _
  rw [clause_subst_subst]
  have hcomp : TermUnification.compose ρ μ = γ := funext hρ
  rw [hcomp]
  change clauseSubst γ
    ((leftCopy C \ pivotFiber γ (leftCopy C) (Lemmatheca.ProofTheory.Resolution.pos p)) ∪
      (rightCopy D \ pivotFiber γ (rightCopy D) (Lemmatheca.ProofTheory.Resolution.neg p))) = _
  rw [clause_subst_union, clause_subst_fiber, clause_subst_fiber, hc, hd]
  rfl

/-- Induct on the existing premise/resolve proof trees, without weakening. -/
theorem tree_lifting (Γ : Set (FOClause L ℕ)) (Δ : Lemmatheca.ProofTheory.Resolution.ClauseSet (GroundAtom L))
    (hΔ : (↑Δ : Set (GroundClause L)) ⊆ GroundClauses Γ)
    {G : GroundClause L} (d : Lemmatheca.ProofTheory.Resolution.Derives Δ G) :
    ∃ C : FOClause L ℕ, Derives Γ C ∧ ∃ σ : ℕ → GroundTerm L, clauseSubst σ C = G := by
  induction d with
  | premise hG =>
    obtain ⟨C, hC, σ, he⟩ := hΔ hG
    exact ⟨C, .premise hC, σ, he⟩
  | @resolve C D p hp hn _ _ ihC ihD =>
    obtain ⟨C', hC, σ, heC⟩ := ihC
    obtain ⟨D', hD, τ, heD⟩ := ihD
    have hp' : Lemmatheca.ProofTheory.Resolution.pos p ∈ clauseSubst σ C' := heC.symm ▸ hp
    have hn' : Lemmatheca.ProofTheory.Resolution.neg p ∈ clauseSubst τ D' := heD.symm ▸ hn
    obtain ⟨data, _, _, ρ, he⟩ := one_step_lifting C' D' σ τ p hp' hn'
    refine ⟨resolvent data, .resolve data hC hD, ρ, ?_⟩
    simpa only [heC, heD] using he

theorem refutation_lifting (Γ : Set (FOClause L ℕ)) (Δ : Lemmatheca.ProofTheory.Resolution.ClauseSet (GroundAtom L))
    (hΔ : (↑Δ : Set (GroundClause L)) ⊆ GroundClauses Γ)
    (d : Lemmatheca.ProofTheory.Resolution.Derives Δ ∅) : Derives Γ ∅ := by
  obtain ⟨C, hC, σ, he⟩ := tree_lifting Γ Δ hΔ d
  have hc : C = ∅ := by
    exact Finset.image_eq_empty.mp he
  simpa only [hc] using hC

theorem refutational_completeness [Nonempty (GroundTerm L)]
    (Γ : Set (FOClause L ℕ)) : ¬ ClauseSatisfiable Γ ↔ Derives Γ ∅ := by
  constructor
  · intro h
    obtain ⟨Δ, hΔ, d⟩ := (finite_ground_refutation Γ).mp h
    exact refutation_lifting Γ Δ hΔ d
  · exact refutation_unsatisfiable

end
end Lemmatheca.MathematicalLogic.FirstOrderResolution
