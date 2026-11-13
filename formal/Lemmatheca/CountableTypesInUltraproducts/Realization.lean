import Lemmatheca.CountableTypesInUltraproducts.CountableIncompleteness
import Lemmatheca.TypesAndRealization.Types
import Mathlib.ModelTheory.Ultraproducts

namespace Lemmatheca.ModelTheory.Ultraproducts.CountableTypes

open FirstOrder FirstOrder.Language Filter Set
universe u v w z
variable {L : Language.{u, v}} {I : Type w}

/-- Actual finite conjunctions in the original shared formula syntax. -/
def prefixConjunction {r : ℕ} (φ : ℕ → L.Formula (Fin r)) (n : ℕ) : L.Formula (Fin r) :=
  ((List.range n).map φ).foldr (· ⊓ ·) ⊤

/-- Existential closure of the actual prefixConjunction formula, including the empty context. -/
noncomputable def prefixSentence {r : ℕ} (φ : ℕ → L.Formula (Fin r)) (n : ℕ) :
    L.Sentence := (Formula.relabel Sum.inr (prefixConjunction φ n)).iExs (Fin r)

private theorem prefix_sentence_realize {r : ℕ} (φ : ℕ → L.Formula (Fin r)) (n : ℕ)
    {N : Type z} [L.Structure N] :
    N ⊨ prefixSentence φ n ↔ ∃ a : Fin r → N, (prefixConjunction φ n).Realize a := by
  simp only [prefixSentence, Sentence.Realize, Formula.realize_iExs,
    Formula.realize_relabel, Function.comp_def, Sum.elim_inr]

theorem prefix_realize {r : ℕ} (φ : ℕ → L.Formula (Fin r)) (n : ℕ)
    {N : Type z} [L.Structure N] (a : Fin r → N) :
    (prefixConjunction φ n).Realize a ↔ ∀ k < n, (φ k).Realize a := by
  change @BoundedFormula.Realize L N _ (Fin r) 0
    (((List.range n).map φ).foldr (· ⊓ ·) ⊤) a default ↔ _
  rw [BoundedFormula.realize_foldr_inf]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Formula.Realize]

variable (U : Ultrafilter I) (D : I → Type z)
variable [∀ i, L.Structure (D i)] [∀ i, Nonempty (D i)]

/-- Coordinate truth of finite solvability; every prefixConjunction uses the same original formulas. -/
def prefixTruth {r : ℕ} (φ : ℕ → L.Formula (Fin r)) (n : ℕ) : Set I :=
  {i | ∃ a : Fin r → D i, (prefixConjunction φ n).Realize a}

theorem prefix_truth_sets {r : ℕ} (φ : ℕ → L.Formula (Fin r))
    (hφ : ∀ n, ∃ a : Fin r → (U : Filter I).Product D, ∀ k < n, (φ k).Realize a) :
    (prefixTruth D φ 0 = univ) ∧ Antitone (prefixTruth D φ) ∧
      ∀ n, prefixTruth D φ n ∈ U := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · ext i
    simp only [prefixTruth, mem_ofPred_eq, mem_univ, iff_true]
    refine ⟨fun _ => Classical.choice (inferInstance : Nonempty (D i)), ?_⟩
    exact (prefix_realize φ 0 _).mpr (fun k hk => by omega)
  · intro m n hmn i hi
    obtain ⟨a, ha⟩ := hi
    refine ⟨a, (prefix_realize φ m a).mpr ?_⟩
    intro k hk
    exact (prefix_realize φ n a).mp ha k (lt_of_lt_of_le hk hmn)
  · intro n
    obtain ⟨a, ha⟩ := hφ n
    have hσ : (U : Filter I).Product D ⊨ prefixSentence φ n :=
      (prefix_sentence_realize φ n).mpr ⟨a, (prefix_realize φ n a).mpr ha⟩
    have hh := (FirstOrder.Language.Ultraproduct.sentence_realize (u := U)
      (M := D) (prefixSentence φ n)).mp hσ
    exact hh.mono (fun i hi => (prefix_sentence_realize φ n).mp hi)

/-- Intersect the actual coordinate truth sets with the prescribed incompleteness witness. -/
def goodSets {r : ℕ} (X : IncompletenessWitness U) (φ : ℕ → L.Formula (Fin r))
    (n : ℕ) : Set I := X.sets n ∩ prefixTruth D φ n

theorem good_sets {r : ℕ} (X : IncompletenessWitness U) (φ : ℕ → L.Formula (Fin r))
    (hφ : ∀ n, ∃ a : Fin r → (U : Filter I).Product D, ∀ k < n, (φ k).Realize a) :
    goodSets U D X φ 0 = univ ∧ Antitone (goodSets U D X φ) ∧
      (⋂ n, goodSets U D X φ n) = ∅ ∧ ∀ n, goodSets U D X φ n ∈ U := by
  obtain ⟨hzero, hanti, hlarge⟩ := prefix_truth_sets U D φ hφ
  refine ⟨by simp [goodSets, X.zero, hzero], ?_, ?_, ?_⟩
  · intro m n hmn i hi
    exact ⟨X.decreasing hmn hi.1, hanti hmn hi.2⟩
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hh : i ∈ ⋂ n, X.sets n := by
      simp only [mem_iInter] at hi ⊢
      intro n
      exact (hi n).1
    rw [X.empty] at hh
    exact hh
  · intro n
    exact inter_mem (X.large n) (hlarge n)

/-- The exact coordinate witness construction, not an assumed realization principle. -/
theorem coordinate_diagonal {r : ℕ} (X : IncompletenessWitness U)
    (φ : ℕ → L.Formula (Fin r))
    (hφ : ∀ n, ∃ a : Fin r → (U : Filter I).Product D, ∀ k < n, (φ k).Realize a) :
    ∃ (hempty : (⋂ n, goodSets U D X φ n) = ∅)
      (f : Fin r → ∀ i, D i),
      (∀ i, (prefixConjunction φ (cutoff (goodSets U D X φ) hempty i)).Realize (fun j => f j i)) ∧
      (∀ k, goodSets U D X φ (k + 1) ⊆ {i | (φ k).Realize (fun j => f j i)}) ∧
      ∀ k, (φ k).Realize (fun j => (f j : (U : Filter I).Product D)) := by
  classical
  obtain ⟨hzero, hanti, hempty, hlarge⟩ := good_sets U D X φ hφ
  have hsol : ∀ i, ∃ a : Fin r → D i,
      (prefixConjunction φ (cutoff (goodSets U D X φ) hempty i)).Realize a := by
    intro i
    exact (cutoff_maximum _ hzero hanti hempty i).1.2
  choose g hg using hsol
  have hinclusion (k : ℕ) :
      goodSets U D X φ (k + 1) ⊆ {i | (φ k).Realize (g i)} := by
    intro i hi
    have hk := ((cutoff_maximum _ hzero hanti hempty i).2 (k + 1)).mp hi
    exact (prefix_realize φ _ (g i)).mp (hg i) k (by omega)
  refine ⟨hempty, fun j i => g i j, hg, hinclusion, ?_⟩
  intro k
  apply (FirstOrder.Language.Ultraproduct.realize_formula_cast (u := U) (M := D)
    (φ k) (fun j i => g i j)).mpr
  exact mem_of_superset (hlarge (k + 1)) (hinclusion k)

/-- Countability applies to this formula collection; the language may have any set size. -/
theorem countable_realization {r : ℕ} (hU : CountablyIncomplete U)
    (p : Set (L.Formula (Fin r))) (hp : p.Countable)
    (hf : Types.FinitelyRealized ((U : Filter I).Product D) p) :
    ∃ a : Fin r → (U : Filter I).Product D, Types.Realizes p a := by
  classical
  let q := insert (⊤ : L.Formula (Fin r)) p
  have hq : q.Countable := hp.insert _
  obtain ⟨φ, hφ⟩ := hq.exists_eq_range (by exact ⟨⊤, Or.inl rfl⟩)
  have hfq : Types.FinitelyRealized ((U : Filter I).Product D) q := by
    intro s hs
    obtain ⟨a, ha⟩ := hf (s.erase ⊤) (by
      intro θ hθ
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hθ
      exact (hs hmem).resolve_left hne)
    refine ⟨a, fun θ hθ => ?_⟩
    by_cases htop : θ = ⊤
    · subst θ
      simp
    · exact ha θ (Finset.mem_erase.mpr ⟨htop, hθ⟩)
  have hpref : ∀ n, ∃ a : Fin r → (U : Filter I).Product D,
      ∀ k < n, (φ k).Realize a := by
    intro n
    obtain ⟨a, ha⟩ := hfq ((Finset.range n).image φ) (by
      intro θ hθ
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hθ
      rw [hφ]
      exact Set.mem_range_self k)
    refine ⟨a, fun k hk => ha (φ k) (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩)⟩
  obtain ⟨X⟩ := hU
  obtain ⟨_, f, _, _, hall⟩ := coordinate_diagonal U D X φ hpref
  refine ⟨fun j => (f j : (U : Filter I).Product D), fun θ hθ => ?_⟩
  have hθq : θ ∈ q := Or.inr hθ
  rw [hφ] at hθq
  obtain ⟨k, rfl⟩ := hθq
  exact hall k

end Lemmatheca.ModelTheory.Ultraproducts.CountableTypes
