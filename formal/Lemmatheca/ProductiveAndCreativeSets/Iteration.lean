import Lemmatheca.ProductiveAndCreativeSets.Completeness
import Lemmatheca.EffectiveEnumerations.Increasing

/-! The finite-domain iteration, its exact prefix invariant, and a range recognizer. -/
namespace Lemmatheca.ComputabilityTheory.ProductiveAndCreativeSets

open UniversalComputation EffectiveEnumerations

def extensionProgram (p : ℕ → ℕ) (e x : ℕ) : Part ℕ :=
  if x = p e then Part.some 0 else phi e x

def ExtensionIndex (p : ℕ → ℕ) (v : ℕ) : Prop :=
  ∀ e x, phi v (Nat.pair e x) = extensionProgram p e x

def extensionMap (v e : ℕ) : ℕ := specialize v e

theorem extension_program_partial {p : ℕ → ℕ} (hp : Computable p) :
    Partrec₂ (extensionProgram p) := by
  have htest : Computable (fun t : ℕ × ℕ => decide (t.2 = p t.1)) :=
    Primrec.eq.decide.to_comp.comp Computable.snd (hp.comp Computable.fst)
  exact (Partrec.cond htest (Computable.const 0).partrec phi_recursive).of_eq
    (fun t => by simp [extensionProgram])

theorem extension_program_domain (p : ℕ → ℕ) (e x : ℕ) :
    (extensionProgram p e x).Dom ↔ x ∈ indexSet e ∪ {p e} := by
  by_cases he : x = p e <;> simp [extensionProgram, he, indexSet]

theorem extension_index_exists {p : ℕ → ℕ} (hp : Computable p) :
    ∃ v, ExtensionIndex p v := by
  obtain ⟨v, hv⟩ := phi_complete (Partrec₂.unpaired'.mpr (extension_program_partial hp))
  refine ⟨v, fun e x => ?_⟩
  simpa only [Nat.unpaired, Nat.unpair_pair] using congrFun hv (Nat.pair e x)

theorem extension_map_primitive (v : ℕ) : Primrec (extensionMap v) := by
  exact specialize_primitive.comp (Primrec.const v) Primrec.id

theorem extension_map_eval (p : ℕ → ℕ) (v : ℕ) (hv : ExtensionIndex p v) (e x : ℕ) :
    phi (extensionMap v e) x = extensionProgram p e x := by
  exact (specialize_eval v e x).trans (hv e x)

theorem extension_map_domain (p : ℕ → ℕ) (v : ℕ) (hv : ExtensionIndex p v) (e : ℕ) :
    indexSet (extensionMap v e) = indexSet e ∪ {p e} := by
  ext x
  change (phi (extensionMap v e) x).Dom ↔ x ∈ indexSet e ∪ {p e}
  rw [extension_map_eval p v hv e x, extension_program_domain]

def indexIteration (v e₀ : ℕ) : ℕ → ℕ := Nat.rec e₀ (fun _ e => extensionMap v e)

def escapeSequence (p : ℕ → ℕ) (v e₀ n : ℕ) : ℕ := p (indexIteration v e₀ n)

theorem index_iteration_primitive (v e₀ : ℕ) : Primrec (indexIteration v e₀) := by
  exact Primrec.nat_rec₁ e₀ ((extension_map_primitive v).comp Primrec.snd)

theorem escape_sequence_computable {p : ℕ → ℕ} (hp : Computable p) (v e₀ : ℕ) :
    Computable (escapeSequence p v e₀) := by
  exact hp.comp (index_iteration_primitive v e₀).to_comp

theorem iteration_prefix_invariant {B : Set ℕ} {p : ℕ → ℕ}
    (hp : ProductiveFunction B p) (v e₀ : ℕ) (hv : ExtensionIndex p v)
    (h₀ : indexSet e₀ = ∅) :
    ∀ n, indexSet (indexIteration v e₀ n) =
      {z | ∃ i < n, escapeSequence p v e₀ i = z} ∧
        indexSet (indexIteration v e₀ n) ⊆ B := by
  intro n
  induction n with
  | zero => simp [indexIteration, h₀]
  | succ n ih =>
    have hnew := hp.2 (indexIteration v e₀ n) ih.2
    have hdom : indexSet (indexIteration v e₀ (n + 1)) =
        indexSet (indexIteration v e₀ n) ∪ {escapeSequence p v e₀ n} :=
      extension_map_domain p v hv (indexIteration v e₀ n)
    constructor
    · rw [hdom, ih.1]
      ext z
      constructor
      · rintro (⟨i, hi, he⟩ | hz)
        · exact ⟨i, Nat.lt_succ_of_lt hi, he⟩
        · exact ⟨n, Nat.lt_succ_self n, (Set.mem_singleton_iff.mp hz).symm⟩
      · rintro ⟨i, hi, he⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
        · exact Or.inl ⟨i, hi, he⟩
        · exact Or.inr (Set.mem_singleton_iff.mpr he.symm)
    · rw [hdom]
      exact Set.union_subset ih.2 (Set.singleton_subset_iff.mpr hnew.1)

theorem escape_sequence_fresh {B : Set ℕ} {p : ℕ → ℕ}
    (hp : ProductiveFunction B p) (v e₀ : ℕ) (hv : ExtensionIndex p v)
    (h₀ : indexSet e₀ = ∅) :
    ∀ n, escapeSequence p v e₀ n ∈ B \ indexSet (indexIteration v e₀ n) := by
  intro n
  exact hp.2 (indexIteration v e₀ n) (iteration_prefix_invariant hp v e₀ hv h₀ n).2

theorem escape_sequence_injective {B : Set ℕ} {p : ℕ → ℕ}
    (hp : ProductiveFunction B p) (v e₀ : ℕ) (hv : ExtensionIndex p v)
    (h₀ : indexSet e₀ = ∅) : Function.Injective (escapeSequence p v e₀) := by
  have hne (a b : ℕ) (hab : a < b) :
      escapeSequence p v e₀ a ≠ escapeSequence p v e₀ b := by
    intro heq
    apply (escape_sequence_fresh hp v e₀ hv h₀ b).2
    rw [(iteration_prefix_invariant hp v e₀ hv h₀ b).1]
    exact ⟨a, hab, heq⟩
  intro i j heq
  by_contra hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hne i j hlt heq
  · exact hne j i hgt heq.symm

theorem escape_range_properties {B : Set ℕ} {p : ℕ → ℕ}
    (hp : ProductiveFunction B p) (v e₀ : ℕ) (hv : ExtensionIndex p v)
    (h₀ : indexSet e₀ = ∅) :
    Set.range (escapeSequence p v e₀) ⊆ B ∧
      (Set.range (escapeSequence p v e₀)).Infinite ∧
        REPred (Set.range (escapeSequence p v e₀)) := by
  refine ⟨?_, Set.infinite_range_of_injective (escape_sequence_injective hp v e₀ hv h₀), ?_⟩
  · rintro x ⟨n, rfl⟩
    exact (escape_sequence_fresh hp v e₀ hv h₀ n).1
  · apply (enumerable_iff_total_range _).mpr
    exact Or.inr ⟨escapeSequence p v e₀, escape_sequence_computable hp.1 v e₀,
      fun _ => Iff.rfl⟩

theorem productive_infinite_enumerable_subset {B : Set ℕ} (hB : Productive B) :
    ∃ X : Set ℕ, X ⊆ B ∧ X.Infinite ∧ REPred X := by
  obtain ⟨p, hp⟩ := hB
  obtain ⟨e₀, h₀⟩ := empty_index_exists
  obtain ⟨v, hv⟩ := extension_index_exists hp.1
  exact ⟨Set.range (escapeSequence p v e₀), escape_range_properties hp v e₀ hv h₀⟩

theorem productive_infinite_decidable_subset {B : Set ℕ} (hB : Productive B) :
    ∃ X : Set ℕ, X ⊆ B ∧ X.Infinite ∧ ComputablePred X := by
  obtain ⟨X, hXB, hXinf, hXce⟩ := productive_infinite_enumerable_subset hB
  obtain ⟨Y, hYX, hYinf, hYdec⟩ := infinite_enumerable_decidable_subset X hXce hXinf
  exact ⟨Y, hYX.trans hXB, hYinf, hYdec⟩

def rangeRecognizer (f : ℕ → ℕ) (y : ℕ) : Part ℕ :=
  (Nat.rfind (fun n => Part.some (decide (f n = y)))).map (fun _ => 0)

theorem range_recognizer_partial {f : ℕ → ℕ} (hf : Computable f) :
    Nat.Partrec (rangeRecognizer f) := by
  have htest : Computable₂ (fun y n : ℕ => decide (f n = y)) :=
    Primrec.eq.decide.to_comp.comp (hf.comp Computable.snd) Computable.fst
  exact Partrec.nat_iff.mp ((Partrec.rfind htest.partrec₂).map (Computable.const 0).to₂)

theorem range_recognizer_domain (f : ℕ → ℕ) (y : ℕ) :
    (rangeRecognizer f y).Dom ↔ y ∈ Set.range f := by
  change (Nat.rfind (fun n => Part.some (decide (f n = y)))).Dom ↔ y ∈ Set.range f
  constructor
  · intro hd
    obtain ⟨n, hn, _⟩ := Nat.rfind_dom.mp hd
    exact ⟨n, by simpa using hn⟩
  · rintro ⟨n, hn⟩
    exact Nat.rfind_dom.mpr ⟨n, by simpa using hn, fun _ => trivial⟩

theorem range_recognizer_index {f : ℕ → ℕ} (hf : Computable f) :
    ∃ b, ∀ y, phi b y = rangeRecognizer f y := by
  obtain ⟨b, hb⟩ := phi_complete (range_recognizer_partial hf)
  exact ⟨b, fun y => congrFun hb y⟩

theorem total_domain_not_inside_productive {B : Set ℕ} (hB : Productive B)
    (q : ℕ) (hq : ∀ x, (phi q x).Dom) :
    indexSet q = Set.univ ∧ ¬ indexSet q ⊆ B := by
  have hqeq : indexSet q = Set.univ := Set.eq_univ_of_forall hq
  refine ⟨hqeq, ?_⟩
  intro hsub
  have hBeq : B = Set.univ := Set.eq_univ_of_forall
    (fun x => hsub (by rw [hqeq]; trivial))
  apply productive_not_enumerable hB
  rw [hBeq]
  exact (Partrec.some : Partrec (@Part.some ℕ)).dom_re

theorem range_index_escape {B : Set ℕ} {p : ℕ → ℕ}
    (hp : ProductiveFunction B p) (v e₀ : ℕ) (hv : ExtensionIndex p v)
    (h₀ : indexSet e₀ = ∅) (b : ℕ)
    (hb : ∀ y, phi b y = rangeRecognizer (escapeSequence p v e₀) y) :
    indexSet b = Set.range (escapeSequence p v e₀) ∧
      p b ∈ B \ Set.range (escapeSequence p v e₀) := by
  have hEq : indexSet b = Set.range (escapeSequence p v e₀) := by
    ext y
    change (phi b y).Dom ↔ y ∈ Set.range (escapeSequence p v e₀)
    rw [hb y, range_recognizer_domain]
  have hsub : indexSet b ⊆ B := by
    rw [hEq]
    exact (escape_range_properties hp v e₀ hv h₀).1
  exact ⟨hEq, by simpa only [hEq] using hp.2 b hsub⟩

theorem escape_range_proper {B : Set ℕ} {p : ℕ → ℕ}
    (hp : ProductiveFunction B p) (v e₀ : ℕ) (hv : ExtensionIndex p v)
    (h₀ : indexSet e₀ = ∅) : Set.range (escapeSequence p v e₀) ⊂ B := by
  obtain ⟨b, hb⟩ := range_recognizer_index (escape_sequence_computable hp.1 v e₀)
  have hescape := (range_index_escape hp v e₀ hv h₀ b hb).2
  refine Set.ssubset_def.mpr ⟨(escape_range_properties hp v e₀ hv h₀).1, ?_⟩
  intro hback
  exact hescape.2 (hback hescape.1)

end Lemmatheca.ComputabilityTheory.ProductiveAndCreativeSets
