import Lemmatheca.FiniteMindChanges.Basic

/-! Concrete operations on approximations and their prefix revision counts. -/
namespace Lemmatheca.ComputabilityTheory.FiniteMindChanges

open UniversalComputation LimitComputability DifferenceEnumerable

set_option backward.isDefEq.respectTransparency false

def delayedComplement (a : Approximation) : Approximation
  | 0, _ => 0
  | s + 1, x => 1 - a s x

theorem delayed_complement_data (a : Approximation) (A : Set ℕ)
    (hc : Computable₂ a) (hb : Binary a) (ha : Converges a A) :
    Computable₂ (delayedComplement a) ∧ Binary (delayedComplement a) ∧
      StartsZero (delayedComplement a) ∧ Converges (delayedComplement a) Aᶜ := by
  classical
  have hcalc : Computable (fun p : ℕ × ℕ =>
      Nat.casesOn (motive := fun _ => ℕ) p.1 0 (fun s => 1 - a s p.2)) :=
    Computable.nat_casesOn Computable.fst (Computable.const 0)
      (Primrec.nat_sub.to_comp.comp (Computable.const 1)
        (hc.comp Computable.snd (Computable.snd.comp Computable.fst))).to₂
  refine ⟨hcalc.of_eq (fun p => by cases p.1 <;> rfl), ?_, fun _ => rfl, ?_⟩
  · intro s x
    cases s with
    | zero => exact Or.inl rfl
    | succ s => rcases hb s x with h | h <;> simp [delayedComplement, h]
  · obtain ⟨_, _, hneg⟩ := complement_approximation a A hc hb ha
    intro x
    obtain ⟨t, ht⟩ := hneg x
    refine ⟨t + 1, ?_⟩
    intro s hs
    cases s with
    | zero => omega
    | succ s => exact ht s (by omega)

theorem delayed_complement_count (a : Approximation) (hb : Binary a) (hz : StartsZero a) :
    ∀ s x, changeCount (delayedComplement a) (s + 1) x = 1 + changeCount a s x := by
  classical
  intro s x
  induction s with
  | zero => simp [changeCount, delayedComplement, hz x]
  | succ s ih =>
      have heq : (1 - a (s + 1) x = 1 - a s x) ↔ a (s + 1) x = a s x := by
        rcases hb (s + 1) x with h | h <;> rcases hb s x with g | g <;> omega
      change (changeCount (delayedComplement a) (s + 1) x +
        if 1 - a (s + 1) x = 1 - a s x then 0 else 1) =
          1 + (changeCount a s x + if a (s + 1) x = a s x then 0 else 1)
      simp only [heq, ih]
      omega

theorem nce_complement (n : ℕ) (A : Set ℕ) (ha : NCE n A) : NCE (n + 1) Aᶜ := by
  obtain ⟨a, hc, hb, hlim, hz, hn⟩ := ha
  obtain ⟨hbc, hbb, hbz, hblim⟩ := delayed_complement_data a A hc hb hlim
  refine ⟨delayedComplement a, hbc, hbb, hblim, hbz, ?_⟩
  intro s x
  cases s with
  | zero => simp [changeCount]
  | succ s => rw [delayed_complement_count a hb hz]; have := hn s x; omega

def pullbackApproximation (a : Approximation) (f : ℕ → ℕ) (s x : ℕ) : ℕ := a s (f x)

theorem pullback_data (a : Approximation) (A : Set ℕ) (f : ℕ → ℕ)
    (hc : Computable₂ a) (hb : Binary a) (ha : Converges a A)
    (hz : StartsZero a) (hf : Computable f) :
    Computable₂ (pullbackApproximation a f) ∧ Binary (pullbackApproximation a f) ∧
      StartsZero (pullbackApproximation a f) ∧
      Converges (pullbackApproximation a f) (f ⁻¹' A) ∧
      ∀ s x, changeCount (pullbackApproximation a f) s x = changeCount a s (f x) := by
  classical
  refine ⟨hc.comp Computable.fst (hf.comp Computable.snd),
    fun s x => hb s (f x), fun x => hz (f x), ?_, ?_⟩
  · intro x
    obtain ⟨t, ht⟩ := ha (f x)
    refine ⟨t, fun s hs => ?_⟩
    change a s (f x) = indicator (f ⁻¹' A) x
    rw [ht s hs]
    rfl
  · intro s x
    induction s with
    | zero => rfl
    | succ s ih => simp only [changeCount, pullbackApproximation, ih]

theorem nce_preimage (n : ℕ) (A : Set ℕ) (f : ℕ → ℕ)
    (ha : NCE n A) (hf : Computable f) : NCE n (f ⁻¹' A) := by
  obtain ⟨a, hc, hb, hlim, hz, hn⟩ := ha
  obtain ⟨hbc, hbb, hbz, hblim, hcount⟩ := pullback_data a A f hc hb hlim hz hf
  exact ⟨pullbackApproximation a f, hbc, hbb, hblim, hbz,
    fun s x => (hcount s x).le.trans (hn s (f x))⟩

def unionApproximation (a b : Approximation) (s x : ℕ) : ℕ := max (a s x) (b s x)

def intersectionApproximation (a b : Approximation) (s x : ℕ) : ℕ := min (a s x) (b s x)

theorem combination_data (a b : Approximation) (A B : Set ℕ)
    (hca : Computable₂ a) (hcb : Computable₂ b) (hba : Binary a) (hbb : Binary b)
    (hza : StartsZero a) (hzb : StartsZero b) (ha : Converges a A) (hb : Converges b B) :
    (Computable₂ (unionApproximation a b) ∧ Binary (unionApproximation a b) ∧
      StartsZero (unionApproximation a b) ∧ Converges (unionApproximation a b) (A ∪ B)) ∧
    (Computable₂ (intersectionApproximation a b) ∧ Binary (intersectionApproximation a b) ∧
      StartsZero (intersectionApproximation a b) ∧
      Converges (intersectionApproximation a b) (A ∩ B)) := by
  classical
  have hu : Converges (unionApproximation a b) (A ∪ B) := by
    intro x
    obtain ⟨t, ht⟩ := ha x
    obtain ⟨u, hu⟩ := hb x
    refine ⟨max t u, fun s hs => ?_⟩
    simp only [unionApproximation, ht s (by omega), hu s (by omega)]
    simp only [indicator, Set.ofPred, Set.union_def]
    by_cases hA : A x <;> by_cases hB : B x <;>
      simp [hA, hB] <;> tauto
  have hi : Converges (intersectionApproximation a b) (A ∩ B) := by
    intro x
    obtain ⟨t, ht⟩ := ha x
    obtain ⟨u, hu⟩ := hb x
    refine ⟨max t u, fun s hs => ?_⟩
    simp only [intersectionApproximation, ht s (by omega), hu s (by omega)]
    simp only [indicator, Set.ofPred, Set.inter_def]
    by_cases hA : A x <;> by_cases hB : B x <;>
      simp [hA, hB] <;> tauto
  refine ⟨⟨Primrec.nat_max.to_comp.comp hca hcb, ?_, ?_, hu⟩,
    ⟨Primrec.nat_min.to_comp.comp hca hcb, ?_, ?_, hi⟩⟩
  · intro s x
    rcases hba s x with h | h <;> rcases hbb s x with g | g <;>
      simp [unionApproximation, h, g]
  · intro x
    simp [unionApproximation, hza x, hzb x]
  · intro s x
    rcases hba s x with h | h <;> rcases hbb s x with g | g <;>
      simp [intersectionApproximation, h, g]
  · intro x
    simp [intersectionApproximation, hza x, hzb x]

theorem combination_count (a b : Approximation) :
    ∀ s x, changeCount (unionApproximation a b) s x ≤ changeCount a s x + changeCount b s x ∧
      changeCount (intersectionApproximation a b) s x ≤ changeCount a s x + changeCount b s x := by
  classical
  intro s x
  induction s with
  | zero => simp [changeCount]
  | succ s ih =>
      have hmax :
          (if max (a (s + 1) x) (b (s + 1) x) = max (a s x) (b s x) then 0 else 1) ≤
            (if a (s + 1) x = a s x then 0 else 1) +
            (if b (s + 1) x = b s x then 0 else 1) := by
        by_cases h : a (s + 1) x = a s x <;>
          by_cases g : b (s + 1) x = b s x <;> simp [h, g] <;> split_ifs <;> omega
      have hmin :
          (if min (a (s + 1) x) (b (s + 1) x) = min (a s x) (b s x) then 0 else 1) ≤
            (if a (s + 1) x = a s x then 0 else 1) +
            (if b (s + 1) x = b s x then 0 else 1) := by
        by_cases h : a (s + 1) x = a s x <;>
          by_cases g : b (s + 1) x = b s x <;> simp [h, g] <;> split_ifs <;> omega
      simp only [changeCount, unionApproximation, intersectionApproximation] at ih ⊢
      constructor <;> omega

theorem nce_combination (m n : ℕ) (A B : Set ℕ) (ha : NCE m A) (hb : NCE n B) :
    NCE (m + n) (A ∪ B) ∧ NCE (m + n) (A ∩ B) := by
  obtain ⟨a, hca, hba, hla, hza, hna⟩ := ha
  obtain ⟨b, hcb, hbb, hlb, hzb, hnb⟩ := hb
  obtain ⟨⟨huc, hub, huz, hul⟩, ⟨hic, hib, hiz, hil⟩⟩ :=
    combination_data a b A B hca hcb hba hbb hza hzb hla hlb
  constructor
  · refine ⟨unionApproximation a b, huc, hub, hul, huz, fun s x => ?_⟩
    exact (combination_count a b s x).1.trans (Nat.add_le_add (hna s x) (hnb s x))
  · refine ⟨intersectionApproximation a b, hic, hib, hil, hiz, fun s x => ?_⟩
    exact (combination_count a b s x).2.trans (Nat.add_le_add (hna s x) (hnb s x))

end Lemmatheca.ComputabilityTheory.FiniteMindChanges
