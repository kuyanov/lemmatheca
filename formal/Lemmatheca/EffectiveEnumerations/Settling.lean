import Lemmatheca.EffectiveEnumerations.Increasing

/-! Settling moduli for the supplied approximation, with both specified algorithms. -/
namespace Lemmatheca.ComputabilityTheory.EffectiveEnumerations

open UniversalComputation

def Settles (A : Set ℕ) (F : ℕ → Set ℕ) (n s : ℕ) : Prop :=
  ∀ x < n, x ∈ A ↔ x ∈ F s

def SettlingModulus (A : Set ℕ) (F : ℕ → Set ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ n, Settles A F n (m n)

theorem settling_persists (A : Set ℕ) (F : ℕ → Set ℕ)
    (hmono : Monotone F) (hcover : ∀ x, x ∈ A ↔ ∃ s, x ∈ F s)
    {n s t : ℕ} (hs : Settles A F n s) (hst : s ≤ t) : Settles A F n t := by
  intro x hx
  constructor
  · intro ha
    exact hmono hst ((hs x hx).mp ha)
  · intro ht
    exact (hcover x).mpr ⟨t, ht⟩

theorem prefix_settled_exists (A : Set ℕ) (F : ℕ → Set ℕ)
    (hmono : Monotone F) (hcover : ∀ x, x ∈ A ↔ ∃ s, x ∈ F s) (n : ℕ) :
    ∃ s, Settles A F n s := by
  classical
  induction n with
  | zero => exact ⟨0, by intro x hx; omega⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    by_cases hn : n ∈ A
    · obtain ⟨t, ht⟩ := (hcover n).mp hn
      refine ⟨max s t, ?_⟩
      intro x hx
      by_cases hxn : x < n
      · exact settling_persists A F hmono hcover hs (Nat.le_max_left _ _) x hxn
      · have he : x = n := by omega
        subst x
        exact ⟨fun _ => hmono (Nat.le_max_right _ _) ht, fun _ => hn⟩
    · refine ⟨s, ?_⟩
      intro x hx
      by_cases hxn : x < n
      · exact hs x hxn
      · have he : x = n := by omega
        subst x
        exact ⟨fun ha => False.elim (hn ha), fun ht => (hcover n).mpr ⟨s, ht⟩⟩

noncomputable def leastSettlingStage {A : Set ℕ} (F : ComputableApproximation A)
    (n : ℕ) : ℕ := by
  classical
  exact Nat.find (prefix_settled_exists A F.atStage
    (approximation_stages F).2.1 (approximation_stages F).2.2 n)

theorem least_settling_spec {A : Set ℕ} (F : ComputableApproximation A) :
    SettlingModulus A F.atStage (leastSettlingStage F) ∧
      (∀ n s, Settles A F.atStage n s → leastSettlingStage F n ≤ s) ∧
      leastSettlingStage F 0 = 0 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro n
    unfold leastSettlingStage
    exact Nat.find_spec _
  · intro n s hs
    unfold leastSettlingStage
    exact Nat.find_min' _ hs
  · unfold leastSettlingStage
    apply (Nat.find_eq_zero _).mpr
    intro x hx
    omega

theorem finite_global_stage (A : Set ℕ) (F : ℕ → Set ℕ)
    (hmono : Monotone F) (hcover : ∀ x, x ∈ A ↔ ∃ s, x ∈ F s)
    (hA : A.Finite) : ∃ s, ∀ t, s ≤ t → F t = A := by
  classical
  let b := hA.toFinset.sup id
  have hb (x : ℕ) (hx : x ∈ A) : x ≤ b :=
    Finset.le_sup (f := id) (by simpa using hx)
  obtain ⟨s, hs⟩ := prefix_settled_exists A F hmono hcover (b + 1)
  refine ⟨s, ?_⟩
  intro t hst
  ext x
  constructor
  · intro ht
    exact (hcover x).mpr ⟨t, ht⟩
  · intro ha
    exact hmono hst ((hs x (Nat.lt_succ_of_le (hb x ha))).mp ha)

def modulusDecider {A : Set ℕ} (F : ComputableApproximation A)
    (m : ℕ → ℕ) (x : ℕ) : ℕ := F.test (m (x + 1)) x

theorem modulus_decider_correct {A : Set ℕ} (F : ComputableApproximation A)
    (m : ℕ → ℕ) (hc : Computable m) (hm : SettlingModulus A F.atStage m) :
    Computable (modulusDecider F m) ∧
      ∀ x, modulusDecider F m x = indicator A x := by
  classical
  refine ⟨F.test_computable.comp (hc.comp Computable.succ) Computable.id, ?_⟩
  intro x
  have ht : x ∈ A ↔ F.test (m (x + 1)) x = 1 := hm (x + 1) x (Nat.lt_succ_self x)
  by_cases hx : A x
  · simpa [modulusDecider, indicator, hx] using ht.mp hx
  · have hnot : F.test (m (x + 1)) x ≠ 1 := fun h => hx (ht.mpr h)
    have hz := (F.binary (m (x + 1)) x).resolve_right hnot
    simpa [modulusDecider, indicator, hx] using hz

def PositiveSettled {A : Set ℕ} (F : ComputableApproximation A)
    (χ : ℕ → ℕ) (n s : ℕ) : Prop :=
  ∀ x < n, χ x = 0 ∨ F.test s x = 1

theorem positive_settled_computable {A : Set ℕ} (F : ComputableApproximation A)
    (χ : ℕ → ℕ) (hc : Computable χ) :
    ComputablePred (fun p : ℕ × ℕ => PositiveSettled F χ p.1 p.2) := by
  classical
  have hR : ComputablePred (fun p : (ℕ × ℕ) × ℕ => χ p.2 = 0 ∨ F.test p.1.2 p.2 = 1) := by
    apply Computable.computablePred
    simpa only [Bool.decide_or] using
      (Primrec.or.to_comp.comp
        (Primrec.eq.decide.to_comp.comp (hc.comp Computable.snd) (Computable.const 0))
        (Primrec.eq.decide.to_comp.comp
          (F.test_computable.comp (Computable.snd.comp Computable.fst) Computable.snd)
          (Computable.const 1)))
  have hb := computable_bounded_forall
    (R := fun p : ℕ × ℕ => fun x => χ x = 0 ∨ F.test p.2 x = 1) hR
  exact (hb.decide.comp (Computable.id.pair Computable.fst)).computablePred

private theorem positive_settled_iff {A : Set ℕ} (F : ComputableApproximation A)
    (χ : ℕ → ℕ) (hχ : ∀ x, χ x = indicator A x) (n s : ℕ) :
    PositiveSettled F χ n s ↔ Settles A F.atStage n s := by
  classical
  constructor
  · intro h x hx
    constructor
    · intro hA
      rcases h x hx with hz | hp
      · have hAx : A x := hA
        have : χ x = 1 := by simp [hχ, indicator, hAx]
        omega
      · exact hp
    · intro hp
      exact (F.exhaustive x).mpr ⟨s, hp⟩
  · intro h x hx
    by_cases hA : A x
    · exact Or.inr ((h x hx).mp hA)
    · exact Or.inl (by simp [hχ, indicator, hA])

theorem positive_settled_exists {A : Set ℕ} (F : ComputableApproximation A)
    (χ : ℕ → ℕ) (hχ : ∀ x, χ x = indicator A x) (n : ℕ) :
    ∃ s, PositiveSettled F χ n s := by
  obtain ⟨s, hs⟩ := prefix_settled_exists A F.atStage
    (approximation_stages F).2.1 (approximation_stages F).2.2 n
  exact ⟨s, (positive_settled_iff F χ hχ n s).mpr hs⟩

noncomputable def deciderModulus {A : Set ℕ} (F : ComputableApproximation A)
    (χ : ℕ → ℕ) (hχ : ∀ x, χ x = indicator A x) (n : ℕ) : ℕ := by
  classical
  exact Nat.find (positive_settled_exists F χ hχ n)

theorem decider_modulus_correct {A : Set ℕ} (F : ComputableApproximation A)
    (χ : ℕ → ℕ) (hc : Computable χ) (hχ : ∀ x, χ x = indicator A x) :
    Computable (deciderModulus F χ hχ) ∧
      SettlingModulus A F.atStage (deciderModulus F χ hχ) ∧
      (∀ n s, PositiveSettled F χ n s → deciderModulus F χ hχ n ≤ s) ∧
      deciderModulus F χ hχ = leastSettlingStage F := by
  classical
  have hm (n : ℕ) : Settles A F.atStage n (deciderModulus F χ hχ n) :=
    (positive_settled_iff F χ hχ n _).mp
      (Nat.find_spec (positive_settled_exists F χ hχ n))
  have hmin (n s : ℕ) (hs : PositiveSettled F χ n s) : deciderModulus F χ hχ n ≤ s :=
    Nat.find_min' _ hs
  refine ⟨Computable.find (positive_settled_computable F χ hc)
    (positive_settled_exists F χ hχ), hm, hmin, ?_⟩
  funext n
  apply le_antisymm
  · exact hmin n _ ((positive_settled_iff F χ hχ n _).mpr ((least_settling_spec F).1 n))
  · exact (least_settling_spec F).2.1 n _ (hm n)

theorem computable_settling_equivalence {A : Set ℕ} (F : ComputableApproximation A) :
    ComputablePred A ↔ ∃ m, Computable m ∧ SettlingModulus A F.atStage m := by
  constructor
  · intro hc
    obtain ⟨χ, hcomp, hχ⟩ := (decidable_iff_characteristic A).mp hc
    obtain ⟨hmcomp, hm, _, _⟩ := decider_modulus_correct F χ hcomp hχ
    exact ⟨_, hmcomp, hm⟩
  · rintro ⟨m, hc, hm⟩
    exact (decidable_iff_characteristic A).mpr
      ⟨modulusDecider F m, modulus_decider_correct F m hc hm⟩

noncomputable def uniformHaltingTest (M : ℕ → ℕ → ℕ) (z : ℕ) : ℕ :=
  stageTest z.unpair.1 (M z.unpair.1 (z.unpair.2 + 1)) z.unpair.2

theorem uniform_halting_test_correct (M : ℕ → ℕ → ℕ) (hc : Computable₂ M)
    (hM : ∀ e, SettlingModulus (indexSet e) (stage e) (M e)) :
    Computable (uniformHaltingTest M) ∧
      ∀ z, uniformHaltingTest M z = indicator haltingPairs z := by
  classical
  have he : Computable (fun z : ℕ => z.unpair.1) := Computable.fst.comp Computable.unpair
  have hx : Computable (fun z : ℕ => z.unpair.2) := Computable.snd.comp Computable.unpair
  refine ⟨stage_test_primitive.to_comp.comp
    ((he.pair (hc.comp he (Computable.succ.comp hx))).pair hx), ?_⟩
  intro z
  have hz : z ∈ haltingPairs ↔
      z.unpair.2 ∈ stage z.unpair.1 (M z.unpair.1 (z.unpair.2 + 1)) :=
    hM z.unpair.1 (z.unpair.2 + 1) z.unpair.2 (Nat.lt_succ_self _)
  by_cases hhalt : haltingPairs z
  · have hp := (stage_test_spec z.unpair.1 (M z.unpair.1 (z.unpair.2 + 1)) z.unpair.2).2.mpr
      (hz.mp hhalt)
    simpa [uniformHaltingTest, indicator, hhalt] using hp
  · have hnot : stageTest z.unpair.1 (M z.unpair.1 (z.unpair.2 + 1)) z.unpair.2 ≠ 1 := by
      intro hp
      exact hhalt (hz.mpr ((stage_test_spec _ _ _).2.mp hp))
    have hz' := (stage_test_spec z.unpair.1 (M z.unpair.1 (z.unpair.2 + 1)) z.unpair.2).1.resolve_right hnot
    simpa [uniformHaltingTest, indicator, hhalt] using hz' 

theorem no_uniform_settling_modulus :
    ¬ ∃ M : ℕ → ℕ → ℕ, Computable₂ M ∧
      ∀ e, SettlingModulus (indexSet e) (stage e) (M e) := by
  rintro ⟨M, hc, hm⟩
  exact haltingPairs_undecidable ((decidable_iff_characteristic haltingPairs).mpr
    ⟨uniformHaltingTest M, uniform_halting_test_correct M hc hm⟩)

theorem finite_index_nonuniform_modulus (e : ℕ) (he : (indexSet e).Finite) :
    ComputablePred (indexSet e) ∧
      ∃ s, Computable (fun _ : ℕ => s) ∧
        SettlingModulus (indexSet e) (stage e) (fun _ => s) := by
  obtain ⟨s, hs⟩ := finite_global_stage (indexSet e) (stage e) (stage_monotone e) (stage_union e) he
  have hm : SettlingModulus (indexSet e) (stage e) (fun _ => s) := by
    intro n x hx
    rw [hs s le_rfl]
  have hcan : SettlingModulus (indexSet e) (canonicalApproximation e).atStage (fun _ => s) := by
    intro n x hx
    rw [(canonical_stages e s).2]
    exact hm n x hx
  exact ⟨(computable_settling_equivalence (canonicalApproximation e)).mpr
    ⟨fun _ => s, Computable.const s, hcan⟩, s, Computable.const s, hm⟩

end Lemmatheca.ComputabilityTheory.EffectiveEnumerations
