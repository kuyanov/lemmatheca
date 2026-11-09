import Lemmatheca.ComputablyBoundedChanges.Basic
import Lemmatheca.FiniteMindChanges.BooleanExpressions

/-! The supplied approximation operations preserve computable input bounds. -/
namespace Lemmatheca.ComputabilityTheory.ComputablyBoundedChanges

open UniversalComputation LimitComputability DifferenceEnumerable FiniteMindChanges

set_option backward.isDefEq.respectTransparency false

theorem complement_bound (a : Approximation) (b : ℕ → ℕ)
    (hb : Binary a) (hz : StartsZero a) (hbound : ComputableBound a b) :
    ComputableBound (delayedComplement a) (fun x => b x + 1) := by
  refine ⟨Computable.succ.comp hbound.1, fun s x => ?_⟩
  cases s with
  | zero => simp only [changeCount]; omega
  | succ s =>
      rw [delayed_complement_count a hb hz]
      change 1 + changeCount a s x ≤ b x + 1
      have h := hbound.2 s x
      omega

theorem omega_complement (A : Set ℕ) (ha : OmegaCE A) : OmegaCE Aᶜ := by
  obtain ⟨a, b, hc, hb, hlim, hz, hbound⟩ := ha
  obtain ⟨hdc, hdb, hdz, hdlim⟩ := delayed_complement_data a A hc hb hlim
  exact ⟨delayedComplement a, fun x => b x + 1, hdc, hdb, hdlim, hdz,
    complement_bound a b hb hz hbound⟩

theorem preimage_bound (a : Approximation) (b f : ℕ → ℕ)
    (hbound : ComputableBound a b) (hf : Computable f) :
    ComputableBound (pullbackApproximation a f) (fun x => b (f x)) := by
  refine ⟨hbound.1.comp hf, fun s x => ?_⟩
  have he : changeCount (pullbackApproximation a f) s x = changeCount a s (f x) := by
    induction s with
    | zero => rfl
    | succ s ih => simp only [changeCount, pullbackApproximation, ih]
  rw [he]
  exact hbound.2 s (f x)

theorem omega_preimage (A : Set ℕ) (f : ℕ → ℕ)
    (ha : OmegaCE A) (hf : Computable f) : OmegaCE (f ⁻¹' A) := by
  obtain ⟨a, b, hc, hb, hlim, hz, hbound⟩ := ha
  obtain ⟨hpc, hpb, hpz, hplim, _⟩ := pullback_data a A f hc hb hlim hz hf
  exact ⟨pullbackApproximation a f, fun x => b (f x), hpc, hpb, hplim, hpz,
    preimage_bound a b f hbound hf⟩

theorem combination_bounds (a d : Approximation) (b c : ℕ → ℕ)
    (ha : ComputableBound a b) (hd : ComputableBound d c) :
    ComputableBound (unionApproximation a d) (fun x => b x + c x) ∧
      ComputableBound (intersectionApproximation a d) (fun x => b x + c x) := by
  have hcomp : Computable (fun x => b x + c x) :=
    Primrec.nat_add.to_comp.comp ha.1 hd.1
  constructor
  · refine ⟨hcomp, fun s x => ?_⟩
    exact (combination_count a d s x).1.trans (Nat.add_le_add (ha.2 s x) (hd.2 s x))
  · refine ⟨hcomp, fun s x => ?_⟩
    exact (combination_count a d s x).2.trans (Nat.add_le_add (ha.2 s x) (hd.2 s x))

theorem omega_combination (A B : Set ℕ) (ha : OmegaCE A) (hb : OmegaCE B) :
    OmegaCE (A ∪ B) ∧ OmegaCE (A ∩ B) := by
  obtain ⟨a, b, hac, hab, halim, haz, habound⟩ := ha
  obtain ⟨d, c, hdc, hdb, hdlim, hdz, hdbound⟩ := hb
  obtain ⟨⟨huc, hub, huz, hulim⟩, ⟨hic, hib, hiz, hilim⟩⟩ :=
    combination_data a d A B hac hdc hab hdb haz hdz halim hdlim
  obtain ⟨hubound, hibound⟩ := combination_bounds a d b c habound hdbound
  exact ⟨⟨unionApproximation a d, fun x => b x + c x, huc, hub, hulim, huz, hubound⟩,
    ⟨intersectionApproximation a d, fun x => b x + c x, hic, hib, hilim, hiz, hibound⟩⟩

theorem omega_boolean_expression (F : BooleanExpression) (U : ℕ → Set ℕ)
    (hu : ∀ i, OmegaCE (U i)) : OmegaCE (F.eval U) := by
  induction F with
  | atom i => exact hu i
  | compl F ih => exact omega_complement (F.eval U) ih
  | union F G ihF ihG => exact (omega_combination (F.eval U) (G.eval U) ihF ihG).1
  | inter F G ihF ihG => exact (omega_combination (F.eval U) (G.eval U) ihF ihG).2

end Lemmatheca.ComputabilityTheory.ComputablyBoundedChanges
