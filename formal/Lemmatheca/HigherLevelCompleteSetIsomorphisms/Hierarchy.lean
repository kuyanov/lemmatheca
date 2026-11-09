import Lemmatheca.HigherLevelCompleteSetIsomorphisms.Matching
import Lemmatheca.PostsTheorem.Hierarchy

/-! Positive relative hierarchy levels, with ordinary maps and unchanged inverse pairs. -/
namespace Lemmatheca.ComputabilityTheory.HigherCompleteIsomorphism

open ArithmeticalHierarchy PostsTheorem TuringJump Myhill

noncomputable section
set_option backward.isDefEq.respectTransparency false

def PiComplete (B : Set ℕ) (n : ℕ) (H : Set ℕ) : Prop :=
  Pi B n H ∧ ∀ S : Set ℕ, Pi B n S → ManyOneReducible S H

theorem compose_pairs {S T U : Set ℕ} {P_S Q_S P_T Q_T : ℕ → ℕ}
    (hS : IsomorphismPair S U P_S Q_S) (hT : IsomorphismPair T U P_T Q_T) :
    IsomorphismPair S T (Q_T ∘ P_S) (Q_S ∘ P_T) := by
  rcases hS with ⟨hPS, hQS, hLS, hRS, hS⟩
  rcases hT with ⟨hPT, hQT, hLT, hRT, hT⟩
  refine ⟨hQT.comp hPS, hQS.comp hPT, ?_, ?_, ?_⟩
  · intro x
    change Q_S (P_T (Q_T (P_S x))) = x
    rw [hRT (P_S x), hLS x]
  · intro y
    change Q_T (P_S (Q_S (P_T y))) = y
    rw [hRS (P_T y), hLT y]
  · intro x
    have ht := hT (Q_T (P_S x))
    rw [hRT] at ht
    exact (hS x).trans ht.symm

theorem complement_pairs (S T : Set ℕ) (P Q : ℕ → ℕ) :
    IsomorphismPair S T P Q ↔ IsomorphismPair Sᶜ Tᶜ P Q := by
  classical
  constructor
  · rintro ⟨hP, hQ, hl, hr, hm⟩
    exact ⟨hP, hQ, hl, hr, fun x => not_congr (hm x)⟩
  · rintro ⟨hP, hQ, hl, hr, hm⟩
    refine ⟨hP, hQ, hl, hr, fun x => ?_⟩
    simpa only [Set.mem_compl_iff, not_not] using not_congr (hm x)

theorem pi_complete_iff_complement_sigma (B : Set ℕ) (n : ℕ) (hn : 0 < n) (H : Set ℕ) :
    PiComplete B n H ↔ SigmaComplete B n Hᶜ := by
  classical
  cases n with
  | zero => omega
  | succ n =>
      have dual (S : Set ℕ) : Pi B (n + 1) S ↔ Sigma B (n + 1) Sᶜ :=
        level_complement B (n + 1) false S
      have dual' (S : Set ℕ) : Sigma B (n + 1) S ↔ Pi B (n + 1) Sᶜ :=
        level_complement B (n + 1) true S
      constructor
      · rintro ⟨hH, hhard⟩
        refine ⟨(dual H).mp hH, fun S hS => ?_⟩
        obtain ⟨f, hf, he⟩ := hhard Sᶜ ((dual' S).mp hS)
        refine ⟨f, hf, fun x => ?_⟩
        change S x ↔ ¬H (f x)
        have hx : (¬S x) ↔ H (f x) := he x
        simpa only [not_not] using not_congr hx
      · rintro ⟨hH, hhard⟩
        refine ⟨(dual H).mpr hH, fun S hS => ?_⟩
        obtain ⟨f, hf, he⟩ := hhard Sᶜ ((dual S).mp hS)
        refine ⟨f, hf, fun x => ?_⟩
        have hx : (¬S x) ↔ ¬H (f x) := he x
        simpa only [not_not] using not_congr hx

theorem sigma_isomorphism (B : Set ℕ) (n : ℕ) (hn : 0 < n) (H : Set ℕ) :
    SigmaComplete B n H ↔ ComputablyIsomorphic H (iterate B n) := by
  cases n with
  | zero => omega
  | succ n =>
      exact (complete_iff_iterate B (n + 1) hn H).trans
        (jump_isomorphism_equivalence (iterate B n) H)

theorem sigma_class_maps {B H D : Set ℕ} {n : ℕ} (hn : 0 < n)
    (hH : SigmaComplete B n H) (hD : SigmaComplete B n D) :
    ∃ P_H Q_H P_D Q_D : ℕ → ℕ,
      IsomorphismPair H (iterate B n) P_H Q_H ∧
      IsomorphismPair D (iterate B n) P_D Q_D ∧
      IsomorphismPair H D (Q_D ∘ P_H) (Q_H ∘ P_D) := by
  obtain ⟨P_H, Q_H, hH⟩ := (pair_iff_isomorphic H (iterate B n)).mpr
    ((sigma_isomorphism B n hn H).mp hH)
  obtain ⟨P_D, Q_D, hD⟩ := (pair_iff_isomorphic D (iterate B n)).mpr
    ((sigma_isomorphism B n hn D).mp hD)
  exact ⟨P_H, Q_H, P_D, Q_D, hH, hD, compose_pairs hH hD⟩

theorem pi_isomorphism (B : Set ℕ) (n : ℕ) (hn : 0 < n) (H : Set ℕ) :
    PiComplete B n H ↔ ComputablyIsomorphic H (iterate B n)ᶜ := by
  rw [pi_complete_iff_complement_sigma B n hn H, sigma_isomorphism B n hn Hᶜ]
  constructor
  · intro h
    obtain ⟨P, Q, h⟩ := (pair_iff_isomorphic Hᶜ (iterate B n)).mpr h
    apply (pair_iff_isomorphic H (iterate B n)ᶜ).mp
    refine ⟨P, Q, ?_⟩
    simpa only [compl_compl] using (complement_pairs Hᶜ (iterate B n) P Q).mp h
  · intro h
    obtain ⟨P, Q, h⟩ := (pair_iff_isomorphic H (iterate B n)ᶜ).mpr h
    apply (pair_iff_isomorphic Hᶜ (iterate B n)).mp
    refine ⟨P, Q, ?_⟩
    simpa only [compl_compl] using (complement_pairs H (iterate B n)ᶜ P Q).mp h

theorem pi_complete_maps {B H : Set ℕ} {n : ℕ} (hn : 0 < n) (hH : PiComplete B n H) :
    ∃ P Q : ℕ → ℕ,
      IsomorphismPair Hᶜ (iterate B n) P Q ∧ IsomorphismPair H (iterate B n)ᶜ P Q := by
  have hs := (pi_complete_iff_complement_sigma B n hn H).mp hH
  obtain ⟨P, Q, hp⟩ := (pair_iff_isomorphic Hᶜ (iterate B n)).mpr
    ((sigma_isomorphism B n hn Hᶜ).mp hs)
  refine ⟨P, Q, hp, ?_⟩
  simpa only [compl_compl] using (complement_pairs Hᶜ (iterate B n) P Q).mp hp

theorem pi_class_maps {B H D : Set ℕ} {n : ℕ} (hn : 0 < n)
    (hH : PiComplete B n H) (hD : PiComplete B n D) :
    ∃ P_H Q_H P_D Q_D : ℕ → ℕ,
      IsomorphismPair H (iterate B n)ᶜ P_H Q_H ∧
      IsomorphismPair D (iterate B n)ᶜ P_D Q_D ∧
      IsomorphismPair H D (Q_D ∘ P_H) (Q_H ∘ P_D) := by
  obtain ⟨P_H, Q_H, _, hH⟩ := pi_complete_maps hn hH
  obtain ⟨P_D, Q_D, _, hD⟩ := pi_complete_maps hn hD
  exact ⟨P_H, Q_H, P_D, Q_D, hH, hD, compose_pairs hH hD⟩

theorem ordinary_classification (n : ℕ) (hn : 0 < n) (H : Set ℕ) :
    (SigmaComplete ∅ n H ↔ ComputablyIsomorphic H (iterate ∅ n)) ∧
      (PiComplete ∅ n H ↔ ComputablyIsomorphic H (iterate ∅ n)ᶜ) := by
  exact ⟨sigma_isomorphism ∅ n hn H, pi_isomorphism ∅ n hn H⟩

end
end Lemmatheca.ComputabilityTheory.HigherCompleteIsomorphism
