import Lemmatheca.EffectiveEnumerations.Stages
import Lemmatheca.ComputablyInseparableSets.Separation

/-! Effective inseparability and exact reductions of disjoint enumerable pairs. -/
namespace Lemmatheca.ComputabilityTheory.EffectiveInseparability

open UniversalComputation EffectiveEnumerations ComputableSeparation

def EffectiveWitness (A B : Set ℕ) (p : ℕ → ℕ → ℕ) : Prop :=
  Computable₂ p ∧ ∀ u v, A ⊆ indexSet u → B ⊆ indexSet v →
    Disjoint (indexSet u) (indexSet v) → p u v ∉ indexSet u ∪ indexSet v

def EffectivelyInseparable (A B : Set ℕ) : Prop :=
  REPred A ∧ REPred B ∧ Disjoint A B ∧ ∃ p, EffectiveWitness A B p

theorem complement_nonempty {A B : Set ℕ} (h : EffectivelyInseparable A B) :
    ∃ z, z ∉ A ∪ B := by
  obtain ⟨a, ha⟩ := (enumerable_iff_index A).mp h.1
  obtain ⟨b, hb⟩ := (enumerable_iff_index B).mp h.2.1
  have hA : indexSet a = A := Set.ext fun x => (ha x).symm
  have hB : indexSet b = B := Set.ext fun x => (hb x).symm
  obtain ⟨p, hp⟩ := h.2.2.2
  have hout := hp.2 a b (by rw [hA]) (by rw [hB])
    (by simpa [hA, hB] using h.2.2.1)
  exact ⟨p a b, by simpa [hA, hB] using hout⟩

theorem ordinarily_inseparable {A B : Set ℕ} (h : EffectivelyInseparable A B) :
    ComputablyInseparable A B := by
  refine ⟨h.2.2.1, ?_⟩
  rintro ⟨C, hC, hsep⟩
  obtain ⟨u, hu⟩ := (enumerable_iff_index C).mp hC.to_re
  obtain ⟨v, hv⟩ := (enumerable_iff_index (fun x => x ∉ C)).mp hC.not.to_re
  have hU : indexSet u = C := Set.ext fun x => (hu x).symm
  have hV : indexSet v = Cᶜ := Set.ext fun x => (hv x).symm
  obtain ⟨p, hp⟩ := h.2.2.2
  have hsub : B ⊆ Cᶜ := fun _ hb hc => Set.disjoint_left.mp hsep.2 hc hb
  have hdis : Disjoint C Cᶜ := Set.disjoint_left.mpr fun _ hc hnc => hnc hc
  have hout := hp.2 u v (by simpa [hU] using hsep.1)
    (by simpa [hV] using hsub) (by simpa [hU, hV] using hdis)
  simp [hU, hV] at hout

def PairReduction (C D A B : Set ℕ) (f : ℕ → ℕ) : Prop :=
  Computable f ∧ (∀ x, x ∈ C ↔ f x ∈ A) ∧ ∀ x, x ∈ D ↔ f x ∈ B

def PairReducible (C D A B : Set ℕ) : Prop := ∃ f, PairReduction C D A B f

def UniversalPair (A B : Set ℕ) : Prop :=
  REPred A ∧ REPred B ∧ Disjoint A B ∧
    ∀ C D : Set ℕ, REPred C → REPred D → Disjoint C D → PairReducible C D A B

theorem reduction_preserves_outside {C D A B : Set ℕ} {f : ℕ → ℕ}
    (hf : PairReduction C D A B f) (x : ℕ) :
    x ∉ C ∪ D ↔ f x ∉ A ∪ B := by
  simp only [Set.mem_union, ← hf.2.1 x, ← hf.2.2 x]

end Lemmatheca.ComputabilityTheory.EffectiveInseparability
