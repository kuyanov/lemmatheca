import Lemmatheca.EffectiveInseparability.Simultaneous
import Lemmatheca.EffectiveInseparability.Preimages

/-! The specified escape transfer and universality reduction. -/
namespace Lemmatheca.ComputabilityTheory.EffectiveInseparability

open UniversalComputation EffectiveEnumerations ComputableSeparation ProductiveAndCreativeSets

def transferredWitness (f q : ℕ → ℕ) (p : ℕ → ℕ → ℕ) (u v : ℕ) : ℕ :=
  f (p (q u) (q v))

theorem transferred_witness_correct {C D A B : Set ℕ} {f : ℕ → ℕ}
    (hf : PairReduction C D A B f) {p : ℕ → ℕ → ℕ} (hp : EffectiveWitness C D p)
    (r : ℕ) (hr : PreimageIndex f r) :
    EffectiveWitness A B (transferredWitness f (preimageMap r) p) := by
  have hq := (preimage_map_primitive r).to_comp
  refine ⟨hf.1.comp (hp.1.comp (hq.comp Computable.fst) (hq.comp Computable.snd)), ?_⟩
  intro u v hA hB hdis
  have hC : C ⊆ indexSet (preimageMap r u) := by
    rw [preimage_map_domain f r hr u]
    exact fun x hx => hA ((hf.2.1 x).mp hx)
  have hD : D ⊆ indexSet (preimageMap r v) := by
    rw [preimage_map_domain f r hr v]
    exact fun x hx => hB ((hf.2.2 x).mp hx)
  have hpre : Disjoint (indexSet (preimageMap r u)) (indexSet (preimageMap r v)) := by
    rw [preimage_map_domain f r hr u, preimage_map_domain f r hr v]
    exact Set.disjoint_left.mpr fun _ hu hv => Set.disjoint_left.mp hdis hu hv
  have hout := hp.2 (preimageMap r u) (preimageMap r v) hC hD hpre
  intro hin
  rcases hin with hu | hv
  · exact hout (Or.inl (by rw [preimage_map_domain f r hr u]; exact hu))
  · exact hout (Or.inr (by rw [preimage_map_domain f r hr v]; exact hv))

theorem effective_upward {C D A B : Set ℕ} (hCD : EffectivelyInseparable C D)
    (hA : REPred A) (hB : REPred B) (hAB : Disjoint A B)
    (hred : PairReducible C D A B) : EffectivelyInseparable A B := by
  obtain ⟨f, hf⟩ := hred
  obtain ⟨p, hp⟩ := hCD.2.2.2
  obtain ⟨r, hr⟩ := preimage_index_exists hf.1
  exact ⟨hA, hB, hAB, transferredWitness f (preimageMap r) p,
    transferred_witness_correct hf hp r hr⟩

def collisionLeft (A D : Set ℕ) (p : ℕ → ℕ → ℕ) (u v x y : ℕ) : Prop :=
  y ∈ A ∨ (x ∈ D ∧ y = p u v)

def collisionRight (B C : Set ℕ) (p : ℕ → ℕ → ℕ) (u v x y : ℕ) : Prop :=
  y ∈ B ∨ (x ∈ C ∧ y = p u v)

def collisionMap (p : ℕ → ℕ → ℕ) (u v : ℕ → ℕ) (x : ℕ) : ℕ := p (u x) (v x)

private theorem re_or {α : Type*} [Primcodable α] {P Q : α → Prop}
    (hP : REPred P) (hQ : REPred Q) : REPred (fun x => P x ∨ Q x) := by
  obtain ⟨f, hf, he⟩ := Partrec.merge' hP hQ
  exact hf.dom_re.of_eq fun x => by
    simpa [Part.assert, Part.some] using (he x).2

private theorem re_and {α : Type*} [Primcodable α] {P Q : α → Prop}
    (hP : REPred P) (hQ : REPred Q) : REPred (fun x => P x ∧ Q x) := by
  have hf := hP.bind (hQ.comp Computable.fst).to₂
  exact hf.dom_re.of_eq fun x => by simp [Part.bind_dom, Part.assert, Part.some]

private theorem collision_jointly_re {A D : Set ℕ} {p : ℕ → ℕ → ℕ}
    (hA : REPred A) (hD : REPred D) (hp : Computable₂ p) :
    JointlyRE (collisionLeft A D p) := by
  have hy : Computable (fun t : ℕ × (ℕ × (ℕ × ℕ)) => t.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hx : Computable (fun t : ℕ × (ℕ × (ℕ × ℕ)) => t.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hv : Computable (fun t : ℕ × (ℕ × (ℕ × ℕ)) => t.2.1) :=
    Computable.fst.comp Computable.snd
  have heq : ComputablePred (fun t : ℕ × (ℕ × (ℕ × ℕ)) => t.2.2.2 = p t.1 t.2.1) :=
    (Primrec.eq.decide.to_comp.comp hy (hp.comp Computable.fst hv)).computablePred
  exact re_or (hA.comp hy) (re_and (hD.comp hx) heq.to_re)

theorem collision_relations_enumerable {A B C D : Set ℕ} {p : ℕ → ℕ → ℕ}
    (hA : REPred A) (hB : REPred B) (hC : REPred C) (hD : REPred D)
    (hp : Computable₂ p) :
    JointlyRE (collisionLeft A D p) ∧ JointlyRE (collisionRight B C p) := by
  exact ⟨collision_jointly_re hA hD hp, collision_jointly_re hB hC hp⟩

theorem collision_domain_identities (A B C D : Set ℕ) (p : ℕ → ℕ → ℕ)
    (u v : ℕ → ℕ)
    (huv : SimultaneousDomains (collisionLeft A D p) (collisionRight B C p) u v) :
    (∀ x, indexSet (u x) = A ∪ {y | x ∈ D ∧ y = collisionMap p u v x}) ∧
      ∀ x, indexSet (v x) = B ∪ {y | x ∈ C ∧ y = collisionMap p u v x} := by
  constructor
  · intro x
    rw [huv.1 x]
    ext y
    simp only [collisionLeft, collisionMap, Set.mem_ofPred_eq, Set.mem_union, and_comm]
  · intro x
    rw [huv.2 x]
    ext y
    simp only [collisionRight, collisionMap, Set.mem_ofPred_eq, Set.mem_union, and_comm]

theorem specified_universal_reduction {A B C D : Set ℕ} {p : ℕ → ℕ → ℕ}
    (hp : EffectiveWitness A B p) (hAB : Disjoint A B) (hCD : Disjoint C D)
    (u v : ℕ → ℕ) (hu : Computable u) (hv : Computable v)
    (huv : SimultaneousDomains (collisionLeft A D p) (collisionRight B C p) u v) :
    PairReduction C D A B (collisionMap p u v) := by
  classical
  obtain ⟨huv₀, huv₁⟩ := collision_domain_identities A B C D p u v huv
  have left (x : ℕ) (hx : x ∈ C) : collisionMap p u v x ∈ A := by
    have hnD : x ∉ D := fun hd => Set.disjoint_left.mp hCD hx hd
    have hU : indexSet (u x) = A := by simpa [hnD] using huv₀ x
    have hV : indexSet (v x) = B ∪ {collisionMap p u v x} := by simpa [hx] using huv₁ x
    by_contra hnot
    have hd : Disjoint (indexSet (u x)) (indexSet (v x)) := by
      rw [hU, hV]
      apply Set.disjoint_left.mpr
      intro y ha hy
      rcases hy with hb | hy
      · exact Set.disjoint_left.mp hAB ha hb
      · exact hnot ((Set.mem_singleton_iff.mp hy) ▸ ha)
    have hout := hp.2 (u x) (v x) (by rw [hU])
      (by rw [hV]; exact Set.subset_union_left) hd
    apply hout
    right
    rw [hV]
    exact Or.inr rfl
  have right (x : ℕ) (hx : x ∈ D) : collisionMap p u v x ∈ B := by
    have hnC : x ∉ C := fun hc => Set.disjoint_left.mp hCD hc hx
    have hU : indexSet (u x) = A ∪ {collisionMap p u v x} := by simpa [hx] using huv₀ x
    have hV : indexSet (v x) = B := by simpa [hnC] using huv₁ x
    by_contra hnot
    have hd : Disjoint (indexSet (u x)) (indexSet (v x)) := by
      rw [hU, hV]
      apply Set.disjoint_left.mpr
      intro y hy hb
      rcases hy with ha | hy
      · exact Set.disjoint_left.mp hAB ha hb
      · exact hnot ((Set.mem_singleton_iff.mp hy) ▸ hb)
    have hout := hp.2 (u x) (v x)
      (by rw [hU]; exact Set.subset_union_left) (by rw [hV]) hd
    apply hout
    left
    rw [hU]
    exact Or.inr rfl
  have outside (x : ℕ) (hc : x ∉ C) (hd : x ∉ D) : collisionMap p u v x ∉ A ∪ B := by
    have hU : indexSet (u x) = A := by simpa [hd] using huv₀ x
    have hV : indexSet (v x) = B := by simpa [hc] using huv₁ x
    have hout := hp.2 (u x) (v x)
      (by rw [hU]) (by rw [hV]) (by simpa only [hU, hV] using hAB)
    simpa only [hU, hV, collisionMap] using hout
  refine ⟨hp.1.comp hu hv, ?_, ?_⟩
  · intro x
    refine ⟨left x, ?_⟩
    intro ha
    by_contra hc
    by_cases hd : x ∈ D
    · exact Set.disjoint_left.mp hAB ha (right x hd)
    · exact outside x hc hd (Or.inl ha)
  · intro x
    refine ⟨right x, ?_⟩
    intro hb
    by_contra hd
    by_cases hc : x ∈ C
    · exact Set.disjoint_left.mp hAB (left x hc) hb
    · exact outside x hc hd (Or.inr hb)

theorem universal_reduction_exists {A B C D : Set ℕ} {p : ℕ → ℕ → ℕ}
    (hA : REPred A) (hB : REPred B) (hC : REPred C) (hD : REPred D)
    (hp : EffectiveWitness A B p) (hAB : Disjoint A B) (hCD : Disjoint C D) :
    ∃ u v : ℕ → ℕ, Primrec u ∧ Primrec v ∧
      SimultaneousDomains (collisionLeft A D p) (collisionRight B C p) u v ∧
      PairReduction C D A B (collisionMap p u v) := by
  obtain ⟨h₀, h₁⟩ := collision_relations_enumerable hA hB hC hD hp.1
  obtain ⟨h, _, hu, hv, huv⟩ := simultaneous_recursion _ _ h₀ h₁
  exact ⟨leftSelector h, rightSelector h, hu, hv, huv,
    specified_universal_reduction hp hAB hCD _ _ hu.to_comp hv.to_comp huv⟩

theorem effective_implies_universal {A B : Set ℕ} (h : EffectivelyInseparable A B) :
    UniversalPair A B := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro C D hC hD hCD
  obtain ⟨p, hp⟩ := h.2.2.2
  obtain ⟨u, v, _, _, _, hred⟩ := universal_reduction_exists h.1 h.2.1 hC hD hp h.2.2.1 hCD
  exact ⟨collisionMap p u v, hred⟩

theorem characterization {A B : Set ℕ} (hA : REPred A) (hB : REPred B)
    (hAB : Disjoint A B) :
    (EffectivelyInseparable A B ↔ UniversalPair A B) ∧
      (EffectivelyInseparable A B ↔ PairReducible (diagonalOutput 0) (diagonalOutput 1) A B) := by
  have backward : PairReducible (diagonalOutput 0) (diagonalOutput 1) A B →
      EffectivelyInseparable A B :=
    effective_upward diagonal_effective_pair hA hB hAB
  have diagonal (h : UniversalPair A B) :
      PairReducible (diagonalOutput 0) (diagonalOutput 1) A B :=
    h.2.2.2 _ _ (diagonalOutput_enumerable 0) (diagonalOutput_enumerable 1)
      (diagonalOutput_disjoint (by decide))
  exact ⟨⟨effective_implies_universal, fun h => backward (diagonal h)⟩,
    ⟨fun h => diagonal (effective_implies_universal h), backward⟩⟩

end Lemmatheca.ComputabilityTheory.EffectiveInseparability
