import Lemmatheca.ComputableReductions.ComputableReductions
import Lemmatheca.EffectiveEnumerations.Stages

/-! Effective escape in the corpus's existing numerical program numbering. -/
namespace Lemmatheca.ComputabilityTheory.ProductiveAndCreativeSets

open UniversalComputation EffectiveEnumerations

def ProductiveFunction (B : Set ℕ) (p : ℕ → ℕ) : Prop :=
  Computable p ∧ ∀ e, indexSet e ⊆ B → p e ∈ B \ indexSet e

def Productive (B : Set ℕ) : Prop := ∃ p, ProductiveFunction B p

def Creative (C : Set ℕ) : Prop := REPred C ∧ Productive Cᶜ

theorem empty_index_exists : ∃ e, indexSet e = ∅ := by
  obtain ⟨e, he⟩ := phi_complete Nat.Partrec.none
  refine ⟨e, ?_⟩
  ext x
  simp [indexSet, he]

theorem productive_nonempty {B : Set ℕ} (hB : Productive B) : B.Nonempty := by
  obtain ⟨p, hp⟩ := hB
  obtain ⟨e, he⟩ := empty_index_exists
  exact ⟨p e, (hp.2 e (by simp [he])).1⟩

theorem productive_not_enumerable {B : Set ℕ} (hB : Productive B) : ¬ REPred B := by
  rintro hce
  obtain ⟨p, hp⟩ := hB
  obtain ⟨e, he⟩ := (enumerable_iff_index B).mp hce
  have hEq : indexSet e = B := Set.ext (fun x => (he x).symm)
  obtain ⟨hin, hout⟩ := hp.2 e (by rw [hEq])
  exact hout (hEq.symm ▸ hin)

theorem productive_infinite {B : Set ℕ} (hB : Productive B) : B.Infinite := by
  classical
  intro hfinite
  let L : List ℕ := hfinite.toFinset.toList
  have htest : PrimrecPred (fun x : ℕ => ∃ a ∈ L, a = x) :=
    Primrec.eq.exists_mem_list.comp (Primrec.const L) Primrec.id
  apply productive_not_enumerable hB
  exact (htest.computablePred.of_eq (fun x => by simp [L]; rfl)).to_re

theorem creative_undecidable {C : Set ℕ} (hC : Creative C) : ¬ ComputablePred C := by
  intro hc
  exact productive_not_enumerable hC.2 hc.not.to_re

theorem diagonal_complement_identity : ProductiveFunction haltingDiagonalᶜ id := by
  refine ⟨Computable.id, ?_⟩
  intro e hsub
  have hn : e ∉ indexSet e := fun he => (hsub he) he
  exact ⟨hn, hn⟩

theorem diagonal_creative : Creative haltingDiagonal := by
  exact ⟨haltingDiagonal_enumerable, id, diagonal_complement_identity⟩

def constantRun (w _z : ℕ) : Part ℕ := phi w.unpair.1 w.unpair.2

def ConstantRunIndex (v : ℕ) : Prop :=
  ∀ w z, phi v (Nat.pair w z) = constantRun w z

def constantRunMap (v w : ℕ) : ℕ := specialize v w

theorem constant_run_partial : Partrec₂ constantRun := by
  exact phi_recursive.comp
    ((Computable.fst.comp Computable.unpair).comp Computable.fst)
    ((Computable.snd.comp Computable.unpair).comp Computable.fst)

theorem constant_run_index_exists : ∃ v, ConstantRunIndex v := by
  obtain ⟨v, hv⟩ := phi_complete (Partrec₂.unpaired'.mpr constant_run_partial)
  refine ⟨v, fun w z => ?_⟩
  simpa only [Nat.unpaired, Nat.unpair_pair] using congrFun hv (Nat.pair w z)

theorem constant_run_map_primitive (v : ℕ) : Primrec (constantRunMap v) := by
  exact specialize_primitive.comp (Primrec.const v) Primrec.id

theorem constant_run_eval (v : ℕ) (hv : ConstantRunIndex v) (e x z : ℕ) :
    phi (constantRunMap v (Nat.pair e x)) z = phi e x := by
  simpa only [constantRunMap, constantRun, Nat.unpair_pair] using
    (specialize_eval v (Nat.pair e x) z).trans (hv (Nat.pair e x) z)

theorem constant_run_reduction (v : ℕ) (hv : ConstantRunIndex v) :
    ∀ w, w ∈ haltingPairs ↔ constantRunMap v w ∈ haltingDiagonal := by
  intro w
  change (phi w.unpair.1 w.unpair.2).Dom ↔
    (phi (constantRunMap v w) (constantRunMap v w)).Dom
  have he := (specialize_eval v w (constantRunMap v w)).trans
    (hv w (constantRunMap v w))
  rw [show phi (constantRunMap v w) (constantRunMap v w) =
    phi w.unpair.1 w.unpair.2 from he]

theorem paired_to_diagonal : haltingPairs ≤₀ haltingDiagonal := by
  obtain ⟨v, hv⟩ := constant_run_index_exists
  exact ⟨constantRunMap v, (constant_run_map_primitive v).to_comp,
    constant_run_reduction v hv⟩

theorem diagonal_complete {A : ℕ → Prop} (hA : REPred A) : A ≤₀ haltingDiagonal := by
  exact (ComputableReductions.halting_complete hA).trans paired_to_diagonal

def preimageProgram (f : ℕ → ℕ) (e x : ℕ) : Part ℕ := phi e (f x)

def PreimageIndex (f : ℕ → ℕ) (a : ℕ) : Prop :=
  ∀ e x, phi a (Nat.pair e x) = preimageProgram f e x

def preimageMap (a e : ℕ) : ℕ := specialize a e

theorem preimage_program_partial {f : ℕ → ℕ} (hf : Computable f) :
    Partrec₂ (preimageProgram f) := by
  exact phi_recursive.comp Computable.fst (hf.comp Computable.snd)

theorem preimage_index_exists {f : ℕ → ℕ} (hf : Computable f) :
    ∃ a, PreimageIndex f a := by
  obtain ⟨a, ha⟩ := phi_complete (Partrec₂.unpaired'.mpr (preimage_program_partial hf))
  refine ⟨a, fun e x => ?_⟩
  simpa only [Nat.unpaired, Nat.unpair_pair] using congrFun ha (Nat.pair e x)

theorem preimage_map_primitive (a : ℕ) : Primrec (preimageMap a) := by
  exact specialize_primitive.comp (Primrec.const a) Primrec.id

theorem preimage_map_eval (f : ℕ → ℕ) (a : ℕ) (ha : PreimageIndex f a) (e x : ℕ) :
    phi (preimageMap a e) x = phi e (f x) := by
  exact (specialize_eval a e x).trans (ha e x)

theorem preimage_map_domain (f : ℕ → ℕ) (a : ℕ) (ha : PreimageIndex f a) (e : ℕ) :
    indexSet (preimageMap a e) = f ⁻¹' indexSet e := by
  ext x
  change (phi (preimageMap a e) x).Dom ↔ (phi e (f x)).Dom
  rw [preimage_map_eval f a ha e x]

def transferredEscape (f : ℕ → ℕ) (a e : ℕ) : ℕ := f (preimageMap a e)

theorem transferred_escape_productive {C : Set ℕ} {f : ℕ → ℕ}
    (hf : Computable f) (hred : ∀ x, x ∈ haltingDiagonal ↔ f x ∈ C)
    (a : ℕ) (ha : PreimageIndex f a) :
    ProductiveFunction Cᶜ (transferredEscape f a) := by
  refine ⟨hf.comp (preimage_map_primitive a).to_comp, ?_⟩
  intro e hsub
  have hpre : indexSet (preimageMap a e) ⊆ haltingDiagonalᶜ := by
    intro x hx hK
    have hfx : f x ∈ indexSet e := by
      rw [preimage_map_domain f a ha e] at hx
      exact hx
    exact hsub hfx ((hred x).mp hK)
  obtain ⟨hnK, hnW⟩ := diagonal_complement_identity.2 (preimageMap a e) hpre
  constructor
  · intro hc
    exact hnK ((hred _).mpr hc)
  · intro he
    apply hnW
    rw [preimage_map_domain f a ha e]
    exact he

theorem complete_implies_creative {C : Set ℕ} (hC : REPred C)
    (hred : haltingDiagonal ≤₀ C) : Creative C := by
  obtain ⟨f, hf, hred⟩ := hred
  obtain ⟨a, ha⟩ := preimage_index_exists hf
  exact ⟨hC, transferredEscape f a, transferred_escape_productive hf hred a ha⟩

end Lemmatheca.ComputabilityTheory.ProductiveAndCreativeSets
