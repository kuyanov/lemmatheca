import Lemmatheca.UniversalComputation.UniversalComputation
import Lemmatheca.UniversalComputation.RecursiveFunctionConventions

/-! Effective self-reference in the corpus's fixed numerical program enumeration.
The fixed-point witness is explicitly `selfSpecialize q`, where `q` indexes the
auxiliary function described in the human proof. -/

namespace Lemmatheca.ComputabilityTheory.RecursionTheorem

open UniversalComputation

def SemanticFixedPoint (f : ℕ → ℕ) (e : ℕ) : Prop :=
  ∀ x, phi e x = phi (f e) x

def selfSpecialize (a : ℕ) : ℕ := specialize a a

theorem numerical_fixed_point_semantic {f : ℕ → ℕ} {e : ℕ}
    (h : Function.IsFixedPt f e) : SemanticFixedPoint f e := by
  intro x
  change f e = e at h
  rw [h]

theorem selfSpecialize_primitive : Primrec selfSpecialize := by
  exact specialize_primitive.comp Primrec.id Primrec.id

theorem selfSpecialize_eval (a x : ℕ) :
    phi (selfSpecialize a) x = phi a (Nat.pair a x) := by
  exact specialize_eval a a x

/-- Every index for the auxiliary function gives the specified fixed-point index. -/
theorem specified_fixed_point {g : ℕ → ℕ → Part ℕ} (q : ℕ)
    (hq : ∀ a x, phi q (Nat.pair a x) = g (selfSpecialize a) x) :
    ∀ x, phi (selfSpecialize q) x = g (selfSpecialize q) x := by
  intro x
  rw [selfSpecialize_eval]
  exact hq q x

/-- The existence statement retains the auxiliary index and the exact witness map. -/
theorem recursion_theorem {g : ℕ → ℕ → Part ℕ} (hg : Partrec₂ g) :
    ∃ q, (∀ a x, phi q (Nat.pair a x) = g (selfSpecialize a) x) ∧
      ∀ x, phi (selfSpecialize q) x = g (selfSpecialize q) x := by
  have hh : Partrec₂ (fun a x => g (selfSpecialize a) x) :=
    hg.comp (selfSpecialize_primitive.to_comp.comp Computable.fst) Computable.snd
  obtain ⟨q, hq⟩ := phi_complete (Partrec₂.unpaired'.mpr hh)
  have hq' : ∀ a x, phi q (Nat.pair a x) = g (selfSpecialize a) x := by
    intro a x
    simpa only [Nat.unpaired, Nat.unpair_pair] using congrFun hq (Nat.pair a x)
  exact ⟨q, hq', specified_fixed_point q hq'⟩

theorem transformer_fixed_point {f : ℕ → ℕ} (hf : Computable f) :
    ∃ e, SemanticFixedPoint f e := by
  have hg : Partrec₂ (fun e x => phi (f e) x) :=
    phi_recursive.comp (hf.comp Computable.fst) Computable.snd
  obtain ⟨q, _, he⟩ := recursion_theorem hg
  exact ⟨selfSpecialize q, he⟩

/-- The converse implication records the parameter map `e ↦ specialize q e`. -/
theorem transformer_to_recursion
    (H : ∀ f : ℕ → ℕ, Computable f → ∃ e, SemanticFixedPoint f e)
    {g : ℕ → ℕ → Part ℕ} (hg : Partrec₂ g) :
    ∃ q, (∀ a x, phi q (Nat.pair a x) = g a x) ∧
      Primrec (fun a => specialize q a) ∧
      ∃ e, SemanticFixedPoint (fun a => specialize q a) e ∧
        ∀ x, phi e x = g e x := by
  obtain ⟨q, hq⟩ := phi_complete (Partrec₂.unpaired'.mpr hg)
  have hq' : ∀ a x, phi q (Nat.pair a x) = g a x := by
    intro a x
    simpa only [Nat.unpaired, Nat.unpair_pair] using congrFun hq (Nat.pair a x)
  have hs : Primrec (fun a => specialize q a) :=
    specialize_primitive.comp (Primrec.const q) Primrec.id
  obtain ⟨e, he⟩ := H _ hs.to_comp
  refine ⟨q, hq', hs, e, he, ?_⟩
  intro x
  exact (he x).trans ((specialize_eval q e x).trans (hq' e x))

end Lemmatheca.ComputabilityTheory.RecursionTheorem
