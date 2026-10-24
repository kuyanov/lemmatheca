import Lemmatheca.SaturatedExtensions.Simultaneous
import Lemmatheca.ElementaryChains.ElementaryChains

/-! Arbitrary elementary chains and the finite-parameter saturation argument. -/
namespace Lemmatheca.ModelTheory.SaturatedExtensions

open FirstOrder FirstOrder.Language
open Types CountableSaturatedModels

universe u v w w'

variable {L : Language.{u, v}}

/-- A countable sequence of nonempty structures with specified elementary successor maps. -/
structure Chain (L : Language.{u, v}) where
  stage : ℕ → Theory.ModelType.{u, v, w} (∅ : L.Theory)
  successor : ∀ n, stage n ↪ₑ[L] stage (n + 1)

namespace Chain

/-- The exact composite of the prescribed successor embeddings. -/
def transition (D : Chain.{u, v, w} L) (i j : ℕ) (h : i ≤ j) :
    D.stage i ↪ₑ[L] D.stage j :=
  Nat.leRecOn h (fun {k} g => (D.successor k).comp g) (ElementaryEmbedding.refl L _)

instance transition_system (D : Chain.{u, v, w} L) :
    DirectedSystem (fun n => (D.stage n : Type w)) (fun i j h => D.transition i j h) := by
  constructor
  · intro i a
    simp only [transition, Nat.leRecOn_self, ElementaryEmbedding.refl_apply]
  · intro k j i hij hjk a
    induction k, hjk using Nat.le_induction with
    | base => simp only [transition, Nat.leRecOn_self, ElementaryEmbedding.refl_apply]
    | succ k hjk ih =>
        change D.transition j (k + 1) (Nat.le.step hjk) (D.transition i j hij a) =
          D.transition i (k + 1) (Nat.le.step (hij.trans hjk)) a
        simp only [transition, Nat.leRecOn_succ hjk,
          Nat.leRecOn_succ (hij.trans hjk), ElementaryEmbedding.comp_apply]
        exact congrArg (D.successor k) ih

/-- A union retains the specified stage maps, their compatibility and their joint range. -/
structure Union (D : Chain.{u, v, w} L) where
  model : Theory.ModelType.{u, v, w} (∅ : L.Theory)
  inclusion : ∀ n, D.stage n ↪ₑ[L] model
  compatible : ∀ i j (h : i ≤ j) a, inclusion j (D.transition i j h a) = inclusion i a
  cover : ∀ a : model, ∃ n b, inclusion n b = a

/-- Elementary direct limits provide the stated compatible union, without size restrictions. -/
theorem exists_union (D : Chain.{u, v, w} L) : Nonempty D.Union := by
  classical
  let G := fun n => (D.stage n : Type w)
  let f := fun i j (h : i ≤ j) => D.transition i j h
  let b := fun i j (h : i ≤ j) => (f i j h).toEmbedding
  let : DirectedSystem G (fun i j h => b i j h) := by
    change DirectedSystem (fun n => (D.stage n : Type w)) (fun i j h => D.transition i j h)
    infer_instance
  let K := FirstOrder.Language.DirectLimit G b
  let j : ∀ n, G n ↪ K := fun n =>
    (FirstOrder.Language.DirectLimit.of L ℕ G b n).toEmbedding
  have hcompat : ∀ i k (h : i ≤ k) a, j k (f i k h a) = j i a := by
    intro i k h a
    exact FirstOrder.Language.DirectLimit.of_f
  have hcover : ∀ a : K, ∃ n x, j n x = a :=
    FirstOrder.Language.DirectLimit.exists_of
  obtain ⟨S, hs⟩ := ElementaryChains.exists_elementary_union_structure G f j hcompat hcover
  let : L.Structure K := S
  choose e he using hs
  let : Nonempty K := ⟨j 0 (Classical.choice (inferInstance : Nonempty (G 0)))⟩
  refine ⟨⟨Theory.ModelType.of (∅ : L.Theory) K, e, ?_, ?_⟩⟩
  · intro i k h a
    exact (congrFun (he k) (D.transition i k h a)).trans
      ((hcompat i k h a).trans (congrFun (he i) a).symm)
  · intro a
    obtain ⟨n, x, hx⟩ := hcover a
    exact ⟨n, x, (congrFun (he n) x).trans hx⟩

/-- Every finite parameter set in this union is contained in a single stage image. -/
theorem finite_stage (D : Chain.{u, v, w} L) (U : D.Union) (A : Finset U.model) :
    ∃ n, (↑A : Set U.model) ⊆ Set.range (U.inclusion n) := by
  classical
  choose n x hx using fun a : A => U.cover a.val
  let k := Finset.univ.sup n
  refine ⟨k, fun a ha => ?_⟩
  let a' : A := ⟨a, ha⟩
  let hle : n a' ≤ k := Finset.le_sup (Finset.mem_univ a')
  exact ⟨D.transition (n a') k hle (x a'), (U.compatible _ _ hle _).trans (hx a')⟩

/-- Named complete theories agree along the particular stage map. -/
theorem named_theory_agreement (D : Chain.{u, v, w} L) (U : D.Union)
    (n : ℕ) (A : Set (D.stage n)) :
    letI : L[[A]].Structure U.model := Diagrams.namedExpansion
      (fun a : A => U.inclusion n a)
    L[[A]].completeTheory (D.stage n) = L[[A]].completeTheory U.model := by
  let : L[[A]].Structure U.model := Diagrams.namedExpansion
    (fun a : A => U.inclusion n a)
  ext σ
  exact ((U.inclusion n).liftWithConstants A).map_sentence σ

end Chain

/-- A sequence of passes answers all finite-parameter requests at every successor. -/
def IsSequenceOfPasses (D : Chain.{u, v, w} L) : Prop :=
  ∀ n, RealizesAllOver (D.successor n)

/-- Recursive choice starts the chain with an isomorphic copy of this specified source. -/
theorem exists_sequence_of_passes {M : Type w} [L.Structure M] [Nonempty M] :
    ∃ D : Chain.{u, v, max u v w} L,
      Nonempty (M ≃[L] D.stage 0) ∧ IsSequenceOfPasses D := by
  classical
  let M₀ : Theory.ModelType.{u, v, max u v w} (∅ : L.Theory) :=
    (Theory.ModelType.of (∅ : L.Theory) M).equivInduced
      (Equiv.ulift.symm : M ≃ ULift.{max u v} M)
  let initial : M ≃[L] M₀ :=
    (Equiv.ulift.symm : M ≃ ULift.{max u v} M).inducedStructureEquiv
  let State := Theory.ModelType.{u, v, max u v w} (∅ : L.Theory)
  have next (P : State) : ∃ Q : State, ∃ f : P ↪ₑ[L] Q, RealizesAllOver f := by
    obtain ⟨Q, SQ, hQ, f, hf⟩ := one_pass_extension (L := L) (M := P)
    let := SQ
    let := hQ
    exact ⟨Theory.ModelType.of (∅ : L.Theory) Q, f, hf⟩
  let P (z : State) := Classical.choose (next z)
  let f (z : State) : z ↪ₑ[L] P z := Classical.choose (Classical.choose_spec (next z))
  have hf (z : State) : RealizesAllOver (f z) :=
    Classical.choose_spec (Classical.choose_spec (next z))
  let states : ℕ → State := Nat.rec M₀ (fun _ z => P z)
  let D : Chain.{u, v, max u v w} L :=
    { stage := states
      successor := fun n => f (states n) }
  exact ⟨D, ⟨initial⟩, fun n => hf (states n)⟩

/-- The finite-parameter type is answered at the following stage and retained in the union. -/
theorem union_saturated (D : Chain.{u, v, w} L)
    (hD : IsSequenceOfPasses D) (U : D.Union) :
    Saturation.OmegaSaturated L U.model := by
  classical
  have realize (A : Finset U.model)
      (p : (L[[(↑A : Set U.model)]].completeTheory U.model).CompleteType (Fin 1)) :
      ∃ b : Fin 1 → U.model, Realizes (formulas p) b := by
    obtain ⟨n, hA⟩ := D.finite_stage U A
    obtain ⟨B, _, q, hq⟩ := finite_type_pullback (U.inclusion n) A hA p
    obtain ⟨b, hb⟩ := hD n B q
    have hbU := realizesThrough_map (D.successor n) (U.inclusion (n + 1)) q b hb
    have he : (U.inclusion (n + 1)).comp (D.successor n) = U.inclusion n := by
      ext x
      have h := U.compatible n (n + 1) (Nat.le_succ n) x
      simpa only [Chain.transition, Nat.leRecOn_succ (le_refl n),
        Nat.leRecOn_self, ElementaryEmbedding.comp_apply, ElementaryEmbedding.refl_apply] using h
    refine ⟨U.inclusion (n + 1) ∘ b, (hq _).mp ?_⟩
    exact he ▸ hbU
  intro A hA
  have h := realize hA.toFinset
  rw [hA.coe_toFinset] at h
  exact h

/-- No countability or smallness assumption is needed to saturate the given source. -/
theorem saturated_extension {M : Type w} [L.Structure M] [Nonempty M] :
    ∃ (V : Type (max u v w)) (_ : L.Structure V) (_ : Nonempty V),
      Saturation.OmegaSaturated L V ∧ Nonempty (M ↪ₑ[L] V) := by
  obtain ⟨D, ⟨e⟩, hD⟩ := exists_sequence_of_passes (L := L) (M := M)
  obtain ⟨U⟩ := Chain.exists_union D
  exact ⟨U.model, inferInstance, inferInstance, union_saturated D hD U,
    ⟨(U.inclusion 0).comp e.toElementaryEmbedding⟩⟩

end Lemmatheca.ModelTheory.SaturatedExtensions
