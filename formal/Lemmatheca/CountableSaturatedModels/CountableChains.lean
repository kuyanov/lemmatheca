import Lemmatheca.CountableSaturatedModels.SmallTheories
import Lemmatheca.ElementaryChains.ElementaryChains
import Lemmatheca.LargerModels.LargerModels

/-! Explicit inner request chains and outer saturating chains, with compatible union maps. -/
namespace Lemmatheca.ModelTheory.CountableSaturatedModels

open FirstOrder FirstOrder.Language
open Types

variable {L : Language.{0, 0}} {T : L.Theory}

/-- A sequence of countable nonempty models with specified elementary successor embeddings. -/
structure CountableChain (T : L.Theory) where
  stage : ℕ → T.ModelType.{0, 0, 0}
  countable_stage : ∀ s, Countable (stage s)
  successor : ∀ s, stage s ↪ₑ[L] stage (s + 1)

namespace CountableChain

/-- The specified composite of the successor maps. -/
def transition (D : CountableChain T) (i j : ℕ) (h : i ≤ j) : D.stage i ↪ₑ[L] D.stage j :=
  Nat.leRecOn h (fun {k} g => (D.successor k).comp g) (ElementaryEmbedding.refl L _)

instance transition_system (D : CountableChain T) :
    DirectedSystem (fun n => (D.stage n : Type)) (fun i j h => D.transition i j h) := by
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

/-- A countable elementary union retaining the exact prescribed stage maps. -/
structure Union (D : CountableChain T) where
  model : T.ModelType.{0, 0, 0}
  countable_model : Countable model
  inclusion : ∀ s, D.stage s ↪ₑ[L] model
  compatible : ∀ i j (h : i ≤ j) a, inclusion j (D.transition i j h a) = inclusion i a
  cover : ∀ a : model, ∃ s b, inclusion s b = a

theorem exists_union (D : CountableChain T) : Nonempty D.Union := by
  classical
  let G := fun n => (D.stage n : Type)
  let f := fun i j (h : i ≤ j) => D.transition i j h
  let b := fun i j (h : i ≤ j) => (f i j h).toEmbedding
  let : DirectedSystem G (fun i j h => b i j h) := by
    change DirectedSystem (fun n => (D.stage n : Type)) (fun i j h => D.transition i j h)
    infer_instance
  let K := FirstOrder.Language.DirectLimit G b
  let j : ∀ n, G n ↪ K := fun n =>
    (FirstOrder.Language.DirectLimit.of L ℕ G b n).toEmbedding
  have hcompat : ∀ i k (h : i ≤ k) a, j k (f i k h a) = j i a := by
    intro i k h a
    exact FirstOrder.Language.DirectLimit.of_f
  have hcover : ∀ a : K, ∃ s x, j s x = a :=
    FirstOrder.Language.DirectLimit.exists_of
  obtain ⟨S, hs⟩ := ElementaryChains.exists_elementary_union_structure G f j hcompat hcover
  let : L.Structure K := S
  choose e he using hs
  let : Nonempty K := ⟨j 0 (Classical.choice (inferInstance : Nonempty (G 0)))⟩
  let : K ⊨ T := ((e 0).theory_model_iff T).mp (D.stage 0).is_model
  have hc : Countable K := by
    let : ∀ n, Countable (G n) := D.countable_stage
    dsimp only [K, FirstOrder.Language.DirectLimit]
    infer_instance
  refine ⟨⟨Theory.ModelType.of T K, hc, e, ?_, ?_⟩⟩
  · intro i k h a
    exact (congrFun (he k) (D.transition i k h a)).trans
      ((hcompat i k h a).trans (congrFun (he i) a).symm)
  · intro a
    obtain ⟨s, x, hx⟩ := hcover a
    exact ⟨s, x, (congrFun (he s) x).trans hx⟩

theorem finite_stage (D : CountableChain T) (U : D.Union) (A : Finset U.model) :
    ∃ s, ∀ a ∈ A, ∃ b : D.stage s, U.inclusion s b = a := by
  classical
  choose s x hx using fun a : A => U.cover a.val
  let k := Finset.univ.sup s
  refine ⟨k, fun a ha => ?_⟩
  let a' : A := ⟨a, ha⟩
  let hle : s a' ≤ k := Finset.le_sup (Finset.mem_univ a')
  exact ⟨D.transition (s a') k hle (x a'), (U.compatible _ _ hle _).trans (hx a')⟩

end CountableChain

/-- One chosen old-base request is realized in a countable further elementary extension. -/
theorem one_request [Countable L.Symbols] {M N : Type}
    [L.Structure M] [L.Structure N] [Nonempty M] [Nonempty N]
    [M ⊨ T] [N ⊨ T] [Countable M] [Countable N]
    (f : M ↪ₑ[L] N) (A : Finset M)
    (p : (L[[(↑A : Set M)]].completeTheory M).CompleteType (Fin 1)) :
    ∃ P : T.ModelType.{0, 0, 0}, Countable P ∧
      ∃ g : N ↪ₑ[L] P, ∃ b : Fin 1 → P, RealizesThrough (g.comp f) p b := by
  classical
  let δ (φ : L[[(↑A : Set M)]].Formula (Fin 1)) : L.Formula (N ⊕ Fin 1) :=
    Formula.relabel (Sum.map f id) (parameterFormula (↑A : Set M) φ)
  let q := δ '' formulas p
  have hfinite : ∀ s : Finset (L.Formula (N ⊕ Fin 1)), (↑s : Set _) ⊆ q →
      ∃ b : Fin 1 → N, Realizes (↑s : Set (L.Formula (N ⊕ Fin 1))) (Sum.elim id b) := by
    intro s hs
    choose φ hφ hδ using fun ψ : s => hs ψ.property
    let t := s.attach.image φ
    have ht : (↑t : Set _) ⊆ formulas p := by
      intro η hη
      obtain ⟨ψ, _, rfl⟩ := Finset.mem_image.mp hη
      exact hφ ψ
    obtain ⟨a, ha⟩ := (partial_iff_finitelyRealized_completeTheory _).mp (partial_formulas p) t ht
    refine ⟨f ∘ a, fun ψ hψ => ?_⟩
    let ψ' : s := ⟨ψ, hψ⟩
    have hφa := ha (φ ψ') (Finset.mem_image.mpr ⟨ψ', Finset.mem_attach _ _, rfl⟩)
    have hM := (parameterFormula_realize (ElementaryEmbedding.refl L M) (↑A : Set M)
      (φ ψ') a).mpr hφa
    have hN := (f.map_formula (parameterFormula (↑A : Set M) (φ ψ'))
      (Sum.elim id a)).mpr hM
    have hctx : Sum.elim id (f ∘ a) ∘ Sum.map f id = f ∘ Sum.elim id a := by
      funext x
      cases x <;> rfl
    have hd : (δ (φ ψ')).Realize (Sum.elim id (f ∘ a)) := by
      change (Formula.relabel (Sum.map f id) (parameterFormula (↑A : Set M) (φ ψ'))).Realize _
      rw [Formula.realize_relabel, hctx]
      exact hN
    rw [hδ ψ'] at hd
    exact hd
  obtain ⟨P, SP, hP, g, b, hb⟩ := exists_elementary_realization q hfinite
  let := SP
  let := hP
  let : P ⊨ T := (g.theory_model_iff T).mp (inferInstance : N ⊨ T)
  have hp : RealizesThrough (g.comp f) p b := by
    intro φ hφ
    have hd := hb (δ φ) ⟨φ, hφ, rfl⟩
    change (Formula.relabel (Sum.map f id) (parameterFormula (↑A : Set M) φ)).Realize _ at hd
    rw [Formula.realize_relabel] at hd
    have hctx : Sum.elim g b ∘ Sum.map f id = Sum.elim (g.comp f) b := by
      funext x
      cases x <;> rfl
    rw [hctx] at hd
    exact (parameterFormula_realize (g.comp f) (↑A : Set M) φ b).mp hd
  obtain ⟨S, hS, hc⟩ := ElementarySubmodels.exists_countable_elementarySubstructure
    (L := L) (Set.range g ∪ Set.range b)
    ((Set.countable_range g).union (Set.countable_range b))
  let : Nonempty S := ⟨⟨g (Classical.choice (inferInstance : Nonempty N)),
    hS (Or.inl (Set.mem_range_self _))⟩⟩
  let : S ⊨ T := (S.subtype.theory_model_iff T).mpr (inferInstance : P ⊨ T)
  obtain ⟨g', hg'⟩ := LargerModels.restrict_elementary_range g S (fun _ h => hS (Or.inl h))
  let b' : Fin 1 → S := fun i => ⟨b i, hS (Or.inr (Set.mem_range_self i))⟩
  refine ⟨Theory.ModelType.of T S, hc, g', b', fun φ hφ => ?_⟩
  apply (parameterFormula_realize (g'.comp f) (↑A : Set M) φ b').mp
  have he := S.subtype.map_formula (parameterFormula (↑A : Set M) φ)
    (Sum.elim (g'.comp f) b')
  have hctx : S.subtype ∘ Sum.elim (g'.comp f) b' = Sum.elim (g.comp f) b := by
    funext x
    cases x with
    | inl x => exact hg' (f x)
    | inr i => rfl
  rw [hctx] at he
  exact he.mp ((parameterFormula_realize (g.comp f) (↑A : Set M) φ b).mpr (hp φ hφ))

/-- The inner chain starts with the given model and answers each fixed-base request in order. -/
structure RequestChain (M : T.ModelType.{0, 0, 0}) (R : ℕ → Request L M) where
  chain : CountableChain T
  initial : chain.stage 0 = M
  base : ∀ s, M ↪ₑ[L] chain.stage s
  base_zero : ∀ a : M, cast (congrArg Theory.ModelType.Carrier initial) (base 0 a) = a
  retained : ∀ s a, chain.successor s (base s a) = base (s + 1) a
  answered : ∀ s, ∃ b : Fin 1 → chain.stage (s + 1),
    RealizesThrough (base (s + 1)) (R s).2 b

theorem exists_requestChain [Countable L.Symbols] (_h : Small T)
    (M : T.ModelType.{0, 0, 0}) [Countable M] (R : ℕ → Request L M) :
    Nonempty (RequestChain M R) := by
  classical
  let State := Σ P : T.ModelType.{0, 0, 0}, {f : M ↪ₑ[L] P // Countable P}
  have next (s : ℕ) (z : State) :
      ∃ P : T.ModelType.{0, 0, 0}, Countable P ∧
        ∃ g : z.1 ↪ₑ[L] P, ∃ b : Fin 1 → P,
          RealizesThrough (g.comp z.2.val) (R s).2 b := by
    let := z.2.property
    exact one_request z.2.val (R s).1 (R s).2
  let P (s : ℕ) (z : State) := Classical.choose (next s z)
  have hc (s : ℕ) (z : State) : Countable (P s z) := (Classical.choose_spec (next s z)).1
  let g (s : ℕ) (z : State) : z.1 ↪ₑ[L] P s z :=
    Classical.choose (Classical.choose_spec (next s z)).2
  have hg (s : ℕ) (z : State) : ∃ b : Fin 1 → P s z,
      RealizesThrough ((g s z).comp z.2.val) (R s).2 b :=
    Classical.choose_spec (Classical.choose_spec (next s z)).2
  let step (s : ℕ) (z : State) : State :=
    ⟨P s z, ⟨(g s z).comp z.2.val, hc s z⟩⟩
  let states : ℕ → State := Nat.rec ⟨M, ⟨ElementaryEmbedding.refl L M, inferInstance⟩⟩ step
  let D : CountableChain T := {
    stage := fun s => (states s).1
    countable_stage := fun s => (states s).2.property
    successor := fun s => g s (states s) }
  exact ⟨⟨D, rfl, fun s => (states s).2.val, fun _ => rfl,
    fun _ _ => rfl, fun s => hg s (states s)⟩⟩

theorem requestChain_union {M : T.ModelType.{0, 0, 0}} {R : ℕ → Request L M}
    (D : RequestChain M R) (U : D.chain.Union) :
    ∀ s, ∃ b : Fin 1 → U.model,
      RealizesThrough ((U.inclusion 0).comp (D.base 0)) (R s).2 b := by
  have hbase (s : ℕ) (a : M) :
      D.chain.transition 0 s (Nat.zero_le s) (D.base 0 a) = D.base s a := by
    induction s with
    | zero => simp only [CountableChain.transition, Nat.leRecOn_self,
        ElementaryEmbedding.refl_apply]
    | succ s ih =>
        change D.chain.transition 0 (s + 1) (Nat.le.step (Nat.zero_le s)) (D.base 0 a) = _
        simp only [CountableChain.transition, Nat.leRecOn_succ (Nat.zero_le s),
          ElementaryEmbedding.comp_apply] at ⊢
        exact (congrArg (D.chain.successor s) ih).trans (D.retained s a)
  intro s
  obtain ⟨b, hb⟩ := D.answered s
  have h := realizesThrough_map (D.base (s + 1)) (U.inclusion (s + 1)) (R s).2 b hb
  have he : (U.inclusion (s + 1)).comp (D.base (s + 1)) =
      (U.inclusion 0).comp (D.base 0) := by
    ext a
    change U.inclusion (s + 1) (D.base (s + 1) a) = U.inclusion 0 (D.base 0 a)
    rw [← hbase (s + 1) a]
    exact U.compatible 0 (s + 1) (Nat.zero_le _) _
  exact ⟨U.inclusion (s + 1) ∘ b, he ▸ h⟩

theorem one_pass_extension [Countable L.Symbols] (h : Small T)
    (M : T.ModelType.{0, 0, 0}) [Countable M] :
    ∃ N : T.ModelType.{0, 0, 0}, Countable N ∧
      ∃ f : M ↪ₑ[L] N, RealizesAllOver f := by
  obtain ⟨R, hR⟩ := request_enumeration (M := M) h
  obtain ⟨D⟩ := exists_requestChain h M R
  obtain ⟨U⟩ := CountableChain.exists_union D.chain
  refine ⟨U.model, U.countable_model, (U.inclusion 0).comp (D.base 0), ?_⟩
  intro A p
  obtain ⟨s, hs⟩ := hR ⟨A, p⟩
  have hreal := requestChain_union D U s
  let H : Request L M → Prop := fun r => ∃ b : Fin 1 → U.model,
    RealizesThrough ((U.inclusion 0).comp (D.base 0)) r.2 b
  have hresult : H ⟨A, p⟩ := Eq.mp (congrArg H hs) hreal
  exact hresult

/-- Each outer successor completes one whole inner pass over its current parameter base. -/
theorem exists_saturatingChain [Countable L.Symbols] (h : Small T)
    (M : T.ModelType.{0, 0, 0}) [Countable M] :
    ∃ D : CountableChain T, D.stage 0 = M ∧ ∀ s, RealizesAllOver (D.successor s) := by
  classical
  let State := {P : T.ModelType.{0, 0, 0} // Countable P}
  have next (z : State) : ∃ P : T.ModelType.{0, 0, 0}, Countable P ∧
      ∃ f : z.val ↪ₑ[L] P, RealizesAllOver f := by
    let := z.property
    exact one_pass_extension h z.val
  let P (z : State) := Classical.choose (next z)
  have hc (z : State) : Countable (P z) := (Classical.choose_spec (next z)).1
  let f (z : State) : z.val ↪ₑ[L] P z :=
    Classical.choose (Classical.choose_spec (next z)).2
  have hf (z : State) : RealizesAllOver (f z) :=
    Classical.choose_spec (Classical.choose_spec (next z)).2
  let step (z : State) : State := ⟨P z, hc z⟩
  let states : ℕ → State := Nat.rec ⟨M, inferInstance⟩ (fun _ z => step z)
  let D : CountableChain T := {
    stage := fun s => (states s).val
    countable_stage := fun s => (states s).property
    successor := fun s => f (states s) }
  exact ⟨D, rfl, fun s => hf (states s)⟩

/-- Finite final parameter sets occur at a stage and are answered at the next outer stage. -/
theorem union_saturated (D : CountableChain T)
    (hD : ∀ s, RealizesAllOver (D.successor s)) (U : D.Union) :
    Saturation.OmegaSaturated L U.model := by
  classical
  have realize (A : Finset U.model)
      (p : (L[[(↑A : Set U.model)]].completeTheory U.model).CompleteType (Fin 1)) :
      ∃ b : Fin 1 → U.model, Realizes (formulas p) b := by
    obtain ⟨s, hs⟩ := D.finite_stage U A
    have hA : (↑A : Set U.model) ⊆ Set.range (U.inclusion s) := by
      intro a ha
      obtain ⟨b, hb⟩ := hs a ha
      exact ⟨b, hb⟩
    obtain ⟨B, _, q, hq⟩ := finite_type_pullback (U.inclusion s) A hA p
    obtain ⟨b, hb⟩ := hD s B q
    have hbU := realizesThrough_map (D.successor s) (U.inclusion (s + 1)) q b hb
    have he : (U.inclusion (s + 1)).comp (D.successor s) = U.inclusion s := by
      ext x
      have h := U.compatible s (s + 1) (Nat.le_succ s) x
      simpa only [CountableChain.transition, Nat.leRecOn_succ (le_refl s),
        Nat.leRecOn_self, ElementaryEmbedding.comp_apply, ElementaryEmbedding.refl_apply] using h
    refine ⟨U.inclusion (s + 1) ∘ b, (hq _).mp ?_⟩
    exact he ▸ hbU
  intro A hA
  have h := realize hA.toFinset
  rw [hA.coe_toFinset] at h
  exact h

end Lemmatheca.ModelTheory.CountableSaturatedModels
