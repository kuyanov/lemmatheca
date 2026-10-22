import Lemmatheca.ExistentiallyClosedExtensions.TransfinitePass

/-! The actual set-coded transfinite request pass and the outer countable union. -/
namespace Lemmatheca.ModelTheory.ExistentiallyClosedExtensions
open FirstOrder FirstOrder.Language
open Cardinal
open Lemmatheca.ModelTheory
open ModelCompleteness InductiveTheories
universe u v w
variable {L : Language.{u, v}}

/-- The completed pass has a supplied original-base map and a model in the same size bound. -/
structure Pass (T : L.Theory) (κ : Cardinal.{max u v w})
    (A : Theory.ModelType.{u, v, max u v w} T) where
  model : Theory.ModelType.{u, v, max u v w} T
  embedding : A ↪[L] model
  completed : IsCompletedPass T embedding
  card_le : #model ≤ κ

private theorem request_forward {M N P : Type (max u v w)}
    [L.Structure M] [L.Structure N] [L.Structure P]
    (r : Request L M) (f : M ↪[L] N) (g : N ↪[L] P) (h : r.Realized f) :
    r.Realized (g.comp f) := by
  have hp := r.existential.realize_embedding g h
  have hc : (g.comp f) ∘ r.parameters = g ∘ (f ∘ r.parameters) := rfl
  have he : g ∘ (default : Fin 0 → N) = (default : Fin 0 → P) := Subsingleton.elim _ _
  simpa only [Request.Realized, FirstOrder.Language.Formula.Realize, hc, he] using hp

/-- Extract the final model through precisely the composite initial isomorphism/stage map. -/
theorem pass_of_transfinite (T : L.Theory) (κ : Cardinal.{max u v w})
    (A : Theory.ModelType.{u, v, max u v w} T) (D : TransfinitePass T κ A) :
    ∃ P : Pass T κ A,
      ∃ e : P.model ≃[L] (D.stage (lastIndex D.length)).asModel,
        ∀ a, e (P.embedding a) =
          D.transition (firstIndex D.length) (lastIndex D.length) (by change (0 : Ordinal) ≤ D.length; exact zero_le) (D.initial a)  := by
  classical
  let : DirectedSystem (fun i => (D.stage i).asModel)
      (fun i j h => D.transition i j h) := D.system
  let z := firstIndex D.length
  let t := lastIndex D.length
  let base : A ↪[L] (D.stage t).asModel :=
    (D.transition z t (by change (0 : Ordinal) ≤ D.length; exact zero_le)).comp
      D.initial.toEmbedding
  have completed : IsCompletedPass T base := by
    intro r hr
    obtain ⟨i, hi⟩ := D.enumerates r
    let j : Set.Iic D.length := ⟨i.val, by change i.val ≤ D.length; exact le_of_lt i.property⟩
    let k : Set.Iic D.length := ⟨i.val + 1, by
      change i.val + 1 ≤ D.length
      exact Order.add_one_le_iff.mpr i.property⟩
    have zj : z ≤ j := by change (0 : Ordinal) ≤ i.val; exact zero_le
    have zk : z ≤ k := by change (0 : Ordinal) ≤ i.val + 1; exact zero_le
    have jt : j ≤ t := j.property
    have kt : k ≤ t := k.property
    have commj (a : A) : D.transition j t jt (D.transition z j zj (D.initial a)) = base a :=
      FirstOrder.Language.DirectedSystem.map_map (fun i j h => D.transition i j h) zj jt _
    have commk (a : A) : D.transition k t kt (D.transition z k zk (D.initial a)) = base a :=
      FirstOrder.Language.DirectedSystem.map_map (fun i j h => D.transition i j h) zk kt _
    have possible : (D.request i).Possible T ((D.transition z j zj).comp D.initial.toEmbedding) := by
      obtain ⟨N, f, hf⟩ := hr
      refine ⟨N, f.comp (D.transition j t jt), ?_⟩
      rw [hi]
      have heq : (f.comp (D.transition j t jt)).comp
          ((D.transition z j zj).comp D.initial.toEmbedding) = f.comp base := by
        ext a
        exact congrArg f (commj a)
      rw [heq]
      exact hf
    have hs := D.handled i possible
    rw [hi] at hs
    have hh := request_forward r ((D.transition z k zk).comp D.initial.toEmbedding)
      (D.transition k t kt) hs
    have heq : (D.transition k t kt).comp
        ((D.transition z k zk).comp D.initial.toEmbedding) = base := by
      ext a
      exact commk a
    rwa [heq] at hh
  let P : Pass T κ A := ⟨(D.stage t).asModel, base, completed, codedModel_card_le _ _ _⟩
  exact ⟨P, FirstOrder.Language.Equiv.refl L _, fun _ => rfl⟩

theorem exists_pass (T : L.Theory) (hT : IsInductive.{u, v, w} T)
    (κ : Cardinal.{max u v w}) (hω : Cardinal.aleph0 ≤ κ)
    (hL : Cardinal.lift (#L.Symbols) ≤ κ)
    (A : Theory.ModelType.{u, v, max u v w} T) (hA : #A ≤ κ) :
    Nonempty (Pass T κ A)  := by
  obtain ⟨D⟩ := exists_transfinite_pass T hT κ hω hL A hA
  obtain ⟨P, _⟩ := pass_of_transfinite T κ A D
  exact ⟨P⟩

/-- New parameters receive their own pass at the next outer stage. -/
structure PassChain (T : L.Theory) (κ : Cardinal.{max u v w})
    (M : Theory.ModelType.{u, v, max u v w} T) where
  stage : ℕ → Theory.ModelType.{u, v, max u v w} T
  initial : M ≃[L] stage 0
  successor : ∀ n, stage n ↪[L] stage (n + 1)
  completed : ∀ n, IsCompletedPass T (successor n)
  card_le : ∀ n, #(stage n) ≤ κ

namespace PassChain
variable {T : L.Theory} {κ : Cardinal.{max u v w}}
variable {M : Theory.ModelType.{u, v, max u v w} T}

/-- All unions use the original successor maps. -/
abbrev transition (D : PassChain T κ M) := DirectedSystem.natLERec D.successor

abbrev Limit (D : PassChain T κ M) :=
  FirstOrder.Language.DirectLimit (fun n => D.stage n) D.transition

instance limit_nonempty (D : PassChain T κ M) : Nonempty D.Limit :=
  Nonempty.map (DirectLimit.of L ℕ (fun n => D.stage n) D.transition 0) inferInstance

/-- The original supplied model is retained by its actual initial-stage map. -/
noncomputable def initialMap (D : PassChain T κ M) : M ↪[L] D.Limit :=
  (DirectLimit.of L ℕ (fun n => D.stage n) D.transition 0).comp D.initial.toEmbedding

theorem limit_models (D : PassChain T κ M) (hT : IsInductive.{u, v, w} T) : D.Limit ⊨ T := by
  exact inductive_implies_omega T hT D.stage D.successor

theorem limit_card_le (D : PassChain T κ M) (hω : Cardinal.aleph0 ≤ κ) : #D.Limit ≤ κ := by
  have hs : Function.Surjective (fun x : Σ n : ℕ, D.stage n =>
      DirectLimit.of L ℕ (fun n => D.stage n) D.transition x.1 x.2) := by
    intro x
    obtain ⟨n, a, h⟩ := DirectLimit.exists_of x
    exact ⟨⟨n, a⟩, h⟩
  calc
    #D.Limit ≤ #(Σ n : ℕ, D.stage n) := Cardinal.mk_le_of_surjective hs
    _ = Cardinal.sum (fun n : ℕ => #(D.stage n)) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : ℕ => κ) := Cardinal.sum_le_sum _ _ D.card_le
    _ = Cardinal.aleph0 * κ := by simp
    _ ≤ κ * κ := mul_le_mul' hω le_rfl
    _ = κ := Cardinal.mul_eq_self hω

/-- Any finite final parameter tuple occurs at a stage and is handled by that stage's next pass. -/
theorem limit_reflection (D : PassChain T κ M) (hT : IsInductive.{u, v, w} T)
    (N : Theory.ModelType.{u, v, max u v w} T) (f : D.Limit ↪[L] N) :
    ExistentiallyClosedEmbedding f := by
  classical
  have _hm := D.limit_models hT
  intro n φ hφ a ha
  choose idx elem hrep using fun i : Fin n => DirectLimit.exists_of (a i)
  let k := Finset.univ.sup idx
  have hik (i : Fin n) : idx i ≤ k := Finset.le_sup (Finset.mem_univ i)
  let c : Fin n → D.stage k := fun i => D.transition (idx i) k (hik i) (elem i)
  let j : ∀ t : ℕ, D.stage t ↪[L] D.Limit := fun t =>
    DirectLimit.of L ℕ (fun t => D.stage t) D.transition t
  have hc (i : Fin n) : j k (c i) = a i := by
    change DirectLimit.of L ℕ (fun t => D.stage t) D.transition k
      (D.transition (idx i) k (hik i) (elem i)) = a i
    rw [DirectLimit.of_f]
    exact hrep i
  have hsucc (x : D.stage k) : j (k+1) (D.successor k x) = j k x := by
    have he : D.transition k (k+1) (Nat.le_succ k) = D.successor k := by
      dsimp only [transition, DirectedSystem.natLERec]
      rw [Nat.leRecOn_succ (Nat.le_refl k), Nat.leRecOn_self]
      rfl
    rw [← he]
    exact DirectLimit.of_f (f := D.transition) (i := k) (j := k+1) (hij := Nat.le_succ k) (x := x)
  let r : Request L (D.stage k) := ⟨n, φ, hφ, c⟩
  have ht : (j (k+1)).comp (D.successor k) ∘ c = a := by
    funext i
    exact (hsucc (c i)).trans (hc i)
  have possible : r.Possible T (D.successor k) := by
    refine ⟨N, f.comp (j (k+1)), ?_⟩
    change φ.Realize ((((f.comp (j (k+1))).comp (D.successor k)) ∘ c))
    have he : ((f.comp (j (k+1))).comp (D.successor k)) ∘ c = f ∘ a := by
      funext i
      exact congrArg f (congrFun ht i)
    rwa [he]
  have hr := D.completed k r possible
  have hp := request_forward r (D.successor k) (j (k+1)) hr
  change φ.Realize ((j (k+1)).comp (D.successor k) ∘ c) at hp
  rwa [ht] at hp

@[instance_reducible]
noncomputable def limitModel (D : PassChain T κ M) (hT : IsInductive.{u, v, w} T) :
    Theory.ModelType.{u, v, max u v w} T where
  Carrier := D.Limit
  struc := inferInstance
  is_model := D.limit_models hT
  nonempty' := inferInstance

theorem limit_existentiallyClosed (D : PassChain T κ M) (hT : IsInductive.{u, v, w} T) :
    ExistentiallyClosedModel.{u, v, w} T (D.limitModel hT) := by
  intro N f
  exact D.limit_reflection hT N f
end PassChain

/-- The outer chain is also chosen from the bounded set of requests/models. -/
theorem exists_pass_chain (T : L.Theory) (hT : IsInductive.{u, v, w} T)
    (M : Theory.ModelType.{u, v, max u v w} T) : Nonempty (PassChain T (sizeBound L M) M) := by
  classical
  let κ : Cardinal.{max u v w} := sizeBound.{u, v, max u v w} L M
  have hω : Cardinal.aleph0 ≤ κ := le_max_left _ _
  have hL : Cardinal.lift.{w} (#L.Symbols) ≤ κ := by
    dsimp only [κ, sizeBound]
    rw [Cardinal.lift_umax.{max u v, w}, Cardinal.lift_id'.{max u v, w}]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hM : #M ≤ κ := by
    dsimp only [κ, sizeBound]
    rw [Cardinal.lift_id'.{max u v, w}]
    exact (le_max_right _ _).trans (le_max_right _ _)
  let State := {B : Theory.ModelType.{u, v, max u v w} T // #B ≤ κ}
  let R (B C : State) : Prop := ∃ f : B.val ↪[L] C.val, IsCompletedPass T f
  let initial : State := ⟨M, hM⟩
  have extend (B : State) : ∃ C : State, R B C := by
    obtain ⟨P⟩ := exists_pass T hT κ hω hL B.val B.property
    exact ⟨⟨P.model, P.card_le⟩, P.embedding, P.completed⟩
  obtain ⟨G, h0, hsucc⟩ : ∃ G : ℕ → State,
      G 0 = initial ∧ ∀ n, R (G n) (G (n+1)) := by
    let next : State → State := fun B => (extend B).choose
    have hnext (B : State) : R B (next B) := (extend B).choose_spec
    let seq : ℕ → State := Nat.rec initial (fun _ B => next B)
    exact ⟨seq, rfl, fun n => hnext (seq n)⟩
  choose f hf using hsucc
  refine ⟨{ stage := fun n => (G n).val
            initial := ?_
            successor := f
            completed := hf
            card_le := fun n => (G n).property }⟩
  have he : (G 0).val = M := congrArg Subtype.val h0
  rw [he]

/-- Full existence with the size bound for the supplied original model. -/
theorem exists_closed_extension (T : L.Theory) (hT : IsInductive.{u, v, w} T)
    (M : Theory.ModelType.{u, v, max u v w} T) :
    ∃ (D : PassChain T (sizeBound L M) M),
      ExistentiallyClosedModel.{u, v, w} T (D.limitModel hT) ∧
        #(D.limitModel hT) ≤ sizeBound L M := by
  obtain ⟨D⟩ := exists_pass_chain T hT M
  exact ⟨D, D.limit_existentiallyClosed hT, D.limit_card_le (le_max_left _ _)⟩

end Lemmatheca.ModelTheory.ExistentiallyClosedExtensions
