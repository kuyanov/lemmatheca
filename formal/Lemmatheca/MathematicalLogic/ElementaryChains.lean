import Mathlib.ModelTheory.DirectLimit
import Mathlib.ModelTheory.ElementarySubstructures
import Mathlib.ModelTheory.Complexity
import Lemmatheca.MathematicalLogic.ChainUnion

/-! Increasing chains, their actual unions, and elementary stage inclusions.
The ambient structure formulation identifies the union with an iSup whose
carrier is exactly the set union. Mathlib's DirectLimit.Equiv_iSup supplies
the connection with the construction for abstract systems of structures.
All semantic claims use mathlib's shared first-order syntax.
-/

namespace Lemmatheca.MathematicalLogic.ElementaryChains

open FirstOrder FirstOrder.Language

universe u v w w'

/-- An increasing, nonempty sequence of substructures of one ambient structure. -/
structure IncreasingChain (L : Language.{u, v}) (M : Type w) [L.Structure M] where
  stage : ℕ →o L.Substructure M
  nonempty_stage : ∀ n, (stage n : Set M).Nonempty

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

namespace IncreasingChain

variable (C : IncreasingChain L M)

instance stage_nonempty (n : ℕ) : Nonempty (C.stage n) :=
  (C.nonempty_stage n).to_subtype

/-- The union substructure; its carrier is the literal union of the stage carriers. -/
def unionSubstructure : L.Substructure M := ⨆ n, C.stage n

instance union_nonempty : Nonempty C.unionSubstructure := by
  obtain ⟨x, hx⟩ := C.nonempty_stage 0
  exact ⟨⟨x, le_iSup C.stage 0 hx⟩⟩

/-- The specified inclusion between two stages. -/
def inclusion (i j : ℕ) (h : i ≤ j) : C.stage i ↪[L] C.stage j :=
  Substructure.inclusion (C.stage.monotone h)

/-- The specified inclusion of a stage into the union. -/
def intoUnion (i : ℕ) : C.stage i ↪[L] C.unionSubstructure :=
  Substructure.inclusion (le_iSup C.stage i)

/-- Elementarity concerns the actual inclusion maps, not arbitrary maps between stages. -/
def IsElementary : Prop :=
  ∀ i j (h : i ≤ j),
    ∃ e : C.stage i ↪ₑ[L] C.stage j,
      (e : C.stage i → C.stage j) = C.inclusion i j h

/-- Every finite tuple of union elements already belongs to a single stage. -/
theorem finite_tuple_stage {n : ℕ} (a : Fin n → C.unionSubstructure) :
    ∃ r, ∀ i, (a i : M) ∈ C.stage r := by
  classical
  have ha (i : Fin n) : ∃ r, (a i : M) ∈ C.stage r :=
    (Substructure.mem_iSup_of_directed C.stage.monotone.directed_le).mp (a i).property
  choose r hr using ha
  exact ⟨Finset.univ.sup r, fun i =>
    C.stage.monotone (Finset.le_sup (Finset.mem_univ i)) (hr i)⟩

/-- Adjacent elementary inclusions suffice for an elementary chain. -/
theorem isElementary_iff_successor :
    C.IsElementary ↔
      ∀ i, ∃ e : C.stage i ↪ₑ[L] C.stage (i + 1),
        (e : C.stage i → C.stage (i + 1)) = C.inclusion i (i + 1) (Nat.le_succ i) := by
  constructor
  · intro h i
    exact h i (i + 1) (Nat.le_succ i)
  · intro hs i j hij
    induction j, hij using Nat.le_induction with
    | base =>
      exact ⟨ElementaryEmbedding.refl L (C.stage i), rfl⟩
    | succ j hij ih =>
      obtain ⟨e, he⟩ := ih
      obtain ⟨f, hf⟩ := hs j
      refine ⟨f.comp e, ?_⟩
      funext a
      change f (e a) = _
      rw [he, hf]
      rfl

private theorem boundedFormula_union (hC : C.IsElementary) {α : Type*} {n : ℕ}
    (φ : L.BoundedFormula α n) :
    ∀ (i : ℕ) (v : α → C.stage i) (xs : Fin n → C.stage i),
      φ.Realize (C.intoUnion i ∘ v) (C.intoUnion i ∘ xs) ↔ φ.Realize v xs := by
  induction φ with
  | falsum =>
    intros
    rfl
  | equal t s =>
    intros
    exact (BoundedFormula.IsAtomic.equal t s).isQF.realize_embedding _
  | rel R ts =>
    intros
    exact (BoundedFormula.IsAtomic.rel R ts).isQF.realize_embedding _
  | imp φ ψ ihφ ihψ =>
    intro i v xs
    exact imp_congr (ihφ i v xs) (ihψ i v xs)
  | @all n φ ih =>
    intro i v xs
    simp only [BoundedFormula.realize_all]
    constructor
    · intro h a
      apply (ih i v (Fin.snoc xs a)).mp
      simpa only [Fin.comp_snoc] using h (C.intoUnion i a)
    · intro h a
      obtain ⟨j, hj⟩ :=
        (Substructure.mem_iSup_of_directed C.stage.monotone.directed_le).mp a.property
      let r := max i j
      let b : C.stage r := ⟨(a : M), C.stage.monotone (le_max_right i j) hj⟩
      obtain ⟨e, he⟩ := hC i r (le_max_left i j)
      have hm : φ.all.Realize (e ∘ v) (e ∘ xs) :=
        (e.map_boundedFormula φ.all v xs).mpr h
      have hb := BoundedFormula.realize_all.mp hm b
      have hu := (ih r (e ∘ v) (Fin.snoc (e ∘ xs) b)).mpr hb
      have hv : C.intoUnion r ∘ (e ∘ v) = C.intoUnion i ∘ v := by
        funext x
        rw [he]
        rfl
      have hx : C.intoUnion r ∘ Fin.snoc (e ∘ xs) b =
          Fin.snoc (C.intoUnion i ∘ xs) a := by
        rw [Fin.comp_snoc]
        congr 1
        · funext x
          rw [he]
          rfl
      rw [hv, hx] at hu
      exact hu

/-- The actual stage-to-union inclusion is elementary. -/
theorem elementary_union (hC : C.IsElementary) (i : ℕ) :
    ∃ e : C.stage i ↪ₑ[L] C.unionSubstructure,
      (e : C.stage i → C.unionSubstructure) = C.intoUnion i := by
  refine ⟨⟨C.intoUnion i, ?_⟩, rfl⟩
  intro n φ a
  simpa only [Formula.Realize, Subsingleton.elim
    (C.intoUnion i ∘ (default : Fin 0 → C.stage i)) default] using
    C.boundedFormula_union hC φ i a default

/-- Compatibility with every stage uniquely determines the structure on the union carrier. -/
theorem union_structure_unique
    (S : L.Structure C.unionSubstructure)
    (hS : ∀ i, ∃ e : @Language.Embedding L (C.stage i) C.unionSubstructure
        (Substructure.inducedStructure) S,
      (e : C.stage i → C.unionSubstructure) = C.intoUnion i) :
    S = (inferInstance : L.Structure C.unionSubstructure) := by
  apply Language.Structure.ext
  · funext n f a
    obtain ⟨i, hi⟩ := C.finite_tuple_stage a
    let a' : Fin n → C.stage i := fun k => ⟨(a k : M), hi k⟩
    have ha : C.intoUnion i ∘ a' = a := by
      funext k
      exact Subtype.ext rfl
    obtain ⟨e, he⟩ := hS i
    have hs := @Embedding.map_fun L (C.stage i) C.unionSubstructure
      _ S e n f a'
    rw [he, ha] at hs
  · funext n R a
    obtain ⟨i, hi⟩ := C.finite_tuple_stage a
    let a' : Fin n → C.stage i := fun k => ⟨(a k : M), hi k⟩
    have ha : C.intoUnion i ∘ a' = a := by
      funext k
      exact Subtype.ext rfl
    obtain ⟨e, he⟩ := hS i
    have hs := @Embedding.map_rel L (C.stage i) C.unionSubstructure
      _ S e n R a'
    rw [he, ha] at hs

end IncreasingChain

/-- An arbitrary elementary system puts a structure on its unstructured union
carrier for which the original specified maps themselves are elementary. -/
theorem exists_elementary_union_structure {L : Language.{u, v}} (G : ℕ → Type w)
    [∀ n, L.Structure (G n)] [∀ n, Nonempty (G n)]
    (f : ∀ i j, i ≤ j → G i ↪ₑ[L] G j)
    [DirectedSystem G (fun i j h => f i j h)] {U : Type w'}
    (j : ∀ n, G n ↪ U)
    (hcompat : ∀ a b (h : a ≤ b) x, j b (f a b h x) = j a x)
    (hcover : ∀ x : U, ∃ n a, j n a = x) :
    ∃ S : L.Structure U, ∀ n,
      ∃ e : @Language.ElementaryEmbedding L (G n) U
          (inferInstance : L.Structure (G n)) S,
        (e : G n → U) = j n := by
  classical
  have : DirectedSystem G (fun a b h => (f a b h).toEmbedding) := by
    change DirectedSystem G (fun a b h => f a b h)
    infer_instance
  obtain ⟨S, hs⟩ := exists_union_structure G (fun a b h => (f a b h).toEmbedding)
    j hcompat hcover
  let : L.Structure U := S
  choose e he using hs
  have hecompat (a b : ℕ) (h : a ≤ b) (x : G a) :
      e b (f a b h x) = e a x := by
    rw [he a, he b]
    exact hcompat a b h x
  let R : ℕ → L.Substructure U := fun n => (e n).toHom.range
  have hR : Monotone R := by
    intro a b hab x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨f a b hab y, hecompat a b hab y⟩
  let C : IncreasingChain L U :=
    { stage := ⟨R, hR⟩
      nonempty_stage := fun n => by
        obtain ⟨x⟩ := (inferInstance : Nonempty (G n))
        exact ⟨e n x, x, rfl⟩ }
  have hC : C.IsElementary := by
    intro a b hab
    let g : C.stage a ↪ₑ[L] C.stage b :=
      (e b).equivRange.toElementaryEmbedding.comp
        ((f a b hab).comp (e a).equivRange.symm.toElementaryEmbedding)
    refine ⟨g, ?_⟩
    funext x
    apply Subtype.ext
    change e b (f a b hab ((e a).equivRange.symm x)) = (x : U)
    rw [hecompat a b hab]
    exact congrArg Subtype.val ((e a).equivRange.apply_symm_apply x)
  have htop : C.unionSubstructure = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, a, rfl⟩ := hcover x
    exact le_iSup C.stage n ⟨a, congrFun (he n) a⟩
  have hsurj : Function.Surjective C.unionSubstructure.subtype := by
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [htop]
    trivial
  let E : C.unionSubstructure ≃[L] U :=
    { toEquiv := Equiv.ofBijective C.unionSubstructure.subtype
        ⟨C.unionSubstructure.subtype.injective, hsurj⟩
      map_fun' := C.unionSubstructure.subtype.map_fun'
      map_rel' := C.unionSubstructure.subtype.map_rel' }
  refine ⟨S, fun n => ?_⟩
  obtain ⟨hn, hhn⟩ := C.elementary_union hC n
  refine ⟨E.toElementaryEmbedding.comp
    (hn.comp (e n).equivRange.toElementaryEmbedding), ?_⟩
  funext a
  change (hn ((e n).equivRange a) : U) = j n a
  rw [hhn]
  exact congrFun (he n) a

end Lemmatheca.MathematicalLogic.ElementaryChains
