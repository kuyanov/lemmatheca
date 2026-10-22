import Lemmatheca.InductiveTheories.Syntax
import Lemmatheca.ElementaryChains.ElementaryChains

/-! Ordinary directed unions, without elementary hypotheses on the transition maps. -/
namespace Lemmatheca.ModelTheory.InductiveTheories
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory
universe u v w w' w''
variable {L : Language.{u, v}}

/-- Chain-union closure stated for actual function-closed carriers in an ambient structure.
The union is the native supremum substructure and every stage must be nonempty. -/
def IsInductive (T : L.Theory) : Prop :=
  ∀ (M : Theory.ModelType.{u, v, max u v w} (∅ : L.Theory))
    (C : Set (L.Substructure M)), C.Nonempty → IsChain (· ≤ ·) C →
    (∀ S ∈ C, Nonempty S ∧ S ⊨ T) → (sSup C : L.Substructure M) ⊨ T

/-- The analogous ordinary directed-union condition, on actual substructures. -/
def DirectedUnionClosed (T : L.Theory) : Prop :=
  ∀ (M : Theory.ModelType.{u, v, max u v w} (∅ : L.Theory))
    (C : Set (L.Substructure M)), C.Nonempty → DirectedOn (· ≤ ·) C →
    (∀ S ∈ C, Nonempty S ∧ S ⊨ T) → (sSup C : L.Substructure M) ⊨ T

/-- Abstract countable embedding sequences are equivalent to the literal-inclusion formulation. -/
def OmegaChainClosed (T : L.Theory) : Prop :=
  ∀ (G : ℕ → Theory.ModelType.{u, v, max u v w} T)
    (s : ∀ n, G n ↪[L] G (n + 1)),
    (FirstOrder.Language.DirectLimit (fun n => G n) (DirectedSystem.natLERec s)) ⊨ T

private theorem existential_relabel {α β : Type*} {m k : ℕ}
    {φ : L.BoundedFormula α k} (hφ : φ.IsExistential) (f : α → β ⊕ Fin m) :
    (φ.relabel f).IsExistential := by
  induction hφ with
  | of_isQF hq => exact (hq.relabel f).isExistential
  | ex _ ih => simpa only [BoundedFormula.relabel_ex] using ih.ex

private theorem prefix_relabel {α β : Type*} {m k : ℕ}
    {φ : L.BoundedFormula α k} (hφ : IsUniversalExistential φ) (f : α → β ⊕ Fin m) :
    IsUniversalExistential (φ.relabel f) := by
  induction hφ with
  | of_existential he => exact .of_existential (existential_relabel he f)
  | all _ ih => simpa only [BoundedFormula.relabel_all] using ih.all

private theorem sentence_relabel_realize (σ : L.Sentence) {M : Type w''} [L.Structure M]
    (v : Fin 0 → M) (xs : Fin 0 → M) :
    BoundedFormula.Realize (Formula.relabel (Empty.elim : Empty → Fin 0) σ) v xs ↔ M ⊨ σ := by
  have hxs : xs = default := Subsingleton.elim _ _
  subst xs
  change (Formula.relabel Empty.elim σ).Realize v ↔ M ⊨ σ
  rw [Formula.realize_relabel]
  have hv : v ∘ Empty.elim = (default : Empty → M) := Subsingleton.elim _ _
  rw [hv]
  rfl

section Directed
variable {I : Type w'} [Preorder I] [IsDirectedOrder I] [Nonempty I]
variable {G : I → Type w} [∀ i, L.Structure (G i)]
variable (f : ∀ i j, i ≤ j → G i ↪[L] G j)
variable [DirectedSystem G (fun i j h => f i j h)]

/-- Every finite tuple has representatives at one common stage, including the empty tuple. -/
theorem directed_union_tuple {n : ℕ} (a : Fin n → FirstOrder.Language.DirectLimit G f) :
    ∃ (i : I) (b : Fin n → G i), (DirectLimit.of L I G f i) ∘ b = a := by
  obtain ⟨i, b, hb⟩ := DirectLimit.exists_quotient_mk'_sigma_mk'_eq G f a
  exact ⟨i, b, hb.symm⟩

/-- Cofinal-tail truth of the actual shared-syntax prefix transfers to the directed limit. -/
theorem universalExistential_directed_union {r n : ℕ}
    {φ : L.BoundedFormula (Fin r) n} (hφ : IsUniversalExistential φ)
    (i : I) (v : Fin r → G i) (a : Fin n → G i)
    (h : ∀ j (hij : i ≤ j), φ.Realize (f i j hij ∘ v) (f i j hij ∘ a)) :
    φ.Realize (DirectLimit.of L I G f i ∘ v) (DirectLimit.of L I G f i ∘ a) := by
  induction hφ generalizing i with
  | @of_existential n φ he =>
    have hi := h i le_rfl
    have hv : f i i le_rfl ∘ v = v := funext fun x => FirstOrder.Language.DirectedSystem.map_self f (v x)
    have ha : f i i le_rfl ∘ a = a := funext fun x => FirstOrder.Language.DirectedSystem.map_self f (a x)
    rw [hv, ha] at hi
    exact he.realize_embedding (DirectLimit.of L I G f i) hi
  | @all n φ hp ih =>
    rw [BoundedFormula.realize_all]
    intro b
    obtain ⟨j, c, hc⟩ := DirectLimit.exists_of b
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    let d := f j k hjk c
    have hd : DirectLimit.of L I G f k d = b := (DirectLimit.of_f (f := f)).trans hc
    have hh (l : I) (hkl : k ≤ l) :
        φ.Realize (f k l hkl ∘ (f i k hik ∘ v))
          (f k l hkl ∘ Fin.snoc (f i k hik ∘ a) d) := by
      have ht := BoundedFormula.realize_all.mp (h l (hik.trans hkl)) (f k l hkl d)
      have hv : f k l hkl ∘ (f i k hik ∘ v) = f i l (hik.trans hkl) ∘ v := by
        funext x
        exact FirstOrder.Language.DirectedSystem.map_map f hik hkl (v x)
      have ha : f k l hkl ∘ Fin.snoc (f i k hik ∘ a) d =
          Fin.snoc (f i l (hik.trans hkl) ∘ a) (f k l hkl d) := by
        rw [Fin.comp_snoc]
        congr 1
        funext x
        exact FirstOrder.Language.DirectedSystem.map_map f hik hkl (a x)
      rwa [hv, ha]
    have ht := ih k (f i k hik ∘ v) (Fin.snoc (f i k hik ∘ a) d) hh
    have hv : DirectLimit.of L I G f k ∘ (f i k hik ∘ v) =
        DirectLimit.of L I G f i ∘ v := funext fun x => DirectLimit.of_f
    have ha : DirectLimit.of L I G f k ∘ Fin.snoc (f i k hik ∘ a) d =
        Fin.snoc (DirectLimit.of L I G f i ∘ a) b := by
      rw [Fin.comp_snoc, hd]
      congr 1
      funext x
      exact DirectLimit.of_f
    rwa [hv, ha] at ht

/-- Axioms with the prefix form hold in every ordinary directed union of their models. -/
theorem universalExistentialTheory_directed_union (T : L.Theory)
    (hT : IsUniversalExistentialTheory T) [∀ i, Nonempty (G i)]
    (hG : ∀ i, G i ⊨ T) : (FirstOrder.Language.DirectLimit G f) ⊨ T := by
  constructor
  intro σ hσ
  let i : I := Classical.choice inferInstance
  let τ : L.Formula (Fin 0) := Formula.relabel Empty.elim σ
  have hτ : IsUniversalExistential τ := prefix_relabel (hT σ hσ) (Sum.inl ∘ Empty.elim)
  have hr := universalExistential_directed_union f hτ i
    (Fin.elim0 : Fin 0 → G i) (Fin.elim0 : Fin 0 → G i) (by
      intro j hij
      exact (sentence_relabel_realize σ _ _).mpr ((hG j).realize_of_mem σ hσ))
  exact (sentence_relabel_realize σ (DirectLimit.of L I G f i ∘ Fin.elim0)
    (DirectLimit.of L I G f i ∘ Fin.elim0)).mp hr

end Directed

private theorem equivalent_models {T U : L.Theory} (h : Theories.Equivalent T U)
    (A : Type w'') [L.Structure A] [Nonempty A] : A ⊨ T ↔ A ⊨ U := by
  rw [← Theories.model_closure T A, (Theories.equivalent_iff_closure_eq T U).mp h,
    Theories.model_closure U A]

/-- Reaxiomatization also gives preservation for arbitrary index/model universe levels. -/
theorem axiomatization_directed_union (T : L.Theory)
    (hT : HasUniversalExistentialAxiomatization T)
    {I : Type w'} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (G : I → Type w) [∀ i, L.Structure (G i)] [∀ i, Nonempty (G i)]
    (f : ∀ i j, i ≤ j → G i ↪[L] G j) [DirectedSystem G (fun i j h => f i j h)]
    (hG : ∀ i, G i ⊨ T) : (FirstOrder.Language.DirectLimit G f) ⊨ T := by
  obtain ⟨U, hU, hTU⟩ := hT
  let : Nonempty (FirstOrder.Language.DirectLimit G f) :=
    Nonempty.map (DirectLimit.of L I G f (Classical.choice inferInstance)) inferInstance
  exact (equivalent_models hTU _).mpr (universalExistentialTheory_directed_union f U hU
    (fun i => (equivalent_models hTU (G i)).mp (hG i)))

private theorem omega_of_literal (T : L.Theory)
    (h : ∀ (M : Theory.ModelType.{u, v, max u v w} (∅ : L.Theory))
      (C : ElementaryChains.IncreasingChain L M),
      (∀ n, C.stage n ⊨ T) → C.unionSubstructure ⊨ T) : OmegaChainClosed.{u, v, w} T := by
  classical
  intro G step
  let F := DirectedSystem.natLERec step
  let D := FirstOrder.Language.DirectLimit (fun n => G n) F
  let j := fun n => DirectLimit.of L ℕ (fun n => G n) F n
  let : Nonempty D := Nonempty.map (j 0) inferInstance
  have hj (n : ℕ) (a : G n) : j (n + 1) (step n a) = j n a := by
    have hF : F n (n + 1) (Nat.le_succ n) = step n := by
      dsimp only [F, DirectedSystem.natLERec]
      rw [Nat.leRecOn_succ (Nat.le_refl n), Nat.leRecOn_self]
      rfl
    have hh := DirectLimit.of_f (f := F) (i := n) (j := n + 1)
      (hij := Nat.le_succ n) (x := a)
    change j (n + 1) (F n (n + 1) (Nat.le_succ n) a) = j n a at hh
    rwa [hF] at hh
  let R := fun n => (j n).toHom.range
  have hR : Monotone R := by
    apply monotone_nat_of_le_succ
    intro n x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨step n a, hj n a⟩
  let C : ElementaryChains.IncreasingChain L D :=
    { stage := ⟨R, hR⟩
      nonempty_stage := fun n => by
        obtain ⟨a⟩ := (inferInstance : Nonempty (G n))
        exact ⟨j n a, a, rfl⟩ }
  have hm (n : ℕ) : C.stage n ⊨ T := StrongHomClass.theory_model (j n).equivRange
  have hu := h (Theory.ModelType.of ∅ D) C hm
  have heq : C.unionSubstructure = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, a, rfl⟩ := DirectLimit.exists_of x
    exact le_iSup C.stage n ⟨a, rfl⟩
  have hsurj : Function.Surjective C.unionSubstructure.subtype := by
    intro x
    exact ⟨⟨x, by rw [heq]; trivial⟩, rfl⟩
  let e : C.unionSubstructure ≃[L] D :=
    { toEquiv := Equiv.ofBijective C.unionSubstructure.subtype
        ⟨C.unionSubstructure.subtype.injective, hsurj⟩
      map_fun' := C.unionSubstructure.subtype.map_fun'
      map_rel' := C.unionSubstructure.subtype.map_rel' }
  let : C.unionSubstructure ⊨ T := hu
  exact StrongHomClass.theory_model e

/-- The ambient native chain condition includes every abstract countable embedding sequence. -/
theorem inductive_implies_omega (T : L.Theory) (hT : IsInductive.{u, v, w} T) :
    OmegaChainClosed.{u, v, w} T := by
  apply omega_of_literal T
  intro M C hm
  have hmodel := hT M (Set.range C.stage) (Set.range_nonempty C.stage)
    C.stage.monotone.isChain_range (by
      rintro S ⟨n, rfl⟩
      exact ⟨inferInstance, hm n⟩)
  have heq : sSup (Set.range C.stage) = C.unionSubstructure := sSup_range
  let e : (sSup (Set.range C.stage) : L.Substructure M) ≃[L] C.unionSubstructure :=
    heq ▸ FirstOrder.Language.Equiv.refl L (sSup (Set.range C.stage) : L.Substructure M)
  let : (sSup (Set.range C.stage) : L.Substructure M) ⊨ T := hmodel
  exact StrongHomClass.theory_model e

/-- A directed family includes every nonempty chain as a special case. -/
theorem directed_implies_inductive (T : L.Theory)
    (hT : DirectedUnionClosed.{u, v, w} T) : IsInductive.{u, v, w} T := by
  intro M C hne hc hm
  exact hT M C hne hc.directedOn hm

/-- An equivalent universal-existential theory controls every literal directed union. -/
theorem axiomatization_implies_directed (T : L.Theory)
    (hT : HasUniversalExistentialAxiomatization T) : DirectedUnionClosed.{u, v, w} T := by
  classical
  intro M C hne hd hm
  let : Nonempty C := hne.to_subtype
  let : IsDirectedOrder C := ⟨fun a b => by
    obtain ⟨c, hc, ha, hb⟩ := hd a a.property b b.property
    exact ⟨⟨c, hc⟩, ha, hb⟩⟩
  let S : C →o L.Substructure M := ⟨Subtype.val, fun _ _ h => h⟩
  let (i : C) : Nonempty (S i) := (hm i i.property).1
  let F := fun i j (h : i ≤ j) => Substructure.inclusion (S.monotone h)
  have hD : (FirstOrder.Language.DirectLimit (fun i => S i) F) ⊨ T :=
    axiomatization_directed_union T hT (fun i => S i) F (fun i => (hm i i.property).2)
  let := hD
  have hu : (⨆ i, S i : L.Substructure M) ⊨ T :=
    StrongHomClass.theory_model (DirectLimit.Equiv_iSup S)
  have heq : (⨆ i, S i : L.Substructure M) = sSup C :=
    le_antisymm (iSup_le fun i => le_sSup i.property)
      (sSup_le fun i hi => le_iSup S ⟨i, hi⟩)
  rwa [heq] at hu

/-- The literal increasing-chain formulation agrees with the abstract countable condition. -/
theorem omega_closed_iff_literal (T : L.Theory) :
    OmegaChainClosed.{u, v, w} T ↔
      ∀ (M : Theory.ModelType.{u, v, max u v w} (∅ : L.Theory))
        (C : ElementaryChains.IncreasingChain L M),
        (∀ n, C.stage n ⊨ T) → C.unionSubstructure ⊨ T := by
  constructor
  · intro h M C hm
    let G : ℕ → Theory.ModelType.{u, v, max u v w} T := fun n =>
      { Carrier := C.stage n
        struc := inferInstance
        is_model := hm n
        nonempty' := inferInstance }
    let step := fun n => C.inclusion n (n + 1) (Nat.le_succ n)
    let F := DirectedSystem.natLERec step
    have hv (i j : ℕ) (hij : i ≤ j) (x : G i) :
        ((F i j hij x : C.stage j) : M) = ((x : C.stage i) : M) := by
      induction j, hij using Nat.le_induction with
      | base =>
        dsimp only [F, DirectedSystem.natLERec]
        rw [Nat.leRecOn_self]
        rfl
      | succ j hij ih =>
        dsimp only [F, DirectedSystem.natLERec]
        rw [Nat.leRecOn_succ hij]
        exact ih
    let map := FirstOrder.Language.DirectLimit.lift L ℕ (fun n => G n) F
      (fun n => C.intoUnion n) (fun i j hij x => Subtype.ext (hv i j hij x))
    have hsurj : Function.Surjective map := by
      intro x
      obtain ⟨n, hn⟩ := (Substructure.mem_iSup_of_directed C.stage.monotone.directed_le).mp x.property
      refine ⟨DirectLimit.of L ℕ (fun n => G n) F n ⟨(x : M), hn⟩, ?_⟩
      rw [DirectLimit.lift_of]
      rfl
    let e : FirstOrder.Language.DirectLimit (fun n => G n) F ≃[L] C.unionSubstructure :=
      { toEquiv := Equiv.ofBijective map ⟨map.injective, hsurj⟩
        map_fun' := map.map_fun'
        map_rel' := map.map_rel' }
    let := h G step
    exact StrongHomClass.theory_model e
  · exact omega_of_literal T

end Lemmatheca.ModelTheory.InductiveTheories
