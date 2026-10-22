import Lemmatheca.InductiveTheories.Unions
import Lemmatheca.InductiveTheories.Factorization
import Lemmatheca.InductiveTheories.UniversalDiagrams

/-! The two compactness diagrams, retaining the supplied maps. -/
namespace Lemmatheca.ModelTheory.InductiveTheories
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory
open Lemmatheca.ModelTheory.ModelCompleteness
universe u v w w'
variable {L : Language.{u, v}}

private theorem elementary_from_cofinal_sequence
    (G : ℕ → Type (max u v w)) [∀ n, L.Structure (G n)] [∀ n, Nonempty (G n)]
    {C : Type (max u v w)} [L.Structure C]
    (j : ∀ n, G n ↪[L] C) (step : ∀ n, G n ↪ₑ[L] G (n + 1))
    (comm : ∀ n a, j (n + 1) (step n a) = j n a)
    (cover : ∀ x : C, ∃ n a, j n a = x) :
    ∀ n, ∃ e : G n ↪ₑ[L] C, (e : G n → C) = j n := by
  classical
  let R : ℕ → L.Substructure C := fun n => (j n).toHom.range
  have hR : Monotone R := by
    apply monotone_nat_of_le_succ
    intro n x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨step n a, comm n a⟩
  let S : ElementaryChains.IncreasingChain L C :=
    { stage := ⟨R, hR⟩
      nonempty_stage := fun n => by
        obtain ⟨a⟩ := (inferInstance : Nonempty (G n))
        exact ⟨j n a, a, rfl⟩ }
  have hS : S.IsElementary := by
    apply (S.isElementary_iff_successor).mpr
    intro n
    let g : S.stage n ↪ₑ[L] S.stage (n + 1) :=
      (j (n + 1)).equivRange.toElementaryEmbedding.comp
        ((step n).comp (j n).equivRange.symm.toElementaryEmbedding)
    refine ⟨g, ?_⟩
    funext x
    apply Subtype.ext
    change j (n + 1) (step n ((j n).equivRange.symm x)) = (x : C)
    rw [comm]
    exact congrArg Subtype.val ((j n).equivRange.apply_symm_apply x)
  have htop : S.unionSubstructure = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, a, rfl⟩ := cover x
    exact le_iSup S.stage n ⟨a, rfl⟩
  have hsurj : Function.Surjective S.unionSubstructure.subtype := by
    intro x
    exact ⟨⟨x, by rw [htop]; trivial⟩, rfl⟩
  let E : S.unionSubstructure ≃[L] C :=
    { toEquiv := Equiv.ofBijective S.unionSubstructure.subtype
        ⟨S.unionSubstructure.subtype.injective, hsurj⟩
      map_fun' := S.unionSubstructure.subtype.map_fun'
      map_rel' := S.unionSubstructure.subtype.map_rel' }
  intro n
  obtain ⟨e, he⟩ := S.elementary_union hS n
  refine ⟨E.toElementaryEmbedding.comp
    (e.comp (j n).equivRange.toElementaryEmbedding), ?_⟩
  funext a
  change (e ((j n).equivRange a) : C) = j n a
  rw [he]
  rfl

private theorem model_of_interleaving (T : L.Theory)
    (hT : OmegaChainClosed.{u, v, w} T)
    (G : ℕ → Theory.ModelType.{u, v, max u v w} (universalExistentialPart T))
    (H : ℕ → Theory.ModelType.{u, v, max u v w} T)
    (a : ∀ n : ℕ, G n ↪[L] H n) (b : ∀ n : ℕ, H n ↪[L] G (n+1))
    (e : ∀ n : ℕ, G n ↪ₑ[L] G (n+1)) (he : ∀ n x, b n (a n x) = e n x) :
    G 0 ⊨ T := by
  classical
  let step : ∀ n : ℕ, G n ↪[L] G (n + 1) := fun n => (b n).comp (a n)
  let F := DirectedSystem.natLERec step
  let C := FirstOrder.Language.DirectLimit (fun n => G n) F
  let j := fun n => DirectLimit.of L ℕ (fun n => G n) F n
  have hj (n : ℕ) (x : G n) : j (n + 1) (step n x) = j n x := by
    have hF : F n (n + 1) (Nat.le_succ n) = step n := by
      dsimp only [F, DirectedSystem.natLERec]
      rw [Nat.leRecOn_succ (Nat.le_refl n), Nat.leRecOn_self]
      rfl
    have hh := DirectLimit.of_f (f := F) (i := n) (j := n + 1)
      (hij := Nat.le_succ n) (x := x)
    change j (n + 1) (F n (n + 1) (Nat.le_succ n) x) = j n x at hh
    rwa [hF] at hh
  let k : ∀ n, H n ↪[L] C := fun n => (j (n + 1)).comp (b n)
  let next : ∀ n, H n ↪[L] H (n + 1) := fun n => (a (n + 1)).comp (b n)
  have hk (n : ℕ) (x : H n) : k (n + 1) (next n x) = k n x := hj (n + 1) (b n x)
  have coverj (x : C) : ∃ n y, j n y = x := DirectLimit.exists_of x
  have coverk (x : C) : ∃ n y, k n y = x := by
    obtain ⟨n, y, rfl⟩ := coverj x
    exact ⟨n, a n y, hj n y⟩
  have hje (n : ℕ) (x : G n) : j (n + 1) (e n x) = j n x := by
    rw [← he]
    exact hj n x
  obtain ⟨em, _hem⟩ := elementary_from_cofinal_sequence (fun n => G n) j
    (fun n => e n) hje coverj 0
  have hlim : FirstOrder.Language.DirectLimit (fun n => H n)
      (DirectedSystem.natLERec next) ⊨ T := hT H next
  let map := FirstOrder.Language.DirectLimit.lift L ℕ (fun n => H n)
    (DirectedSystem.natLERec next) k (by
      intro i j hij x
      induction j, hij using Nat.le_induction with
      | base => simp only [DirectedSystem.natLERec, Nat.leRecOn_self, Embedding.refl_apply]
      | succ j hij ih =>
        dsimp only [DirectedSystem.natLERec]
        rw [Nat.leRecOn_succ hij]
        change k (j + 1) (next j _) = k i x
        rw [hk]
        exact ih)
  have hsurj : Function.Surjective map := by
    intro x
    obtain ⟨n, y, rfl⟩ := coverk x
    exact ⟨DirectLimit.of L ℕ (fun n => H n) (DirectedSystem.natLERec next) n y,
      by simp only [map, DirectLimit.lift_of]⟩
  let iso : FirstOrder.Language.DirectLimit (fun n => H n)
      (DirectedSystem.natLERec next) ≃[L] C :=
    { toEquiv := Equiv.ofBijective map ⟨map.injective, hsurj⟩
      map_fun' := map.map_fun'
      map_rel' := map.map_rel' }
  let := hlim
  have hCT : C ⊨ T := StrongHomClass.theory_model iso
  exact (em.theory_model_iff T).mpr hCT


/-- Interleaving ordinary T-model inclusions with elementary consequence-model inclusions. -/
theorem model_part_of_omega_closed (T : L.Theory)
    (hT : OmegaChainClosed.{u, v, w} T)
    (M : Theory.ModelType.{u, v, max u v w} (universalExistentialPart T)) : M ⊨ T := by
  classical
  have extend (B : Theory.ModelType.{u, v, max u v w} (universalExistentialPart T)) :
      ∃ (N : Theory.ModelType.{u, v, max u v w} T) (P : Theory.ModelType.{u, v, max u v w} (universalExistentialPart T))
        (f : B ↪[L] N) (g : N ↪[L] P) (e : B ↪ₑ[L] P), ∀ a, g (f a) = e a := by
    obtain ⟨N, sN, hne, hNT, f, hf⟩ := (model_part_iff_reflecting_embedding.{u, v, max u v w} T B).mp B.is_model
    let := sN
    let := hne
    let := hNT
    obtain ⟨P, sP, hPe, e, g, hcomm⟩ := elementary_factorization.{u, v, max u v w, max u v w} f hf
    let := sP
    let := hPe
    have hPT : P ⊨ universalExistentialPart T := (e.theory_model_iff _).mp B.is_model
    let := hPT
    exact ⟨Theory.ModelType.of T N, Theory.ModelType.of (universalExistentialPart T) P,
      f, g, e, hcomm⟩
  choose N P a b e he using extend
  let G : ℕ → Theory.ModelType.{u, v, max u v w} (universalExistentialPart T) := Nat.rec M (fun _ B => P B)
  let H : ℕ → Theory.ModelType.{u, v, max u v w} T := fun n => N (G n)
  exact model_of_interleaving T hT G H (fun n => a (G n)) (fun n => b (G n))
    (fun n => e (G n)) (fun n => he (G n))

/-- The equivalent axiom set is specifically the set of actual universal-existential consequences. -/
theorem universalExistentialPart_equivalent (T : L.Theory)
    (hT : OmegaChainClosed.{u, v, w} T) :
    Theories.Equivalent T (universalExistentialPart T) := by
  classical
  ext A
  change A ⊨ T ↔ A ⊨ universalExistentialPart T
  constructor
  · intro hA
    let := hA
    exact model_universalExistentialPart T A
  · intro hA
    let := hA
    let B := Theory.ModelType.ulift.{u, v, max u v, w}
      (Theory.ModelType.of (universalExistentialPart T) A)
    have hB : B ⊨ T := model_part_of_omega_closed T hT B
    let e : A ≃[L] B := (Equiv.ulift.{w}.symm).inducedStructureEquiv
    exact (e.toElementaryEmbedding.theory_model_iff T).mpr hB

/-- The five human conditions are proved through the same native syntax and actual unions. -/
theorem inductive_characterization (T : L.Theory) :
    (IsInductive.{u, v, w} T ↔ OmegaChainClosed.{u, v, w} T) ∧
    (OmegaChainClosed.{u, v, w} T ↔ Theories.Equivalent T (universalExistentialPart T)) ∧
    (Theories.Equivalent T (universalExistentialPart T) ↔
      HasUniversalExistentialAxiomatization T) ∧
    (HasUniversalExistentialAxiomatization T ↔ DirectedUnionClosed.{u, v, w} T) := by
  have axiom_of_part (h : Theories.Equivalent T (universalExistentialPart T)) :
      HasUniversalExistentialAxiomatization T :=
    ⟨_, fun _ hσ => hσ.1, h⟩
  have omega_of_axiom (h : HasUniversalExistentialAxiomatization T) :
      OmegaChainClosed.{u, v, w} T :=
    inductive_implies_omega T (directed_implies_inductive T
      (axiomatization_implies_directed T h))
  have axiom_of_omega (h : OmegaChainClosed.{u, v, w} T) :
      HasUniversalExistentialAxiomatization T :=
    axiom_of_part (universalExistentialPart_equivalent T h)
  refine ⟨⟨inductive_implies_omega T, fun h => directed_implies_inductive T
      (axiomatization_implies_directed T (axiom_of_omega h))⟩,
    ⟨universalExistentialPart_equivalent T, fun h => omega_of_axiom (axiom_of_part h)⟩,
    ⟨axiom_of_part, fun h => universalExistentialPart_equivalent T (omega_of_axiom h)⟩,
    ⟨axiomatization_implies_directed T, fun h =>
      axiom_of_omega (inductive_implies_omega T (directed_implies_inductive T h))⟩⟩

end Lemmatheca.ModelTheory.InductiveTheories
