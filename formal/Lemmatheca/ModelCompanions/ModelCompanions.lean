import Lemmatheca.ModelCompleteness.ModelCompleteness
import Lemmatheca.ElementaryChains.ElementaryChains

/-! Model companions and model completions, with shared signed diagrams and actual maps. -/
namespace Lemmatheca.ModelTheory.ModelCompanions

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.ModelCompleteness
open Lemmatheca.ModelTheory.Preservation
open Lemmatheca.ModelTheory.QuantifierElimination

universe u v w
variable {L : Language.{u, v}}

/-- Each nonempty model of the first theory embeds into a model of the second. -/
def EmbedsModels (T U : L.Theory) : Prop :=
  ∀ M : Theory.ModelType.{u, v, max u v w} T,
    ∃ N : Theory.ModelType.{u, v, max u v w} U, Nonempty (M ↪[L] N)

/-- Mutual embeddability into models, rather than elementary equivalence. -/
def Companions (T U : L.Theory) : Prop :=
  EmbedsModels.{u, v, w} T U ∧ EmbedsModels.{u, v, w} U T

/-- The second theory is a model-complete companion of the first. -/
def ModelCompanion (T U : L.Theory) : Prop :=
  Companions.{u, v, w} T U ∧ ModelComplete.{u, v, w} U

theorem companions_refl (T : L.Theory) : Companions.{u, v, w} T T := by
  constructor <;> intro M <;> exact ⟨M, ⟨Embedding.refl L M⟩⟩

theorem Companions.symm {T U : L.Theory} (h : Companions.{u, v, w} T U) :
    Companions.{u, v, w} U T := by
  exact ⟨h.2, h.1⟩

theorem Companions.trans {T U V : L.Theory} (hTU : Companions.{u, v, w} T U)
    (hUV : Companions.{u, v, w} U V) : Companions.{u, v, w} T V := by
  constructor
  · intro M
    obtain ⟨N, ⟨f⟩⟩ := hTU.1 M
    obtain ⟨P, ⟨g⟩⟩ := hUV.1 N
    exact ⟨P, ⟨g.comp f⟩⟩
  · intro M
    obtain ⟨N, ⟨f⟩⟩ := hUV.2 M
    obtain ⟨P, ⟨g⟩⟩ := hTU.2 N
    exact ⟨P, ⟨g.comp f⟩⟩

private theorem universalPart_subset_of_embedsModels {T U : L.Theory}
    (h : EmbedsModels.{u, v, w} T U) : universalPart U ⊆ universalPart T := by
  rintro σ ⟨hσ, hUσ⟩
  refine ⟨hσ, Theory.models_sentence_iff.mpr ?_⟩
  intro M
  let A := Theory.ModelType.ulift.{u, v, max u v, w} M
  obtain ⟨N, ⟨f⟩⟩ := h A
  let : (universalPart U).IsUniversal := ⟨fun _ hγ => hγ.1⟩
  let : N ⊨ universalPart U := model_universalPart U N
  have hA : A ⊨ universalPart U := Theory.IsUniversal.models_of_embedding f
  have hAσ : A ⊨ σ := hA.realize_of_mem σ ⟨hσ, hUσ⟩
  let e : M ≃[L] A := (Equiv.ulift.{w}.symm).inducedStructureEquiv
  exact (e.toElementaryEmbedding.map_sentence σ).mpr hAσ

/-- Universal consequences determine exactly which structures embed into models. -/
theorem companions_iff_universalPart (T U : L.Theory) :
    Companions.{u, v, w} T U ↔ universalPart T = universalPart U := by
  constructor
  · intro h
    exact Set.Subset.antisymm (universalPart_subset_of_embedsModels h.2)
      (universalPart_subset_of_embedsModels h.1)
  · intro h
    have embed {S R : L.Theory} (he : universalPart S = universalPart R) :
        EmbedsModels.{u, v, w} S R := by
      intro M
      have hM : M ⊨ universalPart R := by
        rw [← he]
        exact model_universalPart S M
      obtain ⟨N, sN, hne, hN, ⟨f⟩⟩ := (model_universalPart_iff_embeds R M).mp hM
      let := sN
      let := hne
      let := hN
      exact ⟨Theory.ModelType.of R N, ⟨f⟩⟩
    exact ⟨embed h, embed h.symm⟩

private theorem cofinal_elementary_maps {T : L.Theory}
    (hT : ModelComplete.{u, v, w} T)
    (G : ℕ → Theory.ModelType.{u, v, max u v w} T)
    {C : Type (max u v w)} [L.Structure C]
    (j : ∀ n, G n ↪[L] C) (f : ∀ n, G n ↪[L] G (n + 1))
    (comm : ∀ n a, j (n + 1) (f n a) = j n a)
    (cover : ∀ x : C, ∃ n a, j n a = x) :
    ∀ n, ∃ e : G n ↪ₑ[L] C, (e : G n → C) = j n := by
  classical
  let R : ℕ → L.Substructure C := fun n => (j n).toHom.range
  have hR : Monotone R := by
    apply monotone_nat_of_le_succ
    intro n x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨f n a, comm n a⟩
  let S : ElementaryChains.IncreasingChain L C :=
    { stage := ⟨R, hR⟩
      nonempty_stage := fun n => by
        obtain ⟨a⟩ := (inferInstance : Nonempty (G n))
        exact ⟨j n a, a, rfl⟩ }
  have hS : S.IsElementary := by
    apply (S.isElementary_iff_successor).mpr
    intro n
    obtain ⟨e, he⟩ := hT (G n) (G (n + 1)) (f n)
    let g : S.stage n ↪ₑ[L] S.stage (n + 1) :=
      (j (n + 1)).equivRange.toElementaryEmbedding.comp
        (e.comp (j n).equivRange.symm.toElementaryEmbedding)
    refine ⟨g, ?_⟩
    funext x
    apply Subtype.ext
    change j (n + 1) (e ((j n).equivRange.symm x)) = (x : C)
    rw [he, comm]
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

private theorem common_of_interleaving {U V : L.Theory}
    (hU : ModelComplete.{u, v, w} U) (hV : ModelComplete.{u, v, w} V)
    (G : ℕ → Theory.ModelType.{u, v, max u v w} U)
    (H : ℕ → Theory.ModelType.{u, v, max u v w} V)
    (a : ∀ n, G n ↪[L] H n) (b : ∀ n, H n ↪[L] G (n + 1)) :
    ∃ C : Theory.ModelType.{u, v, max u v w} U, C ⊨ V ∧ Nonempty (G 0 ↪ₑ[L] C) := by
  classical
  let step : ∀ n : ℕ, G n ↪[L] G (n + 1) := fun n => (b n).comp (a n)
  let F := DirectedSystem.natLERec step
  let C := FirstOrder.Language.DirectLimit (fun n => G n) F
  let j : ∀ n : ℕ, G n ↪[L] C := fun n => DirectLimit.of L ℕ (fun n => G n) F n
  have hj (n : ℕ) (x : G n) : j (n + 1) (step n x) = j n x := by
    have hF : F n (n + 1) (Nat.le_succ n) = step n := by
      dsimp only [F, DirectedSystem.natLERec]
      rw [Nat.leRecOn_succ (Nat.le_refl n), Nat.leRecOn_self]
      rfl
    have h := DirectLimit.of_f (f := F) (i := n) (j := n + 1)
      (hij := Nat.le_succ n) (x := x)
    change j (n + 1) (F n (n + 1) (Nat.le_succ n) x) = j n x at h
    rwa [hF] at h
  have coverj (x : C) : ∃ n y, j n y = x := DirectLimit.exists_of x
  let k : ∀ n : ℕ, H n ↪[L] C := fun n => (j (n + 1)).comp (b n)
  let next : ∀ n : ℕ, H n ↪[L] H (n + 1) := fun n => (a (n + 1)).comp (b n)
  have hk (n : ℕ) (x : H n) : k (n + 1) (next n x) = k n x :=
    hj (n + 1) (b n x)
  have coverk (x : C) : ∃ n y, k n y = x := by
    obtain ⟨n, y, rfl⟩ := coverj x
    exact ⟨n, a n y, hj n y⟩
  obtain ⟨ej, _hej⟩ := cofinal_elementary_maps hU G j step hj coverj 0
  obtain ⟨ek, _hek⟩ := cofinal_elementary_maps hV H k next hk coverk 0
  let : Nonempty C := Nonempty.map (j 0) inferInstance
  let hCU : C ⊨ U := (ej.theory_model_iff U).mp (G 0).is_model
  have hCV : C ⊨ V := (ek.theory_model_iff V).mp (H 0).is_model
  exact ⟨Theory.ModelType.of U C, hCV, ⟨ej⟩⟩

/-- Interleaving produces a common model and an elementary map from the given initial model. -/
theorem common_elementary_extension {U V : L.Theory} (hUV : Companions.{u, v, w} U V)
    (hU : ModelComplete.{u, v, w} U) (hV : ModelComplete.{u, v, w} V)
    (M : Theory.ModelType.{u, v, max u v w} U) :
    ∃ C : Theory.ModelType.{u, v, max u v w} U, C ⊨ V ∧ Nonempty (M ↪ₑ[L] C) := by
  classical
  let pickV (A : Theory.ModelType.{u, v, max u v w} U) :
      Theory.ModelType.{u, v, max u v w} V := Classical.choose (hUV.1 A)
  let intoV (A : Theory.ModelType.{u, v, max u v w} U) : A ↪[L] pickV A :=
    Classical.choice (Classical.choose_spec (hUV.1 A))
  let pickU (B : Theory.ModelType.{u, v, max u v w} V) :
      Theory.ModelType.{u, v, max u v w} U := Classical.choose (hUV.2 B)
  let intoU (B : Theory.ModelType.{u, v, max u v w} V) : B ↪[L] pickU B :=
    Classical.choice (Classical.choose_spec (hUV.2 B))
  let G : ℕ → Theory.ModelType.{u, v, max u v w} U :=
    Nat.rec M (fun _ A => pickU (pickV A))
  let H : ℕ → Theory.ModelType.{u, v, max u v w} V := fun n => pickV (G n)
  exact common_of_interleaving hU hV G H
    (fun n => intoV (G n)) (fun n => intoU (H n))

/-- Uniqueness means semantic equivalence, allowing different axiom sets. -/
theorem modelCompanion_unique {T U V : L.Theory} (hU : ModelCompanion.{u, v, w} T U)
    (hV : ModelCompanion.{u, v, w} T V) :
    Lemmatheca.ModelTheory.Theories.Equivalent U V := by
  have hUV : Companions.{u, v, w} U V := hU.1.symm.trans hV.1
  have model_of {S R : L.Theory} (hSR : Companions.{u, v, w} S R)
      (hS : ModelComplete.{u, v, w} S) (hR : ModelComplete.{u, v, w} R)
      (A : Lemmatheca.ModelTheory.Theories.Structures L) (hA : A ⊨ S) : A ⊨ R := by
    let := hA
    let B := Theory.ModelType.ulift.{u, v, max u v, w} (Theory.ModelType.of S A)
    obtain ⟨C, hCR, ⟨f⟩⟩ := common_elementary_extension hSR hS hR B
    have hBR : B ⊨ R := (f.theory_model_iff R).mpr hCR
    let e : A ≃[L] B := (Equiv.ulift.{w}.symm).inducedStructureEquiv
    exact (e.toElementaryEmbedding.theory_model_iff R).mpr hBR
  ext A
  exact ⟨model_of hUV hU.2 hV.2 A, model_of hUV.symm hV.2 hU.2 A⟩

/-- The original theory is carried into the language naming all elements of the structure. -/
def diagramTheory (U : L.Theory) (M : Type*) [L.Structure M] : L[[M]].Theory :=
  (L.lhomWithConstants M).onTheory U ∪ Diagrams.signedDiagram L M

private theorem named_diagram_model {U : L.Theory} {M : Type*} {N : Type*}
    [L.Structure M] [L.Structure N] [N ⊨ U] (f : M ↪[L] N) :
    let := Diagrams.namedExpansion (L := L) (f : M → N)
    N ⊨ diagramTheory U M := by
  let : L[[M]].Structure N := Diagrams.namedExpansion (L := L) (f : M → N)
  let : (L.lhomWithConstants M).IsExpansionOn N := Diagrams.namedExpansion_isExpansion f
  have hU : N ⊨ (L.lhomWithConstants M).onTheory U :=
    (LHom.onTheory_model _ _).mpr inferInstance
  exact hU.union (Diagrams.embedding_namedExpansion_models_signed f)

private theorem diagram_model_reduct {U : L.Theory} {M : Type*} {N : Type*}
    [L.Structure M] [L[[M]].Structure N] (hN : N ⊨ diagramTheory U M) :
    let := (L.lhomWithConstants M).reduct N
    (N ⊨ U) ∧ ∃ f : M ↪[L] N, (f : M → N) = Diagrams.canonicalMap L M N := by
  let : L.Structure N := (L.lhomWithConstants M).reduct N
  let : (L.lhomWithConstants M).IsExpansionOn N := LHom.isExpansionOn_reduct _ _
  exact ⟨(LHom.onTheory_model _ _).mp (hN.mono Set.subset_union_left),
    Diagrams.model_signed_iff_canonical_embedding.mp (hN.mono Set.subset_union_right)⟩

/-- Completion requires both existence and completeness of each named-diagram extension. -/
def ModelCompletion (T U : L.Theory) : Prop :=
  T ⊆ U ∧ ∀ M : Theory.ModelType.{u, v, max u v w} T,
    (diagramTheory U M).IsComplete

private theorem complete_diagram_of_embedding_agreement {U : L.Theory}
    (M : Type (max u v w)) [L.Structure M] [Nonempty M]
    (hsat : (diagramTheory U M).IsSatisfiable)
    (agree : ∀ (A B : Theory.ModelType.{u, v, max u v w} U)
      (f : M ↪[L] A) (g : M ↪[L] B) (n : ℕ) (φ : L.Formula (Fin n)) (a : Fin n → M),
      φ.Realize (f ∘ a) ↔ φ.Realize (g ∘ a)) :
    (diagramTheory U M).IsComplete := by
  apply (Theory.IsComplete.isComplete_iff_models_elementarily_equivalent).mpr
  refine ⟨hsat, ?_⟩
  intro A B
  let : L.Structure A := (L.lhomWithConstants M).reduct A
  let : L.Structure B := (L.lhomWithConstants M).reduct B
  let : (L.lhomWithConstants M).IsExpansionOn A := LHom.isExpansionOn_reduct _ _
  let : (L.lhomWithConstants M).IsExpansionOn B := LHom.isExpansionOn_reduct _ _
  obtain ⟨hA, f, hf⟩ := diagram_model_reduct A.is_model
  obtain ⟨hB, g, hg⟩ := diagram_model_reduct B.is_model
  let := hA
  let := hB
  apply elementarilyEquivalent_iff.mpr
  intro γ
  obtain ⟨n, φ, a, rfl, _hLit, _hQf⟩ := Diagrams.sentence_is_namedFormula γ
  rw [Diagrams.realize_namedFormula, Diagrams.realize_namedFormula, ← hf, ← hg]
  exact agree (Theory.ModelType.of U A) (Theory.ModelType.of U B) f g n φ a

private theorem qe_embedding_agreement {U : L.Theory} (hQE : HasQuantifierElimination U)
    {M A B : Type*} [L.Structure M] [L.Structure A] [L.Structure B]
    [Nonempty A] [Nonempty B] [A ⊨ U] [B ⊨ U]
    (f : M ↪[L] A) (g : M ↪[L] B) {n : ℕ} (φ : L.Formula (Fin n)) (a : Fin n → M) :
    φ.Realize (f ∘ a) ↔ φ.Realize (g ∘ a) := by
  obtain ⟨ψ, hψ, he⟩ := hQE n (Shared.pack φ)
  have hA : φ.Realize (f ∘ a) ↔ ψ.Realize Empty.elim (f ∘ a) :=
    (Shared.pack_realize φ (f ∘ a)).symm.trans (he.realize_bd_iff (M := A))
  have hB : φ.Realize (g ∘ a) ↔ ψ.Realize Empty.elim (g ∘ a) :=
    (Shared.pack_realize φ (g ∘ a)).symm.trans (he.realize_bd_iff (M := B))
  have hf : ψ.Realize Empty.elim (f ∘ a) ↔ ψ.Realize Empty.elim a := by
    have hv : f ∘ (Empty.elim : Empty → M) = (Empty.elim : Empty → A) :=
      Subsingleton.elim _ _
    simpa only [hv] using (hψ.realize_embedding f (v := Empty.elim) (xs := a))
  have hg : ψ.Realize Empty.elim (g ∘ a) ↔ ψ.Realize Empty.elim a := by
    have hv : g ∘ (Empty.elim : Empty → M) = (Empty.elim : Empty → B) :=
      Subsingleton.elim _ _
    simpa only [hv] using (hψ.realize_embedding g (v := Empty.elim) (xs := a))
  exact hA.trans (hf.trans (hg.symm.trans hB.symm))

/-- Named-diagram satisfiability yields extension models; its completeness yields elementarity. -/
theorem modelCompletion_modelCompanion {T U : L.Theory}
    (h : ModelCompletion.{u, v, w} T U) : ModelCompanion.{u, v, w} T U := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro M
    let N := (h.2 M).1.some
    let : L.Structure N := (L.lhomWithConstants M).reduct N
    obtain ⟨hNU, f, _hf⟩ := diagram_model_reduct N.is_model
    let := hNU
    exact ⟨Theory.ModelType.of U N, ⟨f⟩⟩
  · intro N
    let : N ⊨ T := N.is_model.mono h.1
    exact ⟨Theory.ModelType.of T N, ⟨Embedding.refl L N⟩⟩
  · intro M N f
    let : M ⊨ T := M.is_model.mono h.1
    have hc : (diagramTheory U M).IsComplete := h.2 (Theory.ModelType.of T M)
    let : L[[M]].Structure M := Diagrams.namedExpansion (L := L) (id : M → M)
    let : L[[M]].Structure N := Diagrams.namedExpansion (L := L) (f : M → N)
    let : (L.lhomWithConstants M).IsExpansionOn M := Diagrams.namedExpansion_isExpansion id
    let : (L.lhomWithConstants M).IsExpansionOn N := Diagrams.namedExpansion_isExpansion f
    let : M ⊨ diagramTheory U M := named_diagram_model (Embedding.refl L M)
    let : N ⊨ diagramTheory U M := named_diagram_model f
    refine ⟨{ toFun := f, map_formula' := ?_ }, rfl⟩
    intro n φ a
    have hs := (elementarilyEquivalent_iff.mp (hc.models_elementarily_equivalent M N))
      (Diagrams.namedFormula φ a)
    rw [Diagrams.realize_namedFormula, Diagrams.realize_namedFormula] at hs
    change φ.Realize (id ∘ a) ↔ φ.Realize (f ∘ a) at hs
    simpa only [Function.id_comp] using hs.symm

/-- The self-completion criterion distinguishes model completeness from sentence completeness. -/
theorem modelComplete_iff_selfCompletion (T : L.Theory) :
    ModelComplete.{u, v, w} T ↔ ModelCompletion.{u, v, w} T T := by
  constructor
  · intro hT
    refine ⟨Set.Subset.rfl, ?_⟩
    intro M
    have hsat : (diagramTheory T M).IsSatisfiable := by
      let : L[[M]].Structure M := Diagrams.namedExpansion (L := L) (id : M → M)
      let : M ⊨ diagramTheory T M := named_diagram_model (Embedding.refl L M)
      exact Theory.Model.isSatisfiable M
    apply complete_diagram_of_embedding_agreement M hsat
    intro A B f g n φ a
    obtain ⟨e, he⟩ := hT M A f
    obtain ⟨j, hj⟩ := hT M B g
    have h₁ := e.map_formula φ a
    have h₂ := j.map_formula φ a
    rw [he] at h₁
    rw [hj] at h₂
    exact h₁.trans h₂.symm
  · intro h
    exact (modelCompletion_modelCompanion h).2

/-- Quantifier elimination ensures agreement over an embedded original model. -/
theorem qe_completion_criterion {T U : L.Theory} (hTU : T ⊆ U)
    (hEmb : EmbedsModels.{u, v, w} T U) (hQE : HasQuantifierElimination U) :
    ModelCompletion.{u, v, w} T U := by
  refine ⟨hTU, ?_⟩
  intro M
  have hsat : (diagramTheory U M).IsSatisfiable := by
    obtain ⟨N, ⟨f⟩⟩ := hEmb M
    let : L[[M]].Structure N := Diagrams.namedExpansion (L := L) (f : M → N)
    let : N ⊨ diagramTheory U M := named_diagram_model f
    exact Theory.Model.isSatisfiable N
  apply complete_diagram_of_embedding_agreement M hsat
  intro A B f g n φ a
  exact qe_embedding_agreement hQE f g φ a

end Lemmatheca.ModelTheory.ModelCompanions
