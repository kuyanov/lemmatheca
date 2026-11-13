import Lemmatheca.StronglyMinimalModelsAndDimension.Extensions
import Lemmatheca.PregeometryDimension.Bases
import Lemmatheca.StronglyMinimalSets.Exchange

namespace Lemmatheca.ModelTheory.StronglyMinimalModelsAndDimension
open FirstOrder FirstOrder.Language
open PartialElementaryMaps StronglyMinimalSets Closures
universe u v w w'
noncomputable section
local instance smdClassificationPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {L : Language.{u,v}} (T : L.Theory) (hT : T.IsComplete)
variable (hSM : StronglyMinimalTheory T)
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
variable [Nonempty M] [Nonempty N] [M ⊨ T] [N ⊨ T]

def ModelBasis (B : Set M) : Prop :=
  (aclPregeometry T hSM (M := M)).IsBasis B Set.univ

def modelDimension (M : Type w) [L.Structure M] [Nonempty M] [M ⊨ T] : Cardinal.{w} :=
  (aclPregeometry T hSM (M := M)).dimension Set.univ

omit hT [L.Structure N] [Nonempty N] [N ⊨ T] in
theorem model_basis_iff (B : Set M) :
    ModelBasis T hSM B ↔
      (aclPregeometry T hSM (M := M)).Independent B ∧ acl L B = Set.univ := by
  simp only [ModelBasis, Pregeometry.IsBasis, Set.subset_univ, true_and]
  rfl

omit hT [L.Structure N] [Nonempty N] [N ⊨ T] in
theorem exists_model_basis : ∃ B : Set M, ModelBasis T hSM B := by
  let P := aclPregeometry T hSM (M := M)
  obtain ⟨B,hB,hI,hcl⟩ := P.exists_generating_basis Set.univ
  have hc : P.cl Set.univ = Set.univ :=
    Set.Subset.antisymm (Set.subset_univ _) (P.extensive _)
  exact ⟨B,hB,hI,hcl.trans hc⟩

omit hT [L.Structure N] [Nonempty N] [N ⊨ T] in
theorem basis_dimension (B : Set M) (hB : ModelBasis T hSM B) :
    modelDimension T hSM M = Cardinal.mk B := by
  let P := aclPregeometry T hSM (M := M)
  have hc : P.cl Set.univ = Set.univ :=
    Set.Subset.antisymm (Set.subset_univ _) (P.extensive _)
  change P.IsBasis B Set.univ at hB
  exact P.dimension_eq_mk (by simpa only [hc] using hB)

include hT in
private theorem finite_prescribed_map (I : Set M) (J : Set N)
    (hI : (aclPregeometry T hSM (M := M)).Independent I)
    (hJ : (aclPregeometry T hSM (M := N)).Independent J) (e : I ≃ J)
    (F : Finset I) :
    ∃ p : Map L M N, p.dom = Subtype.val '' (F : Set I) ∧
      ∀ (x : I) (hx : x.val ∈ p.dom), p.toFun ⟨x.val,hx⟩ = (e x).val := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    let p := Map.empty (hT.models_elementarily_equivalent M N)
    have hd : p.dom = ∅ := FiniteMap.empty_dom (hT.models_elementarily_equivalent M N)
    refine ⟨p, by simp only [Finset.coe_empty, Set.image_empty, hd], ?_⟩
    intro x hx
    rw [hd] at hx
    exact False.elim hx
  | @insert x F hx ih =>
    obtain ⟨p, hpdom, hpval⟩ := ih
    have hsource : p.dom ⊆ I \ {x.val} := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := (show z ∈ Subtype.val '' (F : Set I) by rwa [← hpdom])
      refine ⟨y.property, ?_⟩
      intro he
      have hyx : y = x := Subtype.ext he
      exact hx (hyx ▸ hy)
    have htarget : p.range ⊆ J \ {(e x).val} := by
      rintro b ⟨z, rfl⟩
      obtain ⟨y, hy, he⟩ := (show z.val ∈ Subtype.val '' (F : Set I) by rw [← hpdom]; exact z.property)
      have hymem : y.val ∈ p.dom := he.symm ▸ z.property
      have harg : (⟨y.val,hymem⟩ : p.dom) = z := Subtype.ext he
      have hval : p.toFun z = (e y).val := by simpa only [harg] using hpval y hymem
      rw [hval]
      refine ⟨(e y).property, ?_⟩
      intro heq
      have hyx : y = x := e.injective (Subtype.ext heq)
      exact hx (hyx ▸ hy)
    have ha : x.val ∉ acl L p.dom := by
      intro h
      exact hI x.val x.property (acl_mono hsource h)
    have hb : (e x).val ∉ acl L p.range := by
      intro h
      exact hJ (e x).val (e x).property (acl_mono htarget h)
    obtain ⟨q, hpq, hqdom, _, hxq, hqx⟩ :=
      generic_extension p (theory_model_minimal T hSM) x.val (e x).val ha hb
    refine ⟨q, ?_, ?_⟩
    · rw [hqdom, hpdom]
      simp only [Finset.coe_insert, Set.image_insert_eq]
    · intro y hyq
      by_cases hyx : y = x
      · subst y
        exact hqx
      · have hyold : y.val ∈ p.dom := by
          rw [hqdom] at hyq
          rcases Set.mem_insert_iff.mp hyq with he | hy
          · exact False.elim (hyx (Subtype.ext he))
          · exact hy
        calc
          q.toFun ⟨y.val,hyq⟩ = p.toFun ⟨y.val,hyold⟩ := Map.apply_mono hpq ⟨y.val,hyold⟩
          _ = (e y).val := hpval y hyold

include hT in
/-- Every finite tuple is transported by precisely the supplied independent-set bijection. -/
private theorem independent_elementary (I : Set M) (J : Set N)
    (hI : (aclPregeometry T hSM (M := M)).Independent I)
    (hJ : (aclPregeometry T hSM (M := N)).Independent J) (e : I ≃ J)
    {n : ℕ} (φ : L.Formula (Fin n)) (a : Fin n → I) :
    φ.Realize ((fun x : I => (e x).val) ∘ a) ↔ φ.Realize (Subtype.val ∘ a) := by
  classical
  let F : Finset I := Finset.univ.image a
  obtain ⟨p, hpdom, hpval⟩ := finite_prescribed_map T hT hSM I J hI hJ e F
  let b : Fin n → p.dom := fun i => ⟨(a i).val, by
    rw [hpdom]
    exact ⟨a i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, rfl⟩⟩
  have ht : p.toFun ∘ b = (fun x : I => (e x).val) ∘ a := by
    funext i
    exact hpval (a i) (b i).property
  have hs : (Subtype.val : p.dom → M) ∘ b = Subtype.val ∘ a := rfl
  have h := p.elementary φ b
  rwa [ht, hs] at h

/-- Its actual function is the supplied independent-set bijection, with no change of images. -/
def independentMap (T : L.Theory) (hT : T.IsComplete) (hSM : StronglyMinimalTheory T)
    [M ⊨ T] [N ⊨ T] (I : Set M) (J : Set N)
    (hI : (aclPregeometry T hSM (M := M)).Independent I)
    (hJ : (aclPregeometry T hSM (M := N)).Independent J) (e : I ≃ J) : Map L M N where
  dom := I
  toFun := fun a => (e a).val
  injective := Subtype.val_injective.comp e.injective
  elementary := by
    intro n φ a
    exact independent_elementary T hT hSM I J hI hJ e φ a

theorem independent_map_spec (I : Set M) (J : Set N)
    (hI : (aclPregeometry T hSM (M := M)).Independent I)
    (hJ : (aclPregeometry T hSM (M := N)).Independent J) (e : I ≃ J) :
    (independentMap T hT hSM I J hI hJ e).dom = I ∧
      (independentMap T hT hSM I J hI hJ e).range = J ∧
      ∀ a : I, (independentMap T hT hSM I J hI hJ e).toFun a = (e a).val := by
  refine ⟨rfl,?_,fun _ => rfl⟩
  ext b
  constructor
  · rintro ⟨a,rfl⟩
    exact (e a).property
  · intro hb
    refine ⟨e.symm ⟨b,hb⟩,?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨b,hb⟩)

include hT in
/-- Maximal algebraic extensions retain the entire specified original basis bijection. -/
theorem basis_bijection_extends (B : Set M) (C : Set N)
    (hB : ModelBasis T hSM B) (hC : ModelBasis T hSM C) (e : B ≃ C) :
    ∃ F : M ≃[L] N, ∀ b : B, F b.val = (e b).val := by
  have hB' := (model_basis_iff T hSM B).mp hB
  have hC' := (model_basis_iff T hSM C).mp hC
  let p := independentMap T hT hSM B C hB'.1 hC'.1 e
  have hp := independent_map_spec T hT hSM B C hB'.1 hC'.1 e
  obtain ⟨q, hpq, hmax⟩ := Map.exists_maximal_extension p
  have hBdom : B ⊆ q.dom := Map.dom_mono hpq
  have hCrange : C ⊆ q.range := by
    rw [← hp.2.1]
    exact Map.range_mono hpq
  have hdom : q.dom = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro a
    by_contra hnew
    have ha : a ∈ acl L q.dom := by
      apply acl_mono hBdom
      rw [hB'.2]
      exact Set.mem_univ a
    obtain ⟨b, _, _, r, hqr, hrdom, _, _⟩ := algebraic_extension q a ha hnew
    have hrq : r = q := hmax r hqr
    apply hnew
    rw [← hrq, hrdom]
    exact Set.mem_insert a q.dom
  have hran : q.range = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro b
    by_contra hnew
    have hb : b ∈ acl L q.symm.dom := by
      change b ∈ acl L q.range
      apply acl_mono hCrange
      rw [hC'.2]
      exact Set.mem_univ b
    obtain ⟨a, _, hnot, _⟩ := algebraic_extension q.symm b hb hnew
    rw [Map.symm_range q, hdom] at hnot
    exact hnot (Set.mem_univ a)
  obtain ⟨F, hF⟩ := Map.total_isomorphism q hdom hran
  refine ⟨F, ?_⟩
  intro b
  let a : q.dom := ⟨b.val, hBdom b.property⟩
  calc
    F b.val = q.toFun a := hF a
    _ = p.toFun b := Map.apply_mono hpq b
    _ = (e b).val := rfl

omit T hT hSM [Nonempty M] [Nonempty N] [M ⊨ T] [N ⊨ T] in
theorem isomorphism_image_acl (F : M ≃[L] N) (A : Set M) :
    F '' acl L A = acl L (F '' A) := by
  exact elementary_image_acl F.toElementaryEmbedding A

omit hT in
theorem isomorphism_image_independent (F : M ≃[L] N) (I : Set M)
    (hI : (aclPregeometry T hSM (M := M)).Independent I) :
    (aclPregeometry T hSM (M := N)).Independent (F '' I) := by
  intro b hb hbcl
  obtain ⟨a, ha, rfl⟩ := hb
  apply hI a ha
  change a ∈ acl L (I \ {a})
  change F a ∈ acl L (F '' I \ {F a}) at hbcl
  have hdiff : F '' (I \ {a}) = F '' I \ {F a} := by
    rw [Set.image_sdiff F.injective, Set.image_singleton]
  rw [← hdiff, ← isomorphism_image_acl F (I \ {a})] at hbcl
  obtain ⟨x, hx, he⟩ := hbcl
  exact (F.injective he) ▸ hx

omit hT in
theorem isomorphism_image_basis (F : M ≃[L] N) (B : Set M) (hB : ModelBasis T hSM B) :
    ModelBasis T hSM (F '' B) := by
  rw [model_basis_iff] at hB ⊢
  refine ⟨isomorphism_image_independent T hSM F B hB.1, ?_⟩
  rw [← isomorphism_image_acl F B, hB.2]
  exact Set.image_univ_of_surjective F.surjective

omit hT in
theorem isomorphism_dimension (F : M ≃[L] N) :
    Cardinal.lift.{w'} (modelDimension T hSM M) =
      Cardinal.lift.{w} (modelDimension T hSM N) := by
  obtain ⟨B, hB⟩ := exists_model_basis T hSM (M := M)
  rw [basis_dimension T hSM B hB,
    basis_dimension T hSM (F '' B) (isomorphism_image_basis T hSM F B hB)]
  exact (Cardinal.mk_image_eq_lift (F : M → N) B F.injective).symm

include hT in
theorem isomorphic_iff_dimension :
    Nonempty (M ≃[L] N) ↔
      Cardinal.lift.{w'} (modelDimension T hSM M) =
        Cardinal.lift.{w} (modelDimension T hSM N) := by
  constructor
  · rintro ⟨F⟩
    exact isomorphism_dimension T hSM F
  · intro hdim
    obtain ⟨B,hB⟩ := exists_model_basis T hSM (M := M)
    obtain ⟨C,hC⟩ := exists_model_basis T hSM (M := N)
    rw [basis_dimension T hSM B hB,basis_dimension T hSM C hC] at hdim
    obtain ⟨e⟩ := Cardinal.lift_mk_eq'.mp hdim
    obtain ⟨F,_⟩ := basis_bijection_extends T hT hSM B C hB hC e
    exact ⟨F⟩

end
end Lemmatheca.ModelTheory.StronglyMinimalModelsAndDimension
