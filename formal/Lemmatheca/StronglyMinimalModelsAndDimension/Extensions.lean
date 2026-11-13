import Lemmatheca.StronglyMinimalModelsAndDimension.PartialMaps
import Lemmatheca.StronglyMinimalTypes.Generic

namespace Lemmatheca.ModelTheory.StronglyMinimalModelsAndDimension
open FirstOrder FirstOrder.Language
open PartialElementaryMaps StronglyMinimalSets Closures
universe u v w w'
noncomputable section
local instance smdExtensionsPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {L : Language.{u,v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

private theorem fiber_definable_over (A : Set M) {α : Type*}
    (φ : L.Formula (α ⊕ Fin 1)) (b : α → M) (hb : ∀ i, b i ∈ A) :
    A.Definable₁ L (fiber φ b) := by
  apply Set.definable_iff_exists_formula_sum.mpr
  let ψ := φ.relabel (Sum.map (fun i => (⟨b i,hb i⟩ : A)) id)
  refine ⟨ψ,?_⟩
  ext x
  simp only [ψ,Formula.realize_relabel]
  change φ.Realize (Sum.elim b (fun _ : Fin 1 => x 0)) ↔ φ.Realize _
  apply Iff.of_eq
  congr 1
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl

/-- Every formula has finite syntax, even though its parameter indices can range over A. -/
theorem fiber_definable (A : Set M) (φ : L.Formula (A ⊕ Fin 1)) :
    A.Definable₁ L (fiber φ (Subtype.val : A → M)) :=
  fiber_definable_over A φ Subtype.val Subtype.property

theorem mapped_fiber_definable (p : Map L M N) (φ : L.Formula (p.dom ⊕ Fin 1)) :
    p.range.Definable₁ L (fiber φ p.toFun) :=
  fiber_definable_over p.range φ p.toFun (fun i => ⟨i,rfl⟩)

private theorem fiber_not {α : Type*} (φ : L.Formula (α ⊕ Fin 1)) (b : α → M) :
    fiber φ.not b = (fiber φ b)ᶜ := by
  ext x
  simp only [fiber, Set.mem_ofPred_eq, Formula.realize_not, Set.mem_compl_iff]

private theorem fiber_nonempty {α : Type*} (φ : L.Formula (α ⊕ Fin 1)) (b : α → M) :
    (φ.iExs (Fin 1)).Realize b ↔ (fiber φ b).Nonempty := by
  rw [Formula.realize_iExs]
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨v 0,?_⟩
    have he : v = fun _ : Fin 1 => v 0 := funext fun i => congrArg v (Subsingleton.elim _ _)
    exact (congrArg (fun g : Fin 1 → M => φ.Realize (Sum.elim b g)) he).mp hv
  · rintro ⟨x,hx⟩
    exact ⟨fun _ => x,hx⟩

def PointMatch (p : Map L M N) (a : M) (b : N) : Prop :=
  ∀ φ : L.Formula (p.dom ⊕ Fin 1),
    φ.Realize (Sum.elim (Subtype.val : p.dom → M) (fun _ => a)) ↔
      φ.Realize (Sum.elim p.toFun (fun _ => b))

def adjoinFun (p : Map L M N) (a : M) (b : N) : ↥(insert a p.dom : Set M) → N :=
  fun x => if h : x.val = a then b
    else p.toFun ⟨x.val,(Set.mem_insert_iff.mp x.property).resolve_left h⟩

/-- The graph really is the old function together with the supplied new pair. -/
def adjoinMap (p : Map L M N) (a : M) (b : N)
    (ha : a ∉ p.dom) (hb : b ∉ p.range) (hmatch : PointMatch p a b) : Map L M N where
  dom := insert a p.dom
  toFun := adjoinFun p a b
  injective := by
    intro x y hxy
    by_cases hx : x.val = a
    · by_cases hy : y.val = a
      · exact Subtype.ext (hx.trans hy.symm)
      · have hy' : y.val ∈ p.dom := (Set.mem_insert_iff.mp y.property).resolve_left hy
        have hya : y.val ≠ a := fun he => ha (he ▸ hy')
        have he : b = p.toFun ⟨y.val,hy'⟩ := by simpa only [adjoinFun,dite_eq_left hx,dite_eq_right hya] using hxy
        exact False.elim (hb ⟨⟨y.val,hy'⟩,he.symm⟩)
    · by_cases hy : y.val = a
      · have hx' : x.val ∈ p.dom := (Set.mem_insert_iff.mp x.property).resolve_left hx
        have he : p.toFun ⟨x.val,hx'⟩ = b := by simpa only [adjoinFun,dite_eq_right hx,dite_eq_left hy] using hxy
        exact False.elim (hb ⟨⟨x.val,hx'⟩,he⟩)
      · have he : p.toFun ⟨x.val,(Set.mem_insert_iff.mp x.property).resolve_left hx⟩ =
            p.toFun ⟨y.val,(Set.mem_insert_iff.mp y.property).resolve_left hy⟩ := by
          simpa only [adjoinFun,dite_eq_right hx,dite_eq_right hy] using hxy
        exact Subtype.ext (congrArg (fun t : p.dom => t.val) (p.injective he))
  elementary := by
    intro n φ c
    let index (i : Fin n) : p.dom ⊕ Fin 1 :=
      if h : (c i).val = a then .inr 0
      else .inl ⟨(c i).val,(Set.mem_insert_iff.mp (c i).property).resolve_left h⟩
    have hsource : Sum.elim (Subtype.val : p.dom → M) (fun _ : Fin 1 => a) ∘ index =
        Subtype.val ∘ c := by
      funext i
      by_cases h : (c i).val = a <;> simp [index,h]
    have htarget : Sum.elim p.toFun (fun _ : Fin 1 => b) ∘ index =
        adjoinFun p a b ∘ c := by
      funext i
      by_cases h : (c i).val = a <;> simp [index,adjoinFun,h]
    have hm := hmatch (φ.relabel index)
    rw [Formula.realize_relabel,Formula.realize_relabel,hsource,htarget] at hm
    exact hm.symm

theorem adjoin_map_spec (p : Map L M N) (a : M) (b : N)
    (ha : a ∉ p.dom) (hb : b ∉ p.range) (hmatch : PointMatch p a b) :
    p ≤ adjoinMap p a b ha hb hmatch ∧
      (adjoinMap p a b ha hb hmatch).dom = insert a p.dom ∧
      (adjoinMap p a b ha hb hmatch).range = insert b p.range ∧
      (adjoinMap p a b ha hb hmatch).toFun ⟨a,Set.mem_insert a p.dom⟩ = b := by
  have hold (x : p.dom) : adjoinFun p a b ⟨x.val,Set.mem_insert_of_mem a x.property⟩ = p.toFun x := by
    have hx : x.val ≠ a := fun he => ha (he ▸ x.property)
    simp only [adjoinFun,dite_eq_right hx]
  refine ⟨?_,rfl,?_,?_⟩
  · intro xy hxy
    obtain ⟨hx,hval⟩ := hxy
    exact ⟨Set.mem_insert_of_mem a hx,(hold ⟨xy.1,hx⟩).trans hval⟩
  · ext y
    constructor
    · rintro ⟨x,hx⟩
      by_cases he : x.val = a
      · exact Or.inl (by simpa [adjoinMap,adjoinFun,he] using hx.symm)
      · exact Or.inr ⟨⟨x.val,(Set.mem_insert_iff.mp x.property).resolve_left he⟩,
          by simpa only [adjoinMap,adjoinFun,dite_eq_right he] using hx⟩
    · rintro (rfl | ⟨x,hx⟩)
      · exact ⟨⟨a,Set.mem_insert a p.dom⟩,by simp [adjoinMap,adjoinFun]⟩
      · exact ⟨⟨x.val,Set.mem_insert_of_mem a x.property⟩,(hold x).trans hx⟩
  · simp [adjoinMap,adjoinFun]

section Nonempty
variable [Nonempty M] [Nonempty N]

theorem transfer_small (p : Map L M N) (φ : L.Formula (p.dom ⊕ Fin 1)) (r : ℕ) :
    Small (fiber φ (Subtype.val : p.dom → M)) r ↔ Small (fiber φ p.toFun) r := by
  rw [← fiberBound_iff_small φ r,← fiberBound_iff_small φ r]
  simpa only [Function.comp_id] using (p.realize_formula (fiberBound φ r) id).symm

theorem transfer_finite (p : Map L M N) (φ : L.Formula (p.dom ⊕ Fin 1)) :
    (fiber φ (Subtype.val : p.dom → M)).Finite ↔ (fiber φ p.toFun).Finite := by
  constructor
  · intro h
    exact ((transfer_small p φ _).mp ⟨h,le_rfl⟩).1
  · intro h
    exact ((transfer_small p φ _).mpr ⟨h,le_rfl⟩).1

theorem transfer_cofinite (p : Map L M N) (φ : L.Formula (p.dom ⊕ Fin 1)) :
    Cofinite (fiber φ (Subtype.val : p.dom → M)) ↔ Cofinite (fiber φ p.toFun) := by
  simpa only [fiber_not,Cofinite] using transfer_finite p φ.not

omit [Nonempty M] [Nonempty N] in
theorem transfer_nonempty (p : Map L M N) (φ : L.Formula (p.dom ⊕ Fin 1)) :
    (fiber φ (Subtype.val : p.dom → M)).Nonempty ↔ (fiber φ p.toFun).Nonempty := by
  rw [← fiber_nonempty,← fiber_nonempty]
  simpa only [Function.comp_id] using (p.realize_formula (φ.iExs (Fin 1)) id).symm

theorem generic_point_match (p : Map L M N) (hM : Minimal L M) (a : M) (b : N)
    (ha : a ∉ acl L p.dom) (hb : b ∉ acl L p.range) : PointMatch p a b := by
  intro φ
  have hd := fiber_definable p.dom φ
  have he := mapped_fiber_definable p φ
  rcases hM.2 _ (hd.mono (Set.subset_univ _)) with hf | hf
  · have hfa : a ∉ fiber φ (Subtype.val : p.dom → M) := fun hx => ha ⟨_,hd,hf,hx⟩
    have hfb : b ∉ fiber φ p.toFun := fun hx => hb ⟨_,he,(transfer_finite p φ).mp hf,hx⟩
    exact iff_of_false hfa hfb
  · have hdn : p.dom.Definable₁ L (fiber φ (Subtype.val : p.dom → M))ᶜ := by
      rw [← fiber_not]
      exact fiber_definable p.dom φ.not
    have hen : p.range.Definable₁ L (fiber φ p.toFun)ᶜ := by
      rw [← fiber_not]
      exact mapped_fiber_definable p φ.not
    have hfa : a ∉ (fiber φ (Subtype.val : p.dom → M))ᶜ := fun hx => ha ⟨_,hdn,hf,hx⟩
    have hfb : b ∉ (fiber φ p.toFun)ᶜ := fun hx => hb ⟨_,hen,(transfer_cofinite p φ).mp hf,hx⟩
    exact iff_of_true (not_not.mp hfa) (not_not.mp hfb)

theorem generic_extension (p : Map L M N) (hM : Minimal L M) (a : M) (b : N)
    (ha : a ∉ acl L p.dom) (hb : b ∉ acl L p.range) :
    ∃ q : Map L M N, p ≤ q ∧ q.dom = insert a p.dom ∧ q.range = insert b p.range ∧
      ∃ ha' : a ∈ q.dom, q.toFun ⟨a,ha'⟩ = b := by
  have hna : a ∉ p.dom := fun hx => ha (dcl_subset_acl _ (subset_dcl _ hx))
  have hnb : b ∉ p.range := fun hx => hb (dcl_subset_acl _ (subset_dcl _ hx))
  let q := adjoinMap p a b hna hnb (generic_point_match p hM a b ha hb)
  obtain ⟨hle,hd,hr,hv⟩ := adjoin_map_spec p a b hna hnb (generic_point_match p hM a b ha hb)
  exact ⟨q,hle,hd,hr,Set.mem_insert a p.dom,hv⟩

def pointConditions (p : Map L M N) (a : M) : Set (L.Formula (p.dom ⊕ Fin 1)) :=
  {φ | φ.Realize (Sum.elim (Subtype.val : p.dom → M) (fun _ => a))}

/-- The finite original algebraic formula supplies the actual finite target candidate set. -/
theorem algebraic_candidates (p : Map L M N) (a : M) (ha : a ∈ acl L p.dom) :
    ∃ θ : L.Formula (p.dom ⊕ Fin 1), θ ∈ pointConditions p a ∧
      (fiber θ (Subtype.val : p.dom → M)).Finite ∧
      (fiber θ p.toFun).Finite ∧ (fiber θ p.toFun).Nonempty := by
  obtain ⟨S,hS,hfin,haS⟩ := ha
  obtain ⟨θ,hθ⟩ := Set.definable_iff_exists_formula_sum.mp hS
  have he : fiber θ (Subtype.val : p.dom → M) = S := by
    ext x
    have hh := Set.ext_iff.mp hθ (fun _ : Fin 1 => x)
    exact hh.symm
  have hθa : θ ∈ pointConditions p a := by
    change a ∈ fiber θ (Subtype.val : p.dom → M)
    rw [he]
    exact haS
  have hf : (fiber θ (Subtype.val : p.dom → M)).Finite := he.symm ▸ hfin
  exact ⟨θ,hθa,hf,(transfer_finite p θ).mp hf,
    (transfer_nonempty p θ).mp ⟨a,hθa⟩⟩

omit [Nonempty M] [Nonempty N] in
theorem finite_fragment_in_candidates (p : Map L M N) (a : M)
    (θ : L.Formula (p.dom ⊕ Fin 1)) (hθ : θ ∈ pointConditions p a)
    (F : Finset (L.Formula (p.dom ⊕ Fin 1))) (hF : ↑F ⊆ pointConditions p a) :
    ∃ b ∈ fiber θ p.toFun, ∀ φ ∈ F, φ.Realize (Sum.elim p.toFun (fun _ => b)) := by
  let ψ := θ ⊓ Formula.iInf (fun φ : F => φ.val)
  have hm : (fiber ψ (Subtype.val : p.dom → M)).Nonempty := by
    refine ⟨a,?_⟩
    change ψ.Realize _
    exact Formula.realize_inf.mpr ⟨hθ,Formula.realize_iInf.mpr (fun φ => hF φ.property)⟩
  obtain ⟨b,hb⟩ := (transfer_nonempty p ψ).mp hm
  obtain ⟨hθb,hFb⟩ := Formula.realize_inf.mp hb
  exact ⟨b,hθb,fun φ hφ => Formula.realize_iInf.mp hFb ⟨φ,hφ⟩⟩

omit [Nonempty M] [Nonempty N] in
theorem finite_candidates_realize_type (p : Map L M N) (a : M)
    (θ : L.Formula (p.dom ⊕ Fin 1)) (hθ : θ ∈ pointConditions p a)
    (hfin : (fiber θ p.toFun).Finite) :
    ∃ b ∈ fiber θ p.toFun, ∀ φ ∈ pointConditions p a,
      φ.Realize (Sum.elim p.toFun (fun _ => b)) := by
  by_contra hn
  have hfail : ∀ b : fiber θ p.toFun, ∃ φ ∈ pointConditions p a,
      ¬ φ.Realize (Sum.elim p.toFun (fun _ => b.val)) := by
    intro b
    by_contra h
    push Not at h
    exact hn ⟨b.val,b.property,h⟩
  choose φ hφ hbad using hfail
  let : Fintype (fiber θ p.toFun) := hfin.fintype
  let F := Finset.univ.image φ
  have hF : (F : Set (L.Formula (p.dom ⊕ Fin 1))) ⊆ pointConditions p a := by
    intro ψ hψ
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hψ
    exact hφ b
  obtain ⟨b,hb,hall⟩ := finite_fragment_in_candidates p a θ hθ F hF
  exact hbad ⟨b,hb⟩ (hall (φ ⟨b,hb⟩) (Finset.mem_image.mpr ⟨⟨b,hb⟩,Finset.mem_univ _,rfl⟩))

theorem algebraic_point_match (p : Map L M N) (a : M)
    (ha : a ∈ acl L p.dom) (hnew : a ∉ p.dom) :
    ∃ b : N, b ∈ acl L p.range ∧ b ∉ p.range ∧ PointMatch p a b := by
  obtain ⟨θ,hθ,_,hfin,_⟩ := algebraic_candidates p a ha
  obtain ⟨b,hbθ,hall⟩ := finite_candidates_realize_type p a θ hθ hfin
  have hm : PointMatch p a b := by
    intro φ
    constructor
    · exact fun h => hall φ h
    · intro h
      by_contra hn
      have ht : φ.not ∈ pointConditions p a := Formula.realize_not.mpr hn
      exact (Formula.realize_not.mp (hall φ.not ht)) h
  refine ⟨b,⟨_,mapped_fiber_definable p θ,hfin,hbθ⟩,?_,hm⟩
  rintro ⟨d,hd⟩
  let eq : L.Formula (p.dom ⊕ Fin 1) :=
    (Term.var (.inr 0)).equal (Term.var (.inl d))
  have hbEq : eq.Realize (Sum.elim p.toFun (fun _ => b)) := by
    simpa only [eq,Formula.realize_equal,Term.realize_var,Sum.elim_inr,Sum.elim_inl] using hd.symm
  have haEq := (hm eq).mpr hbEq
  have he : a = d.val := by
    simpa only [eq,Formula.realize_equal,Term.realize_var,Sum.elim_inr,Sum.elim_inl] using haEq
  exact hnew (he ▸ d.property)

theorem algebraic_extension (p : Map L M N) (a : M)
    (ha : a ∈ acl L p.dom) (hnew : a ∉ p.dom) :
    ∃ b : N, b ∈ acl L p.range ∧ b ∉ p.range ∧
      ∃ q : Map L M N, p ≤ q ∧ q.dom = insert a p.dom ∧ q.range = insert b p.range ∧
        ∃ ha' : a ∈ q.dom, q.toFun ⟨a,ha'⟩ = b := by
  obtain ⟨b,hba,hb,hm⟩ := algebraic_point_match p a ha hnew
  obtain ⟨hle,hd,hr,hv⟩ := adjoin_map_spec p a b hnew hb hm
  exact ⟨b,hba,hb,adjoinMap p a b hnew hb hm,hle,hd,hr,Set.mem_insert a p.dom,hv⟩

end Nonempty
end
end Lemmatheca.ModelTheory.StronglyMinimalModelsAndDimension
