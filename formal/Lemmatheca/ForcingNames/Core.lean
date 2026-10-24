import Lemmatheca.ForcingAndGenericFilters.Cohen
import Lemmatheca.MostowskiCollapse.WellFoundedRecursion

namespace Lemmatheca.SetTheory.ForcingNames
open Set Order
open scoped ZFSet
open Lemmatheca.SetTheory.WellFoundedRecursion
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

def Child (σ τ : ZFSet.{u}) : Prop := ∃ p, ZFSet.pair σ p ∈ τ

def domain (τ : ZFSet.{u}) : ZFSet.{u} :=
  (⋃₀(⋃₀τ)).sep fun σ => Child σ τ


private theorem child_in_double_union {σ τ : ZFSet.{u}} (h : Child σ τ) :
    σ ∈ ⋃₀(⋃₀τ) := by
  obtain ⟨p,hp⟩ := h
  exact ZFSet.mem_sUnion.mpr ⟨{σ},ZFSet.mem_sUnion.mpr
    ⟨ZFSet.pair σ p,hp,by simp [ZFSet.pair]⟩,by simp⟩

theorem child_rank_lt {σ τ : ZFSet.{u}} (h : Child σ τ) :
    ZFSet.rank σ < ZFSet.rank τ := by
  obtain ⟨p,hp⟩ := h
  have hs : σ ∈ ({σ} : ZFSet.{u}) := by simp
  have hpair : ({σ} : ZFSet.{u}) ∈ ZFSet.pair σ p := by simp [ZFSet.pair]
  exact (ZFSet.rank_lt_of_mem hs).trans ((ZFSet.rank_lt_of_mem hpair).trans
    (ZFSet.rank_lt_of_mem hp))

theorem child_wellFounded : WellFounded (Child : ZFSet.{u} → ZFSet.{u} → Prop) := by
  exact (InvImage.wf ZFSet.rank Ordinal.lt_wf).mono
    (fun _ _ h => child_rank_lt h)

theorem child_small (τ : ZFSet.{u}) : Small.{u} {σ // Child σ τ} := by
  let f : {σ // Child σ τ} → (⋃₀(⋃₀τ) : ZFSet.{u}) :=
    fun σ => ⟨σ.val,child_in_double_union σ.property⟩
  exact small_of_injective (f := f) (fun a b h => Subtype.ext (congrArg (fun z : (⋃₀(⋃₀τ) : ZFSet.{u}) => z.val) h))

instance childSmall (τ : ZFSet.{u}) : Small.{u} {σ // Child σ τ} := child_small τ

def IsName (P : ZFSet.{u}) : ZFSet.{u} → Prop :=
  child_wellFounded.fix (fun τ rec =>
    (∀ z ∈ τ, ∃ σ p, z = ZFSet.pair σ p ∧ p ∈ P) ∧
    ∀ σ p, (h : ZFSet.pair σ p ∈ τ) → rec σ ⟨p,h⟩)

def hierarchy (P : ZFSet.{u}) : Ordinal.{u} → ZFSet.{u} :=
  Ordinal.lt_wf.fix (fun α rec =>
    ⋃₀(ZFSet.range (fun β : Set.Iio α => ZFSet.powerset (ZFSet.prod (rec β.val β.property) P))))

def nameRank : ZFSet.{u} → Ordinal.{u} :=
  child_wellFounded.fix (fun τ rec => ⨆ σ : {σ // Child σ τ}, rec σ.val σ.property + 1)

def evaluationRule (G : ZFSet.{u}) : RecursionRule.{u} (Child : ZFSet.{u} → ZFSet.{u} → Prop) :=
  fun τ rec => ZFSet.range (fun σ : {σ : {σ // Child σ τ} // ∃ p ∈ G, ZFSet.pair σ.val p ∈ τ} =>
    rec σ.val)

def evaluation (G : ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} :=
  recursiveValue child_wellFounded (evaluationRule G)

def extension (P M G : ZFSet.{u}) : ZFSet.{u} :=
  letI := Classical.allZFSetDefinable (fun a : Fin 1 → ZFSet.{u} => evaluation G (a 0))
  ZFSet.image (evaluation G) (M.sep (IsName P))

theorem domain_mem {σ τ : ZFSet.{u}} : σ ∈ domain τ ↔ Child σ τ := by
  change σ ∈ (⋃₀(⋃₀τ)).sep (fun σ => Child σ τ) ↔ Child σ τ
  rw [ZFSet.mem_sep]
  exact ⟨And.right,fun h => ⟨child_in_double_union h,h⟩⟩

theorem isName_iff (P τ : ZFSet.{u}) :
    IsName P τ ↔ ∀ z ∈ τ, ∃ σ p, z = ZFSet.pair σ p ∧ p ∈ P ∧ IsName P σ := by
  classical
  rw [IsName,WellFounded.fix_eq]
  change ((∀ z ∈ τ, ∃ σ p, z = ZFSet.pair σ p ∧ p ∈ P) ∧
    ∀ σ p, ZFSet.pair σ p ∈ τ → IsName P σ) ↔ _
  constructor
  · rintro ⟨hp,hc⟩ z hz
    obtain ⟨σ,p,rfl,hp⟩ := hp z hz
    exact ⟨σ,p,rfl,hp,hc σ p hz⟩
  · intro h
    refine ⟨?_,?_⟩
    · intro z hz
      obtain ⟨σ,p,he,hp,_⟩ := h z hz
      exact ⟨σ,p,he,hp⟩
    · intro σ p hsp
      obtain ⟨σ',p',he,_,hn⟩ := h (ZFSet.pair σ p) hsp
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      exact hn

theorem nameRank_equation (τ : ZFSet.{u}) :
    nameRank τ = ⨆ σ : {σ // Child σ τ}, nameRank σ.val + 1 := by
  rw [nameRank,WellFounded.fix_eq]

theorem nameRank_child {σ τ : ZFSet.{u}} (h : Child σ τ) :
    nameRank σ < nameRank τ := by
  rw [nameRank_equation τ]
  exact (lt_add_one (nameRank σ)).trans_le
    (Ordinal.le_iSup (fun σ : {σ // Child σ τ} => nameRank σ.val+1) ⟨σ,h⟩)


private theorem hierarchy_mem_step (P τ : ZFSet.{u}) (α : Ordinal.{u}) :
    τ ∈ hierarchy P α ↔ ∃ β < α, τ ⊆ ZFSet.prod (hierarchy P β) P := by
  rw [hierarchy,WellFoundedLT.fix_eq]
  change τ ∈ ⋃₀(ZFSet.range (fun β : Set.Iio α =>
    ZFSet.powerset (ZFSet.prod (hierarchy P β.val) P))) ↔ _
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨z,hz,hτ⟩
    obtain ⟨β,rfl⟩ := ZFSet.mem_range.mp hz
    exact ⟨β.val,β.property,ZFSet.mem_powerset.mp hτ⟩
  · rintro ⟨β,hβ,hτ⟩
    exact ⟨_,ZFSet.mem_range_self (f := fun γ : Set.Iio α =>
      ZFSet.powerset (ZFSet.prod (hierarchy P γ.val) P)) ⟨β,hβ⟩,ZFSet.mem_powerset.mpr hτ⟩

theorem hierarchy_mem (P τ : ZFSet.{u}) (α : Ordinal.{u}) :
    τ ∈ hierarchy P α ↔ IsName P τ ∧ nameRank τ < α := by
  induction α using Ordinal.lt_wf.induction generalizing τ with
  | ind α ih =>
    rw [hierarchy_mem_step]
    constructor
    · rintro ⟨β,hβα,hsub⟩
      have hc : ∀ σ p, ZFSet.pair σ p ∈ τ →
          IsName P σ ∧ nameRank σ < β ∧ p ∈ P := by
        intro σ p hsp
        obtain ⟨σ',hσ',p',hp',he⟩ := ZFSet.mem_prod.mp (hsub hsp)
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
        exact ⟨((ih β hβα σ).mp hσ').1,((ih β hβα σ).mp hσ').2,hp'⟩
      refine ⟨(isName_iff P τ).mpr ?_,?_⟩
      · intro z hz
        obtain ⟨σ,hσ,p,hp,rfl⟩ := ZFSet.mem_prod.mp (hsub hz)
        exact ⟨σ,p,rfl,hp,((ih β hβα σ).mp hσ).1⟩
      · have hr : nameRank τ ≤ β := by
          rw [nameRank_equation]
          apply Ordinal.iSup_le
          intro σ
          obtain ⟨p,hp⟩ := σ.property
          exact Order.succ_le_iff.mpr (hc σ.val p hp).2.1
        exact hr.trans_lt hβα
    · rintro ⟨hn,hr⟩
      refine ⟨nameRank τ,hr,?_⟩
      intro z hz
      obtain ⟨σ,p,rfl,hp,hσ⟩ := (isName_iff P τ).mp hn z hz
      apply ZFSet.mem_prod.mpr
      exact ⟨σ,(ih (nameRank τ) hr σ).mpr ⟨hσ,nameRank_child ⟨p,hz⟩⟩,p,hp,rfl⟩

theorem hierarchy_mono (P : ZFSet.{u}) : Monotone (hierarchy P) := by
  intro α β hαβ τ hτ
  obtain ⟨hn,hr⟩ := (hierarchy_mem P τ α).mp hτ
  exact (hierarchy_mem P τ β).mpr ⟨hn,hr.trans_le hαβ⟩

theorem hierarchy_zero (P : ZFSet.{u}) : hierarchy P 0 = ∅ := by
  ext τ
  rw [hierarchy_mem]
  simp

theorem hierarchy_succ (P : ZFSet.{u}) (α : Ordinal.{u}) :
    hierarchy P (α+1) = ZFSet.powerset (ZFSet.prod (hierarchy P α) P) := by
  ext τ
  rw [hierarchy_mem_step,ZFSet.mem_powerset]
  constructor
  · rintro ⟨β,hβ,hτ⟩ z hz
    obtain ⟨σ,hσ,p,hp,rfl⟩ := ZFSet.mem_prod.mp (hτ hz)
    exact ZFSet.mem_prod.mpr ⟨σ,hierarchy_mono P (Order.le_of_lt_succ hβ) hσ,p,hp,rfl⟩
  · intro hτ
    exact ⟨α,lt_add_one α,hτ⟩

theorem hierarchy_limit (P : ZFSet.{u}) (α : Ordinal.{u}) (hα : Order.IsSuccLimit α) :
    hierarchy P α = ⋃₀(ZFSet.range (fun β : Set.Iio α => hierarchy P β.val)) := by
  ext τ
  rw [hierarchy_mem,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨hn,hr⟩
    obtain ⟨β,hρβ,hβα⟩ := hα.lt_iff_nonempty_Ioo.mp hr
    exact ⟨hierarchy P β,ZFSet.mem_range_self (f := fun b : Set.Iio α => hierarchy P b.val) ⟨β,hβα⟩,
      (hierarchy_mem P τ β).mpr ⟨hn,hρβ⟩⟩
  · rintro ⟨z,hz,hτ⟩
    obtain ⟨β,rfl⟩ := ZFSet.mem_range.mp hz
    obtain ⟨hn,hr⟩ := (hierarchy_mem P τ β.val).mp hτ
    exact ⟨hn,hr.trans β.property⟩

theorem least_name_stage (P τ : ZFSet.{u}) (hτ : IsName P τ) :
    τ ∈ hierarchy P (nameRank τ + 1) ∧
      ∀ α : Ordinal.{u}, τ ∈ hierarchy P (α+1) → nameRank τ ≤ α := by
  refine ⟨(hierarchy_mem P τ _).mpr ⟨hτ,lt_add_one _⟩,?_⟩
  intro α hα
  exact Order.le_of_lt_succ ((hierarchy_mem P τ _).mp hα).2

theorem evaluation_mem (G τ x : ZFSet.{u}) :
    x ∈ evaluation G τ ↔
      ∃ σ p, ZFSet.pair σ p ∈ τ ∧ p ∈ G ∧ x = evaluation G σ := by
  rw [evaluation,recursiveValue,WellFounded.fix_eq]
  change x ∈ ZFSet.range (fun σ : {σ : {σ // Child σ τ} //
    ∃ p ∈ G, ZFSet.pair σ.val p ∈ τ} => evaluation G σ.val.val) ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨σ,hσ⟩,p,hp,hsp⟩,he⟩
    exact ⟨σ,p,hsp,hp,he.symm⟩
  · rintro ⟨σ,p,hsp,hp,he⟩
    exact ⟨⟨⟨σ,p,hsp⟩,p,hp,hsp⟩,he.symm⟩

theorem evaluation_unique (G : ZFSet.{u}) (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ τ x, x ∈ F τ ↔ ∃ σ p, ZFSet.pair σ p ∈ τ ∧ p ∈ G ∧ x = F σ) :
    F = evaluation G := by
  funext τ
  induction τ using child_wellFounded.induction with
  | h τ ih =>
    apply ZFSet.ext
    intro x
    rw [hF,evaluation_mem]
    constructor
    · rintro ⟨σ,p,hsp,hp,he⟩
      exact ⟨σ,p,hsp,hp,he.trans (ih σ ⟨p,hsp⟩)⟩
    · rintro ⟨σ,p,hsp,hp,he⟩
      exact ⟨σ,p,hsp,hp,he.trans (ih σ ⟨p,hsp⟩).symm⟩

theorem extension_mem (P M G x : ZFSet.{u}) :
    x ∈ extension P M G ↔ ∃ τ ∈ M, IsName P τ ∧ evaluation G τ = x := by
  simp only [extension,ZFSet.mem_image,ZFSet.mem_sep]
  constructor
  · rintro ⟨τ,⟨hτ,hn⟩,he⟩
    exact ⟨τ,hτ,hn,he⟩
  · rintro ⟨τ,hτ,hn,he⟩
    exact ⟨τ,⟨hτ,hn⟩,he⟩

theorem child_in_transitive_domain (M : ZFSet.{u}) (hM : M.IsTransitive)
    {σ τ : ZFSet.{u}} (hτ : τ ∈ M) (hchild : Child σ τ) : σ ∈ M := by
  obtain ⟨p,hp⟩ := hchild
  have hpair : ZFSet.pair σ p ∈ M := hM τ hτ hp
  have hs : ({σ} : ZFSet.{u}) ∈ M := hM _ hpair (by simp [ZFSet.pair])
  exact hM _ hs (by simp)

theorem extension_transitive (P M G : ZFSet.{u}) (hM : M.IsTransitive) :
    (extension P M G).IsTransitive := by
  intro x hx y hy
  obtain ⟨τ,hτ,hn,rfl⟩ := (extension_mem P M G x).mp hx
  obtain ⟨σ,p,hsp,hp,rfl⟩ := (evaluation_mem G τ y).mp hy
  have hσ := child_in_transitive_domain M hM hτ ⟨p,hsp⟩
  obtain ⟨σ',p',he,_,hname⟩ := (isName_iff P τ).mp hn _ hsp
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact (extension_mem P M G _).mpr ⟨σ,hσ,hname,rfl⟩

theorem extension_countable (P M G : ZFSet.{u}) (hM : (M : Set ZFSet.{u}).Countable) :
    (extension P M G : Set ZFSet.{u}).Countable := by
  apply (hM.image (evaluation G)).mono
  intro x hx
  obtain ⟨τ,hτ,_,rfl⟩ := (extension_mem P M G x).mp hx
  exact ⟨τ,hτ,rfl⟩

theorem value_rank_le (G τ : ZFSet.{u}) :
    ZFSet.rank (evaluation G τ) ≤ nameRank τ := by
  induction τ using child_wellFounded.induction with
  | h τ ih =>
    apply ZFSet.rank_le_iff.mpr
    intro x hx
    obtain ⟨σ,p,hsp,hp,rfl⟩ := (evaluation_mem G τ x).mp hx
    exact (ih σ ⟨p,hsp⟩).trans_lt (nameRank_child ⟨p,hsp⟩)

theorem nameRank_unique (F : ZFSet.{u} → Ordinal.{u})
    (hF : ∀ τ, F τ = ⨆ σ : {σ // Child σ τ}, F σ.val + 1) :
    F = nameRank := by
  funext τ
  induction τ using child_wellFounded.induction with
  | h τ ih =>
    rw [hF,nameRank_equation]
    congr 1
    funext σ
    rw [ih σ.val σ.property]

theorem namehood_partial_agree (P A : ZFSet.{u}) (hA : A.IsTransitive)
    (F : A → Prop)
    (hF : ∀ τ : A, F τ ↔ ∀ z ∈ τ.val, ∃ σ : A, ∃ p ∈ P,
      z = ZFSet.pair σ.val p ∧ F σ) :
    ∀ τ : A, F τ ↔ IsName P τ.val := by
  have hall : ∀ t : ZFSet.{u}, ∀ ht : t ∈ A, F ⟨t,ht⟩ ↔ IsName P t := by
    intro t
    induction t using child_wellFounded.induction with
    | h t ih =>
      intro ht
      rw [hF,isName_iff]
      constructor
      · intro h z hz
        obtain ⟨σ,p,hp,he,hσ⟩ := h z hz
        exact ⟨σ.val,p,he,hp,(ih σ.val ⟨p,he ▸ hz⟩ σ.property).mp hσ⟩
      · intro h z hz
        obtain ⟨σ,p,he,hp,hσ⟩ := h z hz
        have hsA := child_in_transitive_domain A hA ht ⟨p,he ▸ hz⟩
        exact ⟨⟨σ,hsA⟩,p,hp,he,(ih σ ⟨p,he ▸ hz⟩ hsA).mpr hσ⟩
  exact fun τ => hall τ.val τ.property

theorem nameRank_partial_agree (A : ZFSet.{u}) (hA : A.IsTransitive)
    (F : A → Ordinal.{u})
    (hF : ∀ τ : A, F τ = ⨆ σ : {σ : A // Child σ.val τ.val}, F σ.val + 1) :
    ∀ τ : A, F τ = nameRank τ.val := by
  have hall : ∀ t : ZFSet.{u}, ∀ ht : t ∈ A, F ⟨t,ht⟩ = nameRank t := by
    intro t
    induction t using child_wellFounded.induction with
    | h t ih =>
      intro ht
      rw [hF,nameRank_equation]
      apply le_antisymm
      · apply Ordinal.iSup_le
        intro σ
        rw [ih σ.val.val σ.property σ.val.property]
        exact Ordinal.le_iSup (fun σ : {σ // Child σ t} => nameRank σ.val+1)
          ⟨σ.val.val,σ.property⟩
      · apply Ordinal.iSup_le
        intro σ
        have hsA := child_in_transitive_domain A hA ht σ.property
        rw [← ih σ.val σ.property hsA]
        exact Ordinal.le_iSup (fun σ : {σ : A // Child σ.val t} => F σ.val+1)
          ⟨⟨σ.val,hsA⟩,σ.property⟩
  exact fun τ => hall τ.val τ.property

theorem evaluation_partial_agree (G A : ZFSet.{u}) (hA : A.IsTransitive)
    (F : A → ZFSet.{u})
    (hF : ∀ (τ : A) x, x ∈ F τ ↔
      ∃ σ : A, ∃ p ∈ G, ZFSet.pair σ.val p ∈ τ.val ∧ x = F σ) :
    ∀ τ : A, F τ = evaluation G τ.val := by
  have hall : ∀ t : ZFSet.{u}, ∀ ht : t ∈ A, F ⟨t,ht⟩ = evaluation G t := by
    intro t
    induction t using child_wellFounded.induction with
    | h t ih =>
      intro ht
      apply ZFSet.ext
      intro x
      rw [hF,evaluation_mem]
      constructor
      · rintro ⟨σ,p,hp,hsp,he⟩
        exact ⟨σ.val,p,hsp,hp,he.trans (ih σ.val ⟨p,hsp⟩ σ.property)⟩
      · rintro ⟨σ,p,hsp,hp,he⟩
        have hsA := child_in_transitive_domain A hA ht ⟨p,hsp⟩
        exact ⟨⟨σ,hsA⟩,p,hp,hsp,he.trans (ih σ ⟨p,hsp⟩ hsA).symm⟩
  exact fun τ => hall τ.val τ.property


end
end Lemmatheca.SetTheory.ForcingNames
