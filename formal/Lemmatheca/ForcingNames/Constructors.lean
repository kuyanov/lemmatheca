import Lemmatheca.ForcingNames.Core

namespace Lemmatheca.SetTheory.ForcingNames
open Set Order
open scoped ZFSet
universe u v
noncomputable section
attribute [local instance] Classical.propDecidable

def CodedFilter (P R G : ZFSet.{u}) : Prop :=
  G ⊆ P ∧ G.Nonempty ∧
    (∀ p ∈ G, ∀ q ∈ P, ZFSet.pair p q ∈ R → q ∈ G) ∧
    ∀ p ∈ G, ∀ q ∈ G, ∃ r ∈ G, ZFSet.pair r p ∈ R ∧ ZFSet.pair r q ∈ R

def filterSet {Q : Type v} [PartialOrder Q] (P : ZFSet.{u}) (code : Q ≃ P)
    (G : PFilter Q) : ZFSet.{u} :=
  letI : Small.{u} Q := small_of_injective code.injective
  ZFSet.range (fun q : G => (code q.val).val)

theorem filterSet_mem {Q : Type v} [PartialOrder Q] (P : ZFSet.{u}) (code : Q ≃ P)
    (G : PFilter Q) (x : ZFSet.{u}) :
    x ∈ filterSet P code G ↔ ∃ q ∈ G, x = (code q).val := by
  let : Small.{u} Q := small_of_injective code.injective
  change x ∈ ZFSet.range (fun q : G => (code q.val).val) ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨q,he⟩
    exact ⟨q.val,q.property,he.symm⟩
  · rintro ⟨q,hq,he⟩
    exact ⟨⟨q,hq⟩,he.symm⟩

theorem coded_filter_bridge {Q : Type v} [PartialOrder Q]
    (P R : ZFSet.{u}) (code : Q ≃ P)
    (hR : ∀ q p, ZFSet.pair (code q).val (code p).val ∈ R ↔ q ≤ p) (G : PFilter Q) :
    CodedFilter P R (filterSet P code G) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨q,_,rfl⟩ := (filterSet_mem P code G x).mp hx
    exact (code q).property
  · obtain ⟨q,hq⟩ := G.nonempty
    exact ⟨(code q).val,(filterSet_mem P code G _).mpr ⟨q,hq,rfl⟩⟩
  · intro p hp q hq hpq
    obtain ⟨p',hp',rfl⟩ := (filterSet_mem P code G p).mp hp
    let q' := code.symm ⟨q,hq⟩
    have he : (code q').val = q := congrArg Subtype.val (code.apply_symm_apply _)
    have hpq' : p' ≤ q' := (hR p' q').mp (he.symm ▸ hpq)
    exact (filterSet_mem P code G q).mpr ⟨q',PFilter.mem_of_le hpq' hp',he.symm⟩
  · intro p hp q hq
    obtain ⟨p',hp',rfl⟩ := (filterSet_mem P code G p).mp hp
    obtain ⟨q',hq',rfl⟩ := (filterSet_mem P code G q).mp hq
    obtain ⟨r,hr,hrp,hrq⟩ := G.directed p' hp' q' hq'
    exact ⟨(code r).val,(filterSet_mem P code G _).mpr ⟨r,hr,rfl⟩,
      (hR r p').mpr hrp,(hR r q').mpr hrq⟩

theorem coded_filter_iff {Q : Type v} [PartialOrder Q]
    (P R G : ZFSet.{u}) (code : Q ≃ P)
    (hR : ∀ q p, ZFSet.pair (code q).val (code p).val ∈ R ↔ q ≤ p) :
    CodedFilter P R G ↔
      G ⊆ P ∧ IsPFilter {q : Q | (code q).val ∈ G} := by
  constructor
  · intro hG
    refine ⟨hG.1,IsPFilter.of_def ?_ ?_ ?_⟩
    · obtain ⟨p,hp⟩ := hG.2.1
      let q := code.symm ⟨p,hG.1 hp⟩
      have he : (code q).val = p := congrArg Subtype.val (code.apply_symm_apply _)
      refine ⟨q,?_⟩
      change (code q).val ∈ G
      rw [he]; exact hp
    · intro p hp q hq
      obtain ⟨r,hr,hrp,hrq⟩ := hG.2.2.2 (code p).val hp (code q).val hq
      let r' := code.symm ⟨r,hG.1 hr⟩
      have he : (code r').val = r := congrArg Subtype.val (code.apply_symm_apply _)
      refine ⟨r',?_,(hR r' p).mp (he.symm ▸ hrp),
        (hR r' q).mp (he.symm ▸ hrq)⟩
      change (code r').val ∈ G
      rw [he]; exact hr
    · intro p q hpq hp
      exact hG.2.2.1 (code p).val hp (code q).val (code q).property ((hR p q).mpr hpq)
  · rintro ⟨hGP,hF⟩
    let G' := hF.toPFilter
    have he : filterSet P code G' = G := by
      ext x
      rw [filterSet_mem]
      constructor
      · rintro ⟨q,hq,he⟩
        exact he ▸ hq
      · intro hx
        let q := code.symm ⟨x,hGP hx⟩
        have he : (code q).val = x := congrArg Subtype.val (code.apply_symm_apply _)
        refine ⟨q,?_,he.symm⟩
        change (code q).val ∈ G
        rw [he]; exact hx
    exact he ▸ coded_filter_bridge P R code hR G' 

theorem coded_top_mem (P R G t : ZFSet.{u}) (hG : CodedFilter P R G)
    (ht : t ∈ P) (htop : ∀ p ∈ P, ZFSet.pair p t ∈ R) : t ∈ G := by
  obtain ⟨p,hp⟩ := hG.2.1
  exact hG.2.2.1 p hp t ht (htop p (hG.1 hp))

def checkName (t : ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} :=
  ZFSet.mem_wf.fix (fun x rec =>
    ZFSet.range (fun y : x => ZFSet.pair (rec y.val y.property) t))

def genericName (P t : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun p : P => ZFSet.pair (checkName t p.val) p.val)

def pairName (t σ τ : ZFSet.{u}) : ZFSet.{u} := {ZFSet.pair σ t,ZFSet.pair τ t}

def orderedPairName (t σ τ : ZFSet.{u}) : ZFSet.{u} :=
  pairName t (pairName t σ σ) (pairName t σ τ)

def grandDomain (τ : ZFSet.{u}) : ZFSet.{u} :=
  letI := Classical.allZFSetDefinable (fun a : Fin 1 → ZFSet.{u} => domain (a 0))
  ⋃₀(ZFSet.image domain (domain τ))

def unionName (P R τ : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.prod (grandDomain τ) P).sep fun z =>
    ∃ χ r, z = ZFSet.pair χ r ∧
      ∃ π p, ZFSet.pair π p ∈ τ ∧
        ∃ q, ZFSet.pair χ q ∈ π ∧ ZFSet.pair r p ∈ R ∧ ZFSet.pair r q ∈ R

def singletonAttachment (σ p : ZFSet.{u}) : ZFSet.{u} := {ZFSet.pair σ p}

theorem checkName_mem (t x z : ZFSet.{u}) :
    z ∈ checkName t x ↔ ∃ y ∈ x, z = ZFSet.pair (checkName t y) t := by
  rw [checkName,WellFounded.fix_eq]
  change z ∈ ZFSet.range (fun y : x => ZFSet.pair (checkName t y.val) t) ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨y,he⟩
    exact ⟨y.val,y.property,he.symm⟩
  · rintro ⟨y,hy,he⟩
    exact ⟨⟨y,hy⟩,he.symm⟩

theorem checkName_isName (P t x : ZFSet.{u}) (ht : t ∈ P) :
    IsName P (checkName t x) := by
  induction x using ZFSet.inductionOn with
  | _ x ih =>
    apply (isName_iff P _).mpr
    intro z hz
    obtain ⟨y,hy,rfl⟩ := (checkName_mem t x z).mp hz
    exact ⟨checkName t y,t,rfl,ht,ih y hy⟩

theorem checkName_value (t G x : ZFSet.{u}) (ht : t ∈ G) :
    evaluation G (checkName t x) = x := by
  induction x using ZFSet.inductionOn with
  | _ x ih =>
    apply ZFSet.ext
    intro z
    rw [evaluation_mem]
    constructor
    · rintro ⟨σ,p,hsp,hp,he⟩
      obtain ⟨y,hy,he'⟩ := (checkName_mem t x _).mp hsp
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he'
      exact (he.trans (ih y hy)) ▸ hy
    · intro hz
      exact ⟨checkName t z,t,(checkName_mem t x _).mpr ⟨z,hz,rfl⟩,
        ht,(ih z hz).symm⟩

theorem genericName_isName (P t : ZFSet.{u}) (ht : t ∈ P) :
    IsName P (genericName P t) := by
  apply (isName_iff P _).mpr
  intro z hz
  obtain ⟨p,rfl⟩ := ZFSet.mem_range.mp hz
  exact ⟨checkName t p.val,p.val,rfl,p.property,checkName_isName P t p.val ht⟩

theorem genericName_value (P t G : ZFSet.{u}) (ht : t ∈ G) (hG : G ⊆ P) :
    evaluation G (genericName P t) = G := by
  apply ZFSet.ext
  intro x
  rw [evaluation_mem]
  constructor
  · rintro ⟨σ,p,hsp,hp,he⟩
    obtain ⟨q,he'⟩ := ZFSet.mem_range.mp hsp
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he'
    exact (he.trans (checkName_value t G q.val ht)) ▸ hp
  · intro hx
    exact ⟨checkName t x,x,ZFSet.mem_range_self (f := fun p : P => ZFSet.pair (checkName t p.val) p.val) ⟨x,hG hx⟩,hx,
      (checkName_value t G x ht).symm⟩

theorem pairName_isName (P t σ τ : ZFSet.{u}) (ht : t ∈ P)
    (hσ : IsName P σ) (hτ : IsName P τ) : IsName P (pairName t σ τ) := by
  apply (isName_iff P _).mpr
  intro z hz
  rcases ZFSet.mem_insert_iff.mp hz with rfl | hz
  · exact ⟨σ,t,rfl,ht,hσ⟩
  · have he := ZFSet.mem_singleton.mp hz
    subst z
    exact ⟨τ,t,rfl,ht,hτ⟩

theorem pairName_value (t G σ τ : ZFSet.{u}) (ht : t ∈ G) :
    evaluation G (pairName t σ τ) = {evaluation G σ,evaluation G τ} := by
  apply ZFSet.ext
  intro x
  simp only [evaluation_mem,pairName,ZFSet.mem_insert_iff,ZFSet.mem_singleton,ZFSet.pair_inj]
  constructor
  · rintro ⟨χ,p,(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩),_,he⟩
    · exact Or.inl he
    · exact Or.inr he
  · rintro (he | he)
    · exact ⟨σ,t,Or.inl ⟨rfl,rfl⟩,ht,he⟩
    · exact ⟨τ,t,Or.inr ⟨rfl,rfl⟩,ht,he⟩

theorem orderedPairName_isName (P t σ τ : ZFSet.{u}) (ht : t ∈ P)
    (hσ : IsName P σ) (hτ : IsName P τ) : IsName P (orderedPairName t σ τ) := by
  exact pairName_isName P t _ _ ht
    (pairName_isName P t σ σ ht hσ hσ) (pairName_isName P t σ τ ht hσ hτ)

theorem orderedPairName_value (t G σ τ : ZFSet.{u}) (ht : t ∈ G) :
    evaluation G (orderedPairName t σ τ) =
      ZFSet.pair (evaluation G σ) (evaluation G τ) := by
  simp only [orderedPairName,pairName_value t G _ _ ht,ZFSet.pair_eq_singleton,ZFSet.pair]

theorem grandDomain_mem (τ χ : ZFSet.{u}) :
    χ ∈ grandDomain τ ↔ ∃ π, Child π τ ∧ Child χ π := by
  simp only [grandDomain,ZFSet.mem_sUnion,ZFSet.mem_image]
  constructor
  · rintro ⟨z,⟨π,hπ,rfl⟩,hχ⟩
    exact ⟨π,domain_mem.mp hπ,domain_mem.mp hχ⟩
  · rintro ⟨π,hπ,hχ⟩
    exact ⟨domain π,⟨π,domain_mem.mpr hπ,rfl⟩,domain_mem.mpr hχ⟩

theorem unionName_mem (P R τ χ r : ZFSet.{u}) :
    ZFSet.pair χ r ∈ unionName P R τ ↔
      r ∈ P ∧ ∃ π p, ZFSet.pair π p ∈ τ ∧
        ∃ q, ZFSet.pair χ q ∈ π ∧ ZFSet.pair r p ∈ R ∧ ZFSet.pair r q ∈ R := by
  rw [unionName,ZFSet.mem_sep,ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨_,hrP⟩,χ',r',he,π,p,hπ,q,hχ,hrp,hrq⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hrP,π,p,hπ,q,hχ,hrp,hrq⟩
  · rintro ⟨hrP,π,p,hπ,q,hχ,hrp,hrq⟩
    refine ⟨⟨(grandDomain_mem τ χ).mpr ⟨π,⟨p,hπ⟩,⟨q,hχ⟩⟩,hrP⟩,
      χ,r,rfl,π,p,hπ,q,hχ,hrp,hrq⟩

theorem unionName_isName (P R τ : ZFSet.{u}) (hτ : IsName P τ) :
    IsName P (unionName P R τ) := by
  apply (isName_iff P _).mpr
  intro z hz
  obtain ⟨hprod,_⟩ := ZFSet.mem_sep.mp hz
  obtain ⟨χ,hχ,r,hr,rfl⟩ := ZFSet.mem_prod.mp hprod
  obtain ⟨_,π,p,hπ,q,hχπ,_,_⟩ := (unionName_mem P R τ χ r).mp hz
  obtain ⟨π',p',he,_,hπn⟩ := (isName_iff P τ).mp hτ _ hπ
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  obtain ⟨χ',q',he,_,hχn⟩ := (isName_iff P π).mp hπn _ hχπ
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact ⟨χ,r,rfl,hr,hχn⟩


private theorem empty_isName (P : ZFSet.{u}) : IsName P (∅ : ZFSet.{u}) := by
  apply (isName_iff P ∅).mpr
  intro z hz
  exact (ZFSet.notMem_empty z hz).elim

private theorem empty_evaluation (G : ZFSet.{u}) : evaluation G ∅ = ∅ := by
  ext x
  simp only [evaluation_mem,ZFSet.notMem_empty,false_and,exists_false]

private theorem singleton_evaluation (G σ p : ZFSet.{u}) :
    evaluation G (singletonAttachment σ p) = if p ∈ G then {evaluation G σ} else ∅ := by
  ext x
  simp only [evaluation_mem,singletonAttachment,ZFSet.mem_singleton,ZFSet.pair_inj]
  by_cases hp : p ∈ G
  · simp only [hp,ite_true,ZFSet.mem_singleton]
    aesop
  · simp only [hp,ite_false,ZFSet.notMem_empty]
    aesop

private theorem singleton_isName (P σ p : ZFSet.{u}) (hp : p ∈ P) (hσ : IsName P σ) :
    IsName P (singletonAttachment σ p) := by
  apply (isName_iff P _).mpr
  intro z hz
  have he := ZFSet.mem_singleton.mp hz
  subst z
  exact ⟨σ,p,rfl,hp,hσ⟩

theorem unionName_value (P R G τ : ZFSet.{u}) (hG : CodedFilter P R G)
    (hτ : IsName P τ) :
    evaluation G (unionName P R τ) = ⋃₀(evaluation G τ) := by
  apply ZFSet.ext
  intro z
  rw [evaluation_mem,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨χ,r,hu,hr,rfl⟩
    obtain ⟨_,π,p,hπ,q,hχ,hrp,hrq⟩ := (unionName_mem P R τ χ r).mp hu
    obtain ⟨π',p',he,hpP,hπn⟩ := (isName_iff P τ).mp hτ _ hπ
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    obtain ⟨χ',q',he,hqP,_⟩ := (isName_iff P π).mp hπn _ hχ
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    have hpG := hG.2.2.1 r hr p hpP hrp
    have hqG := hG.2.2.1 r hr q hqP hrq
    exact ⟨evaluation G π,(evaluation_mem G τ _).mpr ⟨π,p,hπ,hpG,rfl⟩,
      (evaluation_mem G π _).mpr ⟨χ,q,hχ,hqG,rfl⟩⟩
  · rintro ⟨y,hy,hz⟩
    obtain ⟨π,p,hπ,hpG,rfl⟩ := (evaluation_mem G τ y).mp hy
    obtain ⟨χ,q,hχ,hqG,rfl⟩ := (evaluation_mem G π z).mp hz
    obtain ⟨r,hr,hrp,hrq⟩ := hG.2.2.2 p hpG q hqG
    exact ⟨χ,r,(unionName_mem P R τ χ r).mpr
      ⟨hG.1 hr,π,p,hπ,q,hχ,hrp,hrq⟩,hr,rfl⟩

theorem extension_contains_ground (P M G t : ZFSet.{u}) (htP : t ∈ P) (htG : t ∈ G)
    (hcheck : ∀ x ∈ M, checkName t x ∈ M) : M ⊆ extension P M G := by
  intro x hx
  exact (extension_mem P M G x).mpr
    ⟨checkName t x,hcheck x hx,checkName_isName P t x htP,checkName_value t G x htG⟩

theorem generic_in_extension (P M G t : ZFSet.{u}) (htP : t ∈ P) (htG : t ∈ G)
    (hGP : G ⊆ P) (hname : genericName P t ∈ M) :
    G ∈ extension P M G := by
  exact (extension_mem P M G G).mpr
    ⟨genericName P t,hname,genericName_isName P t htP,genericName_value P t G htG hGP⟩

theorem extension_pair_closed (P M G t : ZFSet.{u}) (htP : t ∈ P) (htG : t ∈ G)
    (hpair : ∀ σ ∈ M, ∀ τ ∈ M, pairName t σ τ ∈ M) :
    ∀ x ∈ extension P M G, ∀ y ∈ extension P M G, {x,y} ∈ extension P M G := by
  intro x hx y hy
  obtain ⟨σ,hσM,hσn,rfl⟩ := (extension_mem P M G x).mp hx
  obtain ⟨τ,hτM,hτn,rfl⟩ := (extension_mem P M G y).mp hy
  exact (extension_mem P M G _).mpr ⟨pairName t σ τ,hpair σ hσM τ hτM,
    pairName_isName P t σ τ htP hσn hτn,pairName_value t G σ τ htG⟩

theorem extension_union_closed (P R M G : ZFSet.{u}) (hG : CodedFilter P R G)
    (hunion : ∀ τ ∈ M, IsName P τ → unionName P R τ ∈ M) :
    ∀ x ∈ extension P M G, ⋃₀x ∈ extension P M G := by
  intro x hx
  obtain ⟨τ,hτM,hτn,rfl⟩ := (extension_mem P M G x).mp hx
  exact (extension_mem P M G _).mpr ⟨unionName P R τ,hunion τ hτM hτn,
    unionName_isName P R τ hτn,unionName_value P R G τ hG hτn⟩

theorem extension_same_ordinals (P M G : ZFSet.{u}) (hM : M.IsTransitive)
    (hground : M ⊆ extension P M G)
    (hrank : ∀ τ ∈ M, IsName P τ → (nameRank τ).toZFSet ∈ M) :
    ∀ β : ZFSet.{u}, β.IsOrdinal → (β ∈ extension P M G ↔ β ∈ M) := by
  intro β hβ
  constructor
  · intro hβG
    obtain ⟨τ,hτM,hτn,hτβ⟩ := (extension_mem P M G β).mp hβG
    have hr : ZFSet.rank β ≤ nameRank τ := hτβ ▸ value_rank_le G τ
    have hρ := hrank τ hτM hτn
    have hord : ZFSet.IsOrdinal (nameRank τ).toZFSet := ZFSet.isOrdinal_toZFSet _
    have hsub : β ⊆ (nameRank τ).toZFSet :=
      (hβ.rank_le_iff_subset hord).mp (by simpa only [Ordinal.rank_toZFSet] using hr)
    rcases (hβ.subset_iff_eq_or_mem hord).mp hsub with he | hm
    · exact he.symm ▸ hρ
    · exact hM _ hρ hm
  · exact fun h => hground h

theorem inactive_attachment (P G p : ZFSet.{u}) (hpP : p ∈ P) (hpG : p ∉ G) :
    IsName P (∅ : ZFSet.{u}) ∧ IsName P (singletonAttachment ∅ p) ∧
    (∅ : ZFSet.{u}) ≠ singletonAttachment ∅ p ∧
    evaluation G ∅ = ∅ ∧ evaluation G (singletonAttachment ∅ p) = ∅ := by
  refine ⟨empty_isName P,singleton_isName P ∅ p hpP (empty_isName P),?_,
    empty_evaluation G,?_⟩
  · intro he
    have hm : ZFSet.pair ∅ p ∈ singletonAttachment ∅ p := by
      simp [singletonAttachment]
    rw [← he] at hm
    exact ZFSet.notMem_empty _ hm
  · rw [singleton_evaluation,ite_eq_right hpG]

theorem naive_union_counterexample (P R G t p : ZFSet.{u}) (hG : CodedFilter P R G)
    (htP : t ∈ P) (htG : t ∈ G) (hpP : p ∈ P) (hpG : p ∉ G) :
    let π := singletonAttachment ∅ t
    let τ := singletonAttachment π p
    IsName P π ∧ IsName P τ ∧ evaluation G τ = ∅ ∧
      evaluation G π = ({∅} : ZFSet.{u}) ∧
      evaluation G (unionName P R τ) = ∅ ∧ ⋃₀(evaluation G τ) = ∅ := by
  dsimp only
  have hπ := singleton_isName P ∅ t htP (empty_isName P)
  have hτ := singleton_isName P (singletonAttachment ∅ t) p hpP hπ
  have hτv : evaluation G (singletonAttachment (singletonAttachment ∅ t) p) = ∅ := by
    rw [singleton_evaluation,ite_eq_right hpG]
  have hπv : evaluation G (singletonAttachment ∅ t) = {∅} := by
    rw [singleton_evaluation,ite_eq_left htG,empty_evaluation]
  refine ⟨hπ,hτ,hτv,hπv,?_,?_⟩
  · rw [unionName_value P R G _ hG hτ,hτv,ZFSet.sUnion_empty]
  · rw [hτv,ZFSet.sUnion_empty]

end
end Lemmatheca.SetTheory.ForcingNames
