import Lemmatheca.DenseForcingPresentations.Orders
import Lemmatheca.ForcingNames.Constructors

namespace Lemmatheca.SetTheory.DenseForcingPresentations
open Set Order
open Lemmatheca.SetTheory.ForcingNames
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.WellFoundedRecursion
open scoped ZFSet
universe u
noncomputable section
local instance denseNamesPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
variable {Pset Qset : ZFSet.{u}}

private theorem child_name {A σ τ p : ZFSet.{u}} (hτ : IsName A τ)
    (hsp : ZFSet.pair σ p ∈ τ) : IsName A σ := by
  obtain ⟨σ',p',he,_,hσ⟩ := (isName_iff A τ).mp hτ _ hsp
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact hσ

private theorem condition_of_attachment {A σ τ p : ZFSet.{u}} (hτ : IsName A τ)
    (hsp : ZFSet.pair σ p ∈ τ) : p ∈ A := by
  obtain ⟨σ',p',he,hp,_⟩ := (isName_iff A τ).mp hτ _ hsp
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact hp

private theorem coded_filter_member (cP : P ≃ Pset) (G : PFilter P) (p : P) :
    (cP p).val ∈ filterSet Pset cP G ↔ p ∈ G := by
  rw [filterSet_mem]
  constructor
  · rintro ⟨q,hq,he⟩
    have hpq : p = q := cP.injective (Subtype.ext he)
    exact hpq.symm ▸ hq
  · intro hp
    exact ⟨p,hp,rfl⟩

/-- The actual set of coded conditions in the inherited suborder. -/
def suborderSet (cP : P ≃ Pset) (D : Set P) : ZFSet.{u} :=
  Pset.sep (fun x => ∃ p ∈ D, x = (cP p).val)

omit [PartialOrder P] in
theorem suborder_set_members (cP : P ≃ Pset) (D : Set P) (p : P) :
    (cP p).val ∈ suborderSet cP D ↔ p ∈ D := by
  rw [suborderSet,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,q,hq,he⟩
    have hpq : p = q := cP.injective (Subtype.ext he)
    exact hpq.symm ▸ hq
  · intro hp
    exact ⟨(cP p).property,p,hp,rfl⟩

omit [PartialOrder P] in
theorem suborder_coding_bijective (cP : P ≃ Pset) (D : Set P) :
    Function.Bijective (fun d : D => (⟨(cP d.val).val,
      (suborder_set_members cP D d.val).mpr d.property⟩ : suborderSet cP D)) := by
  constructor
  · intro d e he
    apply Subtype.ext
    apply cP.injective
    have hv : (cP d.val).val = (cP e.val).val := congrArg (fun z : suborderSet cP D => z.val) he
    exact Subtype.ext hv
  · intro z
    obtain ⟨_,p,hp,he⟩ := ZFSet.mem_sep.mp z.property
    exact ⟨⟨p,hp⟩,Subtype.ext he.symm⟩

def suborderCoding (cP : P ≃ Pset) (D : Set P) : D ≃ suborderSet cP D :=
  Equiv.ofBijective _ (suborder_coding_bijective cP D)

omit [PartialOrder P] in
theorem suborder_coding_value (cP : P ≃ Pset) (D : Set P) (d : D) :
    (suborderCoding cP D d).val = (cP d.val).val := by rfl

def rebaseRule (cP : P ≃ Pset) (cQ : Q ≃ Qset) (j : Q → P) :
    RecursionRule.{u} (Child : ZFSet.{u} → ZFSet.{u} → Prop) :=
  fun τ rec => ZFSet.range (fun sq : {sq : {σ // Child σ τ} × Q //
      ∃ p, ZFSet.pair sq.1.val (cP p).val ∈ τ ∧ j sq.2 ≤ p} =>
    ZFSet.pair (rec sq.val.1) (cQ sq.val.2).val)

/-- Refine every source attachment by every target condition below it. -/
def rebaseName (cP : P ≃ Pset) (cQ : Q ≃ Qset) (j : Q → P) : ZFSet.{u} → ZFSet.{u} :=
  recursiveValue child_wellFounded (rebaseRule cP cQ j)

omit [PartialOrder Q] in
theorem rebase_name_attachments (cP : P ≃ Pset) (cQ : Q ≃ Qset) (j : Q → P)
    (τ z : ZFSet.{u}) :
    z ∈ rebaseName cP cQ j τ ↔ ∃ σ p q,
      ZFSet.pair σ (cP p).val ∈ τ ∧ j q ≤ p ∧
        z = ZFSet.pair (rebaseName cP cQ j σ) (cQ q).val := by
  rw [rebaseName,recursiveValue,WellFounded.fix_eq]
  change z ∈ ZFSet.range (fun sq : {sq : {σ // Child σ τ} × Q //
      ∃ p, ZFSet.pair sq.1.val (cP p).val ∈ τ ∧ j sq.2 ≤ p} =>
    ZFSet.pair (rebaseName cP cQ j sq.val.1.val) (cQ sq.val.2).val) ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨sq,he⟩
    obtain ⟨p,hp,hqp⟩ := sq.property
    exact ⟨sq.val.1.val,p,sq.val.2,hp,hqp,he.symm⟩
  · rintro ⟨σ,p,q,hsp,hqp,he⟩
    exact ⟨⟨(⟨σ,⟨(cP p).val,hsp⟩⟩,q),p,hsp,hqp⟩,he.symm⟩

omit [PartialOrder Q] in
theorem rebase_name_valid (cP : P ≃ Pset) (cQ : Q ≃ Qset) (j : Q → P)
    (τ : ZFSet.{u}) (hτ : IsName Pset τ) : IsName Qset (rebaseName cP cQ j τ) := by
  induction τ using child_wellFounded.induction with
  | h τ ih =>
    apply (isName_iff Qset _).mpr
    intro z hz
    obtain ⟨σ,p,q,hsp,_,rfl⟩ := (rebase_name_attachments cP cQ j τ z).mp hz
    exact ⟨_,_,rfl,(cQ q).property,ih σ ⟨(cP p).val,hsp⟩ (child_name hτ hsp)⟩

def restrictionName (cP : P ≃ Pset) (D : Set P) : ZFSet.{u} → ZFSet.{u} :=
  rebaseName cP (suborderCoding cP D) Subtype.val

theorem restriction_name_attachments (cP : P ≃ Pset) (D : Set P) (τ z : ZFSet.{u}) :
    z ∈ restrictionName cP D τ ↔ ∃ σ p d, d ∈ D ∧
      ZFSet.pair σ (cP p).val ∈ τ ∧ d ≤ p ∧
        z = ZFSet.pair (restrictionName cP D σ) (cP d).val := by
  change z ∈ rebaseName cP (suborderCoding cP D) Subtype.val τ ↔ _
  rw [rebase_name_attachments]
  constructor
  · rintro ⟨σ,p,d,hsp,hd,he⟩
    exact ⟨σ,p,d.val,d.property,hsp,hd,by simpa only [suborder_coding_value,restrictionName] using he⟩
  · rintro ⟨σ,p,d,hd,hsp,hdp,he⟩
    exact ⟨σ,p,⟨d,hd⟩,hsp,hdp,by simpa only [suborder_coding_value,restrictionName] using he⟩

theorem restriction_name_valid (cP : P ≃ Pset) (D : Set P) (τ : ZFSet.{u})
    (hτ : IsName Pset τ) : IsName (suborderSet cP D) (restrictionName cP D τ) := by
  exact rebase_name_valid cP (suborderCoding cP D) Subtype.val τ hτ

theorem name_mono {A B : ZFSet.{u}} (hAB : A ⊆ B) (τ : ZFSet.{u})
    (hτ : IsName A τ) : IsName B τ := by
  induction τ using child_wellFounded.induction with
  | h τ ih =>
    apply (isName_iff B τ).mpr
    intro z hz
    obtain ⟨σ,p,rfl,hp,hσ⟩ := (isName_iff A τ).mp hτ z hz
    exact ⟨σ,p,rfl,hAB hp,ih σ ⟨p,hz⟩ hσ⟩

omit [PartialOrder P] in
theorem suborder_name_inclusion (cP : P ≃ Pset) (D : Set P) (τ : ZFSet.{u})
    (hτ : IsName (suborderSet cP D) τ) : IsName Pset τ := by
  exact name_mono ZFSet.sep_subset τ hτ

theorem rebase_name_value (cP : P ≃ Pset) (cQ : Q ≃ Qset) (j : Q → P)
    (G : PFilter P) (H : PFilter Q)
    (hforward : ∀ q ∈ H, j q ∈ G)
    (hcofinal : ∀ p ∈ G, ∃ q ∈ H, j q ≤ p)
    (τ : ZFSet.{u}) (hτ : IsName Pset τ) :
    evaluation (filterSet Qset cQ H) (rebaseName cP cQ j τ) =
      evaluation (filterSet Pset cP G) τ := by
  induction τ using child_wellFounded.induction with
  | h τ ih =>
    ext x
    rw [evaluation_mem,evaluation_mem]
    constructor
    · rintro ⟨θ,d,hθd,hd,hx⟩
      obtain ⟨σ,p,q,hsp,hqp,hpair⟩ := (rebase_name_attachments cP cQ j τ _).mp hθd
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hpair
      have hqH := (coded_filter_member cQ H q).mp hd
      have hpG : p ∈ G := PFilter.mem_of_le hqp (hforward q hqH)
      exact ⟨σ,(cP p).val,hsp,(coded_filter_member cP G p).mpr hpG,
        hx.trans (ih σ ⟨(cP p).val,hsp⟩ (child_name hτ hsp))⟩
    · rintro ⟨σ,p,hsp,hp,hx⟩
      have hpP := condition_of_attachment hτ hsp
      let r := cP.symm ⟨p,hpP⟩
      have hr : (cP r).val = p := congrArg Subtype.val (cP.apply_symm_apply _)
      have hrG : r ∈ G := (coded_filter_member cP G r).mp (hr.symm ▸ hp)
      obtain ⟨q,hq,hqr⟩ := hcofinal r hrG
      have hsr : ZFSet.pair σ (cP r).val ∈ τ := hr.symm ▸ hsp
      refine ⟨rebaseName cP cQ j σ,(cQ q).val,
        (rebase_name_attachments cP cQ j τ _).mpr ⟨σ,r,q,hsr,hqr,rfl⟩,
        (coded_filter_member cQ H q).mpr hq,?_⟩
      exact hx.trans (ih σ ⟨p,hsp⟩ (child_name hτ hsp)).symm

theorem restriction_name_value (cP : P ≃ Pset) (D : Set P)
    (G : PFilter P) (hc : CofinalTrace (P := P) (Q := D) (OrderEmbedding.subtype D) G)
    (τ : ZFSet.{u}) (hτ : IsName Pset τ) :
    evaluation (filterSet (suborderSet cP D) (suborderCoding cP D)
      (traceFilter (P := P) (Q := D) (OrderEmbedding.subtype D) G hc)) (restrictionName cP D τ) =
        evaluation (filterSet Pset cP G) τ := by
  apply rebase_name_value cP (suborderCoding cP D) Subtype.val G
    (traceFilter (P := P) (Q := D) (OrderEmbedding.subtype D) G hc) _ _ τ hτ
  · intro d hd
    exact (trace_filter_members _ _ _ d).mp hd
  · intro p hp
    obtain ⟨d,hd,hdp⟩ := hc p hp
    exact ⟨d,(trace_filter_members _ _ _ d).mpr hd,hdp⟩

theorem suborder_name_value (cP : P ≃ Pset) (D : Set P)
    (G : PFilter P) (hc : CofinalTrace (P := P) (Q := D) (OrderEmbedding.subtype D) G)
    (τ : ZFSet.{u}) (hτ : IsName (suborderSet cP D) τ) :
    evaluation (filterSet (suborderSet cP D) (suborderCoding cP D)
      (traceFilter (P := P) (Q := D) (OrderEmbedding.subtype D) G hc)) τ =
        evaluation (filterSet Pset cP G) τ := by
  let H := traceFilter (P := P) (Q := D) (OrderEmbedding.subtype D) G hc
  have hactive (p : ZFSet.{u}) (hp : p ∈ suborderSet cP D) :
      p ∈ filterSet (suborderSet cP D) (suborderCoding cP D) H ↔ p ∈ filterSet Pset cP G := by
    obtain ⟨_,d,hd,rfl⟩ := ZFSet.mem_sep.mp hp
    have hdcode : (suborderCoding cP D ⟨d,hd⟩).val = (cP d).val := suborder_coding_value cP D _
    rw [← hdcode,coded_filter_member,trace_filter_members,hdcode,coded_filter_member]
    rfl
  induction τ using child_wellFounded.induction with
  | h τ ih =>
    ext x
    rw [evaluation_mem,evaluation_mem]
    constructor
    · rintro ⟨σ,p,hsp,hp,hx⟩
      exact ⟨σ,p,hsp,(hactive p (condition_of_attachment hτ hsp)).mp hp,
        hx.trans (ih σ ⟨p,hsp⟩ (child_name hτ hsp))⟩
    · rintro ⟨σ,p,hsp,hp,hx⟩
      exact ⟨σ,p,hsp,(hactive p (condition_of_attachment hτ hsp)).mpr hp,
        hx.trans (ih σ ⟨p,hsp⟩ (child_name hτ hsp)).symm⟩

theorem dense_extensions_equal (cP : P ≃ Pset) (D : Set P) (M : ZFSet.{u})
    (G : PFilter P) (hc : CofinalTrace (P := P) (Q := D) (OrderEmbedding.subtype D) G)
    (hclosed : ∀ τ ∈ M, IsName Pset τ → restrictionName cP D τ ∈ M) :
    extension Pset M (filterSet Pset cP G) =
      extension (suborderSet cP D) M (filterSet (suborderSet cP D)
        (suborderCoding cP D) (traceFilter (P := P) (Q := D) (OrderEmbedding.subtype D) G hc)) := by
  ext x
  rw [extension_mem,extension_mem]
  constructor
  · rintro ⟨τ,hτ,hname,hvalue⟩
    exact ⟨restrictionName cP D τ,hclosed τ hτ hname,restriction_name_valid cP D τ hname,
      (restriction_name_value cP D G hc τ hname).trans hvalue⟩
  · rintro ⟨τ,hτ,hname,hvalue⟩
    exact ⟨τ,hτ,suborder_name_inclusion cP D τ hname,
      (suborder_name_value cP D G hc τ hname).symm.trans hvalue⟩

def pushRule (cQ : Q ≃ Qset) (cP : P ≃ Pset) (j : Q → P) :
    RecursionRule.{u} (Child : ZFSet.{u} → ZFSet.{u} → Prop) :=
  fun τ rec => ZFSet.range (fun sq : {sq : {σ // Child σ τ} × Q //
      ZFSet.pair sq.1.val (cQ sq.2).val ∈ τ} =>
    ZFSet.pair (rec sq.val.1) (cP (j sq.val.2)).val)

/-- Relabel precisely the displayed conditions, without adding refinements. -/
def pushName (cQ : Q ≃ Qset) (cP : P ≃ Pset) (j : Q → P) : ZFSet.{u} → ZFSet.{u} :=
  recursiveValue child_wellFounded (pushRule cQ cP j)

omit [PartialOrder P] [PartialOrder Q] in
theorem push_name_attachments (cQ : Q ≃ Qset) (cP : P ≃ Pset) (j : Q → P)
    (τ z : ZFSet.{u}) :
    z ∈ pushName cQ cP j τ ↔ ∃ σ q,
      ZFSet.pair σ (cQ q).val ∈ τ ∧
        z = ZFSet.pair (pushName cQ cP j σ) (cP (j q)).val := by
  rw [pushName,recursiveValue,WellFounded.fix_eq]
  change z ∈ ZFSet.range (fun sq : {sq : {σ // Child σ τ} × Q //
      ZFSet.pair sq.1.val (cQ sq.2).val ∈ τ} =>
    ZFSet.pair (pushName cQ cP j sq.val.1.val) (cP (j sq.val.2)).val) ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨sq,he⟩
    exact ⟨sq.val.1.val,sq.val.2,sq.property,he.symm⟩
  · rintro ⟨σ,q,hsp,he⟩
    exact ⟨⟨(⟨σ,⟨(cQ q).val,hsp⟩⟩,q),hsp⟩,he.symm⟩

omit [PartialOrder P] [PartialOrder Q] in
theorem push_name_valid (cQ : Q ≃ Qset) (cP : P ≃ Pset) (j : Q → P)
    (τ : ZFSet.{u}) (hτ : IsName Qset τ) : IsName Pset (pushName cQ cP j τ) := by
  induction τ using child_wellFounded.induction with
  | h τ ih =>
    apply (isName_iff Pset _).mpr
    intro z hz
    obtain ⟨σ,q,hsp,rfl⟩ := (push_name_attachments cQ cP j τ z).mp hz
    exact ⟨_,_,rfl,(cP (j q)).property,ih σ ⟨(cQ q).val,hsp⟩ (child_name hτ hsp)⟩

theorem push_name_value (cQ : Q ≃ Qset) (cP : P ≃ Pset) (j : Q → P)
    (G : PFilter P) (H : PFilter Q) (htrace : ∀ q, j q ∈ G ↔ q ∈ H)
    (τ : ZFSet.{u}) (hτ : IsName Qset τ) :
    evaluation (filterSet Pset cP G) (pushName cQ cP j τ) =
      evaluation (filterSet Qset cQ H) τ := by
  induction τ using child_wellFounded.induction with
  | h τ ih =>
    ext x
    rw [evaluation_mem,evaluation_mem]
    constructor
    · rintro ⟨θ,p,hθp,hp,hx⟩
      obtain ⟨σ,q,hsp,hpair⟩ := (push_name_attachments cQ cP j τ _).mp hθp
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hpair
      have hqH := (htrace q).mp ((coded_filter_member cP G (j q)).mp hp)
      exact ⟨σ,(cQ q).val,hsp,(coded_filter_member cQ H q).mpr hqH,
        hx.trans (ih σ ⟨(cQ q).val,hsp⟩ (child_name hτ hsp))⟩
    · rintro ⟨σ,q,hsp,hq,hx⟩
      have hqQ := condition_of_attachment hτ hsp
      let r := cQ.symm ⟨q,hqQ⟩
      have hr : (cQ r).val = q := congrArg Subtype.val (cQ.apply_symm_apply _)
      have hrH := (coded_filter_member cQ H r).mp (hr.symm ▸ hq)
      have hsr : ZFSet.pair σ (cQ r).val ∈ τ := hr.symm ▸ hsp
      exact ⟨pushName cQ cP j σ,(cP (j r)).val,
        (push_name_attachments cQ cP j τ _).mpr ⟨σ,r,hsr,rfl⟩,
        (coded_filter_member cP G (j r)).mpr ((htrace r).mpr hrH),
        hx.trans (ih σ ⟨q,hsp⟩ (child_name hτ hsp)).symm⟩

theorem embedding_extensions_equal (cQ : Q ≃ Qset) (cP : P ≃ Pset)
    (j : Q ↪o P) (M : ZFSet.{u}) (G : PFilter P) (hc : CofinalTrace j G)
    (hpush : ∀ τ ∈ M, IsName Qset τ → pushName cQ cP j τ ∈ M)
    (hpull : ∀ τ ∈ M, IsName Pset τ → rebaseName cP cQ j τ ∈ M) :
    extension Pset M (filterSet Pset cP G) =
      extension Qset M (filterSet Qset cQ (traceFilter j G hc)) := by
  let H := traceFilter j G hc
  have hforward : ∀ q ∈ H, j q ∈ G := fun q hq => (trace_filter_members j G hc q).mp hq
  have hcofinal : ∀ p ∈ G, ∃ q ∈ H, j q ≤ p := by
    intro p hp
    obtain ⟨q,hq,hqp⟩ := hc p hp
    exact ⟨q,(trace_filter_members j G hc q).mpr hq,hqp⟩
  ext x
  rw [extension_mem,extension_mem]
  constructor
  · rintro ⟨τ,hτ,hname,hvalue⟩
    exact ⟨rebaseName cP cQ j τ,hpull τ hτ hname,rebase_name_valid cP cQ j τ hname,
      (rebase_name_value cP cQ j G H hforward hcofinal τ hname).trans hvalue⟩
  · rintro ⟨τ,hτ,hname,hvalue⟩
    exact ⟨pushName cQ cP j τ,hpush τ hτ hname,push_name_valid cQ cP j τ hname,
      (push_name_value cQ cP j G H (fun q => (trace_filter_members j G hc q).symm) τ hname).trans hvalue⟩

end
end Lemmatheca.SetTheory.DenseForcingPresentations
