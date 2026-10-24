import Lemmatheca.ForcingTheorem.ForcingTheorem
import Lemmatheca.CumulativeHierarchy.CumulativeHierarchy

namespace Lemmatheca.SetTheory.ForcingExtensions
open FirstOrder FirstOrder.Language Set Order
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
open Lemmatheca.SetTheory.ForcingNames
open Lemmatheca.SetTheory.ForcingTheorem
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.NaturalNumbersAsSets
open scoped ZFSet
universe u v
noncomputable section
attribute [local instance] Classical.propDecidable

def mapSlots : {n m : ℕ} → membershipLanguage.BoundedFormula Empty n →
    (Fin n → Fin m) → membershipLanguage.BoundedFormula Empty m
  | _, _, .falsum, _ => .falsum
  | _, _, .equal t s, f => .equal (.var (.inr (f (termSlot t)))) (.var (.inr (f (termSlot s))))
  | _, _, .rel r ts, f => .rel r (fun i => .var (.inr (f (termSlot (ts i)))))
  | _, _, .imp φ ψ, f => .imp (mapSlots φ f) (mapSlots ψ f)
  | _n, m, .all φ, f => .all (mapSlots φ (Fin.snoc (fun i => (f i).castSucc) (Fin.last m)))

def placeOne {n} (φ : membershipLanguage.BoundedFormula Empty (n+1))
    (k : ℕ) (x : Fin (n+k)) : membershipLanguage.BoundedFormula Empty (n+k) :=
  mapSlots φ (Fin.lastCases x (Fin.castAdd k))

def placeTwo {n} (φ : membershipLanguage.BoundedFormula Empty (n+2))
    (k : ℕ) (x y : Fin (n+k)) : membershipLanguage.BoundedFormula Empty (n+k) :=
  mapSlots φ (Fin.lastCases y (Fin.lastCases x (Fin.castAdd k)))

def OrdinaryHolds (D : ZFSet.{u}) (φ : membershipLanguage.Sentence) : Prop :=
  letI := actualMembershipStructure D
  D ⊨ φ

theorem mapSlots_realize (D : ZFSet.{u}) {n m}
    (φ : membershipLanguage.BoundedFormula Empty n) (f : Fin n → Fin m) (a : Fin m → D) :
    setSatisfies D (mapSlots φ f) a ↔ setSatisfies D φ (fun i => a (f i)) := by
  let := actualMembershipStructure D
  change (mapSlots φ f).Realize Empty.elim a ↔ φ.Realize Empty.elim (a ∘ f)
  induction φ generalizing m with
  | falsum => rfl
  | equal t s =>
    simp only [mapSlots,BoundedFormula.Realize,Term.realize,Sum.elim_inr,termSlot_realize,Function.comp_apply]
  | rel R ts =>
    cases R
    simp only [mapSlots,BoundedFormula.Realize,Term.realize,Sum.elim_inr,termSlot_realize,Function.comp_apply]
  | imp φ ψ ihφ ihψ =>
    exact (ihφ f a).imp (ihψ f a)
  | @all n φ ih =>
    simp only [mapSlots,BoundedFormula.realize_all]
    apply forall_congr'
    intro x
    have he : (Fin.snoc a x) ∘ Fin.snoc (fun i => (f i).castSucc) (Fin.last m) =
        Fin.snoc (a ∘ f) x := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    exact (ih _ (Fin.snoc a x)).trans (by rw [he])

private theorem shared_mem (D : ZFSet.{u}) {n} (i j : Fin n) (a : Fin n → D) :
    setSatisfies D (memScoped i j) a ↔ (a i).val ∈ (a j).val := Iff.rfl

private theorem shared_equal (D : ZFSet.{u}) {n} (i j : Fin n) (a : Fin n → D) :
    setSatisfies D (.equal (.var (.inr i)) (.var (.inr j))) a ↔ a i = a j := Iff.rfl

private theorem shared_and (D : ZFSet.{u}) {n}
    (φ ψ : membershipLanguage.BoundedFormula Empty n) (a : Fin n → D) :
    setSatisfies D (φ ⊓ ψ) a ↔ setSatisfies D φ a ∧ setSatisfies D ψ a := by
  let := actualMembershipStructure D
  exact BoundedFormula.realize_inf

private theorem shared_iff (D : ZFSet.{u}) {n}
    (φ ψ : membershipLanguage.BoundedFormula Empty n) (a : Fin n → D) :
    setSatisfies D (φ.iff ψ) a ↔ (setSatisfies D φ a ↔ setSatisfies D ψ a) := by
  let := actualMembershipStructure D
  exact BoundedFormula.realize_iff

private theorem shared_imp (D : ZFSet.{u}) {n}
    (φ ψ : membershipLanguage.BoundedFormula Empty n) (a : Fin n → D) :
    setSatisfies D (φ.imp ψ) a ↔ (setSatisfies D φ a → setSatisfies D ψ a) := Iff.rfl

private theorem shared_all (D : ZFSet.{u}) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+1)) (a : Fin n → D) :
    setSatisfies D φ.all a ↔ ∀ x : D, setSatisfies D φ (Fin.snoc a x) := Iff.rfl

private theorem shared_ex (D : ZFSet.{u}) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+1)) (a : Fin n → D) :
    setSatisfies D φ.ex a ↔ ∃ x : D, setSatisfies D φ (Fin.snoc a x) := by
  let := actualMembershipStructure D
  exact BoundedFormula.realize_ex

private theorem ordinary_alls (D : ZFSet.{u}) {n}
    (φ : membershipLanguage.BoundedFormula Empty n) :
    OrdinaryHolds D φ.alls ↔ ∀ a : Fin n → D, setSatisfies D φ a := by
  let := actualMembershipStructure D
  change Formula.Realize φ.alls default ↔ _
  rw [BoundedFormula.realize_alls]
  rw [show (default : Empty → D) = Empty.elim from Subsingleton.elim _ _]
  rfl

private theorem placeOne_truth (D : ZFSet.{u}) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+1))
    (k : ℕ) (x : Fin (n+k)) (a : Fin (n+k) → D) :
    setSatisfies D (placeOne φ k x) a ↔
      setSatisfies D φ (Fin.snoc (fun i => a (i.castAdd k)) (a x)) := by
  rw [placeOne,mapSlots_realize]
  have he : (fun i : Fin (n+1) => a (Fin.lastCases x (Fin.castAdd k) i)) =
      Fin.snoc (fun i => a (i.castAdd k)) (a x) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [he]

private theorem placeTwo_truth (D : ZFSet.{u}) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+2))
    (k : ℕ) (x y : Fin (n+k)) (a : Fin (n+k) → D) :
    setSatisfies D (placeTwo φ k x y) a ↔
      setSatisfies D φ (Fin.snoc (Fin.snoc (fun i => a (i.castAdd k)) (a x)) (a y)) := by
  rw [placeTwo,mapSlots_realize]
  have he : (fun i : Fin (n+2) => a (Fin.lastCases y (Fin.lastCases x (Fin.castAdd k)) i)) =
      Fin.snoc (Fin.snoc (fun i => a (i.castAdd k)) (a x)) (a y) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun l => ?_) j <;> simp
  rw [he]

private theorem castAdd_succ {n} (k) (i : Fin n) : i.castAdd (k+1) = (i.castAdd k).castSucc := rfl
private theorem castAdd_zero {n} (i : Fin n) : i.castAdd 0 = i := rfl

private theorem powerFormula_set (D : ZFSet.{u}) (hD : D.IsTransitive)
    {n} (p x : Fin n) (a : Fin n → D) :
    setSatisfies D (powerSetFormula p x) a ↔
      ∀ z : D, z.val ∈ (a p).val ↔ z.val ⊆ (a x).val := by
  let := actualMembershipStructure D
  change ((memScoped (Fin.last n) p.castSucc).iff
    (subsetTest (Fin.last n) x.castSucc).toShared).all.Realize Empty.elim a ↔ _
  rw [BoundedFormula.realize_all]
  apply forall_congr'
  intro z
  rw [BoundedFormula.realize_iff]
  have hm : (memScoped (Fin.last n) p.castSucc).Realize Empty.elim (Fin.snoc a z) ↔
      z.val ∈ (a p).val := by
    change (Fin.snoc (α := fun _ : Fin (n+1) => D) a z (Fin.last n)).val ∈
      (Fin.snoc (α := fun _ : Fin (n+1) => D) a z p.castSucc).val ↔ _
    simp only [Fin.snoc_last,Fin.snoc_castSucc]
  rw [hm]
  change (z.val ∈ (a p).val ↔ setSatisfies D
    (subsetTest (Fin.last n) x.castSucc).toShared (Fin.snoc a z)) ↔ _
  rw [bounded_to_universe D hD,subsetTest_correct]
  simp only [Fin.snoc_last,Fin.snoc_castSucc]


def separationMatrix {n} (φ : membershipLanguage.BoundedFormula Empty (n+1)) :
    membershipLanguage.BoundedFormula Empty (n+2) :=
  (memScoped (Fin.last (n+1)) (Fin.last n).castSucc) ⊓
    placeOne φ 2 (Fin.last (n+1))

def separationSentence {n} (φ : membershipLanguage.BoundedFormula Empty (n+1)) :
    membershipLanguage.Sentence :=
  (((memScoped (Fin.last (n+2)) (Fin.last (n+1)).castSucc).iff
    ((memScoped (Fin.last (n+2)) (Fin.last n).castSucc.castSucc) ⊓
      placeOne φ 3 (Fin.last (n+2)))).all.ex.all).alls

theorem separationMatrix_realize (D : ZFSet.{u}) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+1))
    (a : Fin n → D) (σ π : D) :
    setSatisfies D (separationMatrix φ) (Fin.snoc (Fin.snoc a σ) π) ↔
      π.val ∈ σ.val ∧ setSatisfies D φ (Fin.snoc a π) := by
  simp only [separationMatrix,shared_and,shared_mem,placeOne_truth,
    castAdd_succ,castAdd_zero,Fin.snoc_last,Fin.snoc_castSucc]

theorem separationSentence_realize (D : ZFSet.{u}) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+1)) :
    OrdinaryHolds D (separationSentence φ) ↔
      ∀ a : Fin n → D, ∀ x : D, ∃ y : D, ∀ z : D,
        z.val ∈ y.val ↔ z.val ∈ x.val ∧ setSatisfies D φ (Fin.snoc a z) := by
  rw [separationSentence,ordinary_alls]
  simp only [shared_all,shared_ex,shared_iff,shared_and,shared_mem,placeOne_truth,
    castAdd_succ,castAdd_zero,Fin.snoc_last,Fin.snoc_castSucc]

variable {Q : Type v} [PartialOrder Q]

def separationName (C : Context.{u,v} Q) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+1))
    (a : Fin n → C.Name) (σ : C.Name) : ZFSet.{u} :=
  (ZFSet.prod (domain σ.val) C.conditions).sep (fun z =>
    ∃ π : C.Name, ∃ p : Q, z = ZFSet.pair π.val (C.code p).val ∧
      C.semanticForce (separationMatrix φ) (Fin.snoc (Fin.snoc a σ) π) p)

def selectedSubset (C : Context.{u,v} Q) (G : PFilter Q) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+1))
    (a : Fin n → C.Name) (σ : C.Name) : ZFSet.{u} :=
  (C.value G σ).val.sep (fun x => ∃ hx : x ∈ C.valueDomain G,
    setSatisfies (C.valueDomain G) φ (Fin.snoc (C.valueAssignment G a) ⟨x,hx⟩))


private theorem name_value_member (C : Context.{u,v} Q) (G : PFilter Q)
    (x : ZFSet.{u}) (τ : C.Name) :
    x ∈ (C.value G τ).val ↔ ∃ θ q, Attached C θ τ q ∧ q ∈ G ∧ x = (C.value G θ).val := by
  change x ∈ evaluation (C.filterCode G) τ.val ↔ _
  rw [evaluation_mem]
  constructor
  · rintro ⟨σ,p,hσp,hp,he⟩
    obtain ⟨q,hq,rfl⟩ := (filterSet_mem C.conditions C.code G p).mp hp
    obtain ⟨σ',p',hpair,_,hn⟩ := (isName_iff C.conditions τ.val).mp τ.property.2 _ hσp
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hpair
    have hσM := child_in_transitive_domain C.ground C.transitive τ.property.1 ⟨(C.code q).val,hσp⟩
    exact ⟨⟨σ,hσM,hn⟩,q,hσp,hq,he⟩
  · rintro ⟨θ,q,hθ,hq,he⟩
    exact ⟨θ.val,(C.code q).val,hθ,(filterSet_mem C.conditions C.code G _).mpr
      ⟨q,hq,rfl⟩,he⟩

private theorem name_value_surjective (C : Context.{u,v} Q) (G : PFilter Q)
    (x : C.valueDomain G) : ∃ σ : C.Name, C.value G σ = x := by
  obtain ⟨τ,hτ,hn,he⟩ := (extension_mem C.conditions C.ground (C.filterCode G) x.val).mp x.property
  exact ⟨⟨τ,hτ,hn⟩,Subtype.ext he⟩

private theorem assignment_snoc (C : Context.{u,v} Q) (G : PFilter Q) {n}
    (a : Fin n → C.Name) (σ : C.Name) :
    C.valueAssignment G (Fin.snoc a σ) = Fin.snoc (C.valueAssignment G a) (C.value G σ) :=
  Fin.comp_snoc (C.value G) a σ

private theorem bounded_subname_valid (C : Context.{u,v} Q) (σ : C.Name) (τ : ZFSet.{u})
    (hτ : τ ⊆ ZFSet.prod (domain σ.val) C.conditions) : IsName C.conditions τ := by
  apply (isName_iff C.conditions τ).mpr
  intro z hz
  obtain ⟨π,hπ,p,hp,rfl⟩ := ZFSet.mem_prod.mp (hτ hz)
  obtain ⟨q,hq⟩ := domain_mem.mp hπ
  obtain ⟨π',q',he,_,hn⟩ := (isName_iff C.conditions σ.val).mp σ.property.2 _ hq
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact ⟨π,p,rfl,hp,hn⟩

theorem separationName_members (C : Context.{u,v} Q) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+1))
    (a : Fin n → C.Name) (σ π : C.Name) (p : Q) :
    ZFSet.pair π.val (C.code p).val ∈ separationName C φ a σ ↔
      Child π.val σ.val ∧ C.semanticForce (separationMatrix φ) (Fin.snoc (Fin.snoc a σ) π) p := by
  rw [separationName,ZFSet.mem_sep,ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hπ,_⟩,π',p',he,hforce⟩
    obtain ⟨heπ,hep⟩ := ZFSet.pair_inj.mp he
    have hπ' : π' = π := Subtype.ext heπ.symm
    have hp' : p' = p := C.code.injective (Subtype.ext hep.symm)
    subst π'; subst p'
    exact ⟨domain_mem.mp hπ,hforce⟩
  · rintro ⟨hπ,hforce⟩
    exact ⟨⟨domain_mem.mpr hπ,(C.code p).property⟩,π,p,rfl,hforce⟩


theorem separationName_valid (C : Context.{u,v} Q) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+1))
    (a : Fin n → C.Name) (σ : C.Name) :
    IsName C.conditions (separationName C φ a σ) := by
  exact bounded_subname_valid C σ _ (fun _ hz => (ZFSet.mem_sep.mp hz).1)


theorem separationName_value (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (G : PFilter Q) (hG : GenericFor G C.groundFamily) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+1))
    (a : Fin n → C.Name) (σ : C.Name) :
    evaluation (C.filterCode G) (separationName C φ a σ) = selectedSubset C G φ a σ := by
  ext x
  rw [evaluation_mem,selectedSubset,ZFSet.mem_sep]
  constructor
  · rintro ⟨π,p,hpair,hp,he⟩
    obtain ⟨_,θ,q,hθ,hforce⟩ := ZFSet.mem_sep.mp hpair
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hθ
    obtain ⟨q',hq',hqq⟩ := (filterSet_mem C.conditions C.code G _).mp hp
    have hq : q = q' := C.code.injective (Subtype.ext hqq)
    subst q'
    have ht := hforce G hG hq'
    rw [assignment_snoc,assignment_snoc] at ht
    obtain ⟨hmem,hφ⟩ := (separationMatrix_realize _ φ _ _ _).mp ht
    refine ⟨he ▸ hmem,?_,?_⟩
    · exact he ▸ (C.value G θ).property
    · have hval : C.value G θ = (⟨x,he ▸ (C.value G θ).property⟩ : C.valueDomain G) := Subtype.ext he.symm
      exact hval ▸ hφ
  · rintro ⟨hx,hxD,hφ⟩
    obtain ⟨π,q,hπ,hq,he⟩ := (name_value_member C G x σ).mp hx
    have hπx : C.value G π = (⟨x,hxD⟩ : C.valueDomain G) := Subtype.ext he.symm
    have ht : setSatisfies (C.valueDomain G) (separationMatrix φ)
        (C.valueAssignment G (Fin.snoc (Fin.snoc a σ) π)) := by
      rw [assignment_snoc,assignment_snoc,separationMatrix_realize]
      exact ⟨he ▸ hx,hπx.symm ▸ hφ⟩
    obtain ⟨r,hr,hrf⟩ := (ordinary_truth C hC G hG _ _).mp ht
    obtain ⟨p,hp,hpq,hpr⟩ := G.directed q hq r hr
    refine ⟨π.val,(C.code p).val,?_,(filterSet_mem _ _ _ _).mpr ⟨p,hp,rfl⟩,he⟩
    exact (separationName_members C φ a σ π p).mpr
      ⟨⟨(C.code q).val,hπ⟩,semantic_monotone C _ _ hpr hrf⟩


def SeparationNamesClosed (C : Context.{u,v} Q) : Prop :=
  ∀ n (φ : membershipLanguage.BoundedFormula Empty (n+1))
    (a : Fin n → C.Name) (σ : C.Name), separationName C φ a σ ∈ C.ground

theorem extension_separation (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (hclose : SeparationNamesClosed C) (G : PFilter Q)
    (hG : GenericFor G C.groundFamily) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+1)) :
    OrdinaryHolds (C.valueDomain G) (separationSentence φ) := by
  apply (separationSentence_realize _ φ).mpr
  intro a x
  choose b hb using fun i => name_value_surjective C G (a i)
  obtain ⟨σ,hσ⟩ := name_value_surjective C G x
  have ha : C.valueAssignment G b = a := funext hb
  let τ : C.Name := ⟨separationName C φ b σ,hclose n φ b σ,separationName_valid C φ b σ⟩
  refine ⟨C.value G τ,?_⟩
  intro z
  change z.val ∈ evaluation (C.filterCode G) (separationName C φ b σ) ↔ _
  rw [separationName_value C hC G hG,selectedSubset,ZFSet.mem_sep]
  rw [ha,hσ]
  constructor
  · rintro ⟨hz,hzD,hφ⟩
    exact ⟨hz,hφ⟩
  · rintro ⟨hz,hφ⟩
    exact ⟨hz,z.property,hφ⟩


def relevantIndices (I : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  I.sep (fun i => ∃ y, R i y)

def leastWitnessStage (R : ZFSet.{u} → ZFSet.{u} → Prop) (i : ZFSet.{u}) : Ordinal.{u} :=
  sInf {α | ∃ y ∈ ZFSet.vonNeumann α, R i y}

def collectionBound (I : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop) : Ordinal.{u} :=
  ⨆ i : relevantIndices I R, leastWitnessStage R i.val

def collectedWitnesses (I : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  (ZFSet.vonNeumann (collectionBound I R)).sep (fun y => ∃ i ∈ relevantIndices I R, R i y)

theorem leastWitnessStage_spec (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (i : ZFSet.{u}) (h : ∃ y, R i y) :
    (∃ y ∈ ZFSet.vonNeumann (leastWitnessStage R i), R i y) ∧
      ∀ α, (∃ y ∈ ZFSet.vonNeumann α, R i y) → leastWitnessStage R i ≤ α := by
  have hne : {α : Ordinal.{u} | ∃ y ∈ ZFSet.vonNeumann α, R i y}.Nonempty := by
    obtain ⟨y,hy⟩ := h
    exact ⟨ZFSet.rank y+1,y,ZFSet.mem_vonNeumann.mpr (lt_add_one _),hy⟩
  exact ⟨csInf_mem hne,fun α hα => csInf_le ⟨0,fun _ _ => bot_le⟩ hα⟩

theorem collectedWitnesses_members (I : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop) (y) :
    y ∈ collectedWitnesses I R ↔ y ∈ ZFSet.vonNeumann (collectionBound I R) ∧
      ∃ i ∈ I, (∃ z, R i z) ∧ R i y := by
  simp only [collectedWitnesses,ZFSet.mem_sep,relevantIndices]
  simp only [and_assoc]

theorem collection_exact_bound (I : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop) :
    ∀ i ∈ I, (∃ y, R i y) → ∃ y ∈ collectedWitnesses I R, R i y := by
  intro i hi h
  obtain ⟨y,hy,hr⟩ := (leastWitnessStage_spec R i h).1
  have hii : i ∈ relevantIndices I R := ZFSet.mem_sep.mpr ⟨hi,h⟩
  have hb : leastWitnessStage R i ≤ collectionBound I R :=
    Ordinal.le_iSup (fun j : relevantIndices I R => leastWitnessStage R j.val) ⟨i,hii⟩
  exact ⟨y,(collectedWitnesses_members I R y).mpr
    ⟨ZFSet.vonNeumann_strictMono.monotone hb hy,i,hi,h,hr⟩,hr⟩

def topProductName [OrderTop Q] (C : Context.{u,v} Q) (S : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod S {(C.code ⊤).val}

def nameValues (C : Context.{u,v} Q) (G : PFilter Q) (S : ZFSet.{u}) : ZFSet.{u} :=
  letI := Classical.allZFSetDefinable (fun a : Fin 1 → ZFSet.{u} => evaluation (C.filterCode G) (a 0))
  ZFSet.image (evaluation (C.filterCode G)) S

private theorem coded_top_in_filter [OrderTop Q] (C : Context.{u,v} Q) (G : PFilter Q) :
    (C.code ⊤).val ∈ C.filterCode G := by
  exact (filterSet_mem C.conditions C.code G _).mpr ⟨⊤,PFilter.top_mem,rfl⟩

private theorem attached_child_name (P σ τ : ZFSet.{u}) (hτ : IsName P τ)
    (hσ : Child σ τ) : IsName P σ := by
  obtain ⟨p,hp⟩ := hσ
  obtain ⟨σ',p',he,_,hname⟩ := (isName_iff P τ).mp hτ _ hp
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact hname



theorem topProductName_valid [OrderTop Q] (C : Context.{u,v} Q) (S : ZFSet.{u})
    (hS : ∀ μ ∈ S, IsName C.conditions μ) : IsName C.conditions (topProductName C S) := by
  apply (isName_iff C.conditions _).mpr
  intro z hz
  obtain ⟨μ,hμ,p,hp,rfl⟩ := ZFSet.mem_prod.mp hz
  have he : p = (C.code ⊤).val := ZFSet.mem_singleton.mp hp
  subst p
  exact ⟨μ,(C.code ⊤).val,rfl,(C.code ⊤).property,hS μ hμ⟩

theorem topProductName_value [OrderTop Q] (C : Context.{u,v} Q) (G : PFilter Q) (S : ZFSet.{u}) :
    evaluation (C.filterCode G) (topProductName C S) = nameValues C G S := by
  let := Classical.allZFSetDefinable (fun a : Fin 1 → ZFSet.{u} => evaluation (C.filterCode G) (a 0))
  ext x
  rw [evaluation_mem]
  change _ ↔ x ∈ ZFSet.image (evaluation (C.filterCode G)) S
  rw [ZFSet.mem_image]
  constructor
  · rintro ⟨μ,p,hμp,hp,he⟩
    obtain ⟨hμ,hpt⟩ := ZFSet.pair_mem_prod.mp hμp
    exact ⟨μ,hμ,he.symm⟩
  · rintro ⟨μ,hμ,he⟩
    exact ⟨μ,(C.code ⊤).val,ZFSet.pair_mem_prod.mpr ⟨hμ,ZFSet.mem_singleton.mpr rfl⟩,
      coded_top_in_filter C G,he.symm⟩

def CollectedNames (C : Context.{u,v} Q) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+2))
    (a : Fin n → C.Name) (σ : C.Name) (S : ZFSet.{u}) : Prop :=
  (∀ μ ∈ S, μ ∈ C.ground ∧ IsName C.conditions μ) ∧
    ∀ π : C.Name, Child π.val σ.val → ∀ p,
      (∃ μ : C.Name, C.semanticForce φ (Fin.snoc (Fin.snoc a π) μ) p) →
      ∃ μ : C.Name, μ.val ∈ S ∧ C.semanticForce φ (Fin.snoc (Fin.snoc a π) μ) p

def FunctionalOn (C : Context.{u,v} Q) (G : PFilter Q) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+2))
    (a : Fin n → C.Name) (σ : C.Name) : Prop :=
  ∀ x : C.valueDomain G, x.val ∈ (C.value G σ).val →
    ∃! y : C.valueDomain G, setSatisfies (C.valueDomain G) φ
      (Fin.snoc (Fin.snoc (C.valueAssignment G a) x) y)

theorem replacement_bound [OrderTop Q] (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (G : PFilter Q) (hG : GenericFor G C.groundFamily) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+2))
    (a : Fin n → C.Name) (σ : C.Name) (S : ZFSet.{u})
    (hS : CollectedNames C φ a σ S) (hfun : FunctionalOn C G φ a σ) :
    ∀ x y : C.valueDomain G, x.val ∈ (C.value G σ).val →
      setSatisfies (C.valueDomain G) φ (Fin.snoc (Fin.snoc (C.valueAssignment G a) x) y) →
        y.val ∈ evaluation (C.filterCode G) (topProductName C S) := by
  intro x y hx hφ
  obtain ⟨π,q,hπ,hq,he⟩ := (name_value_member C G x.val σ).mp hx
  have hπx : C.value G π = x := Subtype.ext he.symm
  obtain ⟨μ,hμ⟩ := name_value_surjective C G y
  have ht : setSatisfies (C.valueDomain G) φ
      (C.valueAssignment G (Fin.snoc (Fin.snoc a π) μ)) := by
    rw [assignment_snoc,assignment_snoc,hπx,hμ]
    exact hφ
  obtain ⟨p,hp,hforce⟩ := (ordinary_truth C hC G hG φ _).mp ht
  obtain ⟨ν,hν,hνf⟩ := hS.2 π ⟨(C.code q).val,hπ⟩ p ⟨μ,hforce⟩
  have hνφ := hνf G hG hp
  rw [assignment_snoc,assignment_snoc,hπx] at hνφ
  obtain ⟨w,hw,huniq⟩ := hfun x hx
  have hνy : C.value G ν = y := (huniq _ hνφ).trans (huniq _ hφ).symm
  rw [← hνy]
  let := Classical.allZFSetDefinable (fun a : Fin 1 → ZFSet.{u} => evaluation (C.filterCode G) (a 0))
  rw [topProductName_value]
  exact ZFSet.mem_image.mpr ⟨ν.val,hν,rfl⟩


def rangeMatrix {n} (φ : membershipLanguage.BoundedFormula Empty (n+2)) :
    membershipLanguage.BoundedFormula Empty (n+2) :=
  ((memScoped (Fin.last (n+2)) (Fin.last n).castSucc.castSucc) ⊓
    placeTwo φ 3 (Fin.last (n+2)) (Fin.last (n+1)).castSucc).ex

def functionalityMatrix {n} (φ : membershipLanguage.BoundedFormula Empty (n+2)) :
    membershipLanguage.BoundedFormula Empty (n+1) :=
  ((memScoped (Fin.last (n+1)) (Fin.last n).castSucc).imp
    ((placeTwo φ 3 (Fin.last (n+1)).castSucc (Fin.last (n+2))) ⊓
      ((placeTwo φ 4 (Fin.last (n+1)).castSucc.castSucc (Fin.last (n+3))).imp
        (.equal (.var (.inr (Fin.last (n+3)))) (.var (.inr (Fin.last (n+2)).castSucc)))).all).ex).all

def replacementSentence {n} (φ : membershipLanguage.BoundedFormula Empty (n+2)) :
    membershipLanguage.Sentence :=
  ((functionalityMatrix φ).imp
    (((memScoped (Fin.last (n+2)) (Fin.last (n+1)).castSucc).iff
      ((memScoped (Fin.last (n+3)) (Fin.last n).castSucc.castSucc.castSucc) ⊓
        placeTwo φ 4 (Fin.last (n+3)) (Fin.last (n+2)).castSucc).ex).all.ex)).alls

theorem rangeMatrix_realize (D : ZFSet.{u}) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+2))
    (a : Fin n → D) (σ y : D) :
    setSatisfies D (rangeMatrix φ) (Fin.snoc (Fin.snoc a σ) y) ↔
      ∃ x : D, x.val ∈ σ.val ∧ setSatisfies D φ (Fin.snoc (Fin.snoc a x) y) := by
  simp only [rangeMatrix,shared_ex,shared_and,shared_mem,placeTwo_truth,
    castAdd_succ,castAdd_zero,Fin.snoc_last,Fin.snoc_castSucc]

theorem replacementSentence_realize (D : ZFSet.{u}) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+2)) :
    OrdinaryHolds D (replacementSentence φ) ↔
      ∀ a : Fin n → D, ∀ σ : D,
        (∀ x : D, x.val ∈ σ.val → ∃! y : D, setSatisfies D φ (Fin.snoc (Fin.snoc a x) y)) →
        ∃ Y : D, ∀ y : D, y.val ∈ Y.val ↔
          ∃ x : D, x.val ∈ σ.val ∧ setSatisfies D φ (Fin.snoc (Fin.snoc a x) y) := by
  rw [replacementSentence,ordinary_alls]
  simp only [shared_imp,shared_all,shared_ex,shared_iff,shared_and,shared_mem,
    functionalityMatrix,placeTwo_truth,shared_equal,castAdd_succ,castAdd_zero,
    Fin.snoc_last,Fin.snoc_castSucc,ExistsUnique]
  constructor
  · intro h a σ
    simpa only [Fin.snoc_last,Fin.snoc_castSucc] using h (Fin.snoc a σ)
  · intro h a
    exact h (fun i => a i.castSucc) (a (Fin.last n))

def replacementRangeName (C : Context.{u,v} Q) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+2))
    (a : Fin n → C.Name) (σ B : C.Name) : ZFSet.{u} :=
  separationName C (rangeMatrix φ) (Fin.snoc a σ) B

theorem replacementRangeName_value (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (G : PFilter Q) (hG : GenericFor G C.groundFamily) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+2))
    (a : Fin n → C.Name) (σ B : C.Name)
    (hbound : ∀ x y : C.valueDomain G, x.val ∈ (C.value G σ).val →
      setSatisfies (C.valueDomain G) φ (Fin.snoc (Fin.snoc (C.valueAssignment G a) x) y) →
        y.val ∈ (C.value G B).val) :
    ∀ y : C.valueDomain G,
      y.val ∈ evaluation (C.filterCode G) (replacementRangeName C φ a σ B) ↔
        ∃ x : C.valueDomain G, x.val ∈ (C.value G σ).val ∧
          setSatisfies (C.valueDomain G) φ (Fin.snoc (Fin.snoc (C.valueAssignment G a) x) y) := by
  intro y
  rw [replacementRangeName,separationName_value C hC G hG,selectedSubset,ZFSet.mem_sep]
  rw [assignment_snoc]
  constructor
  · rintro ⟨_,hyD,hy⟩
    exact (rangeMatrix_realize _ φ _ _ _).mp hy
  · rintro ⟨x,hx,hφ⟩
    exact ⟨hbound x y hx hφ,y.property,(rangeMatrix_realize _ φ _ _ _).mpr ⟨x,hx,hφ⟩⟩


def ReplacementBoundsClosed [OrderTop Q] (C : Context.{u,v} Q) : Prop :=
  ∀ n (φ : membershipLanguage.BoundedFormula Empty (n+2))
    (a : Fin n → C.Name) (σ : C.Name),
    ∃ S ∈ C.ground, CollectedNames C φ a σ S ∧ topProductName C S ∈ C.ground

theorem extension_replacement [OrderTop Q] (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (hsep : SeparationNamesClosed C) (hcoll : ReplacementBoundsClosed C)
    (G : PFilter Q) (hG : GenericFor G C.groundFamily) {n}
    (φ : membershipLanguage.BoundedFormula Empty (n+2)) :
    OrdinaryHolds (C.valueDomain G) (replacementSentence φ) := by
  apply (replacementSentence_realize _ φ).mpr
  intro a x hfun
  choose b hb using fun i => name_value_surjective C G (a i)
  obtain ⟨σ,hσ⟩ := name_value_surjective C G x
  have ha : C.valueAssignment G b = a := funext hb
  have hf : FunctionalOn C G φ b σ := by simpa only [FunctionalOn,ha,hσ] using hfun
  obtain ⟨S,hSM,hS,hBM⟩ := hcoll n φ b σ
  let B : C.Name := ⟨topProductName C S,hBM,topProductName_valid C S (fun μ hμ => (hS.1 μ hμ).2)⟩
  have hbound := replacement_bound C hC G hG φ b σ S hS hf
  let Y : C.Name := ⟨replacementRangeName C φ b σ B,
    hsep (n+1) (rangeMatrix φ) (Fin.snoc b σ) B,
    separationName_valid C (rangeMatrix φ) (Fin.snoc b σ) B⟩
  refine ⟨C.value G Y,?_⟩
  intro y
  have hv := replacementRangeName_value C hC G hG φ b σ B hbound y
  change y.val ∈ evaluation (C.filterCode G) (replacementRangeName C φ b σ B) ↔ _
  rw [← ha,← hσ]
  exact hv


def InternalPowerSet (M A Q : ZFSet.{u}) : Prop :=
  Q ∈ M ∧ ∀ τ, τ ∈ Q ↔ τ ∈ M ∧ τ ⊆ A

def restrictionName (C : Context.{u,v} Q) (σ μ : C.Name) : ZFSet.{u} :=
  (ZFSet.prod (domain σ.val) C.conditions).sep (fun z =>
    ∃ π : C.Name, ∃ p : Q, z = ZFSet.pair π.val (C.code p).val ∧
      C.semanticForce (memScoped (0 : Fin 2) 1) ![π,μ] p)

theorem restrictionName_subset (C : Context.{u,v} Q) (σ μ : C.Name) :
    restrictionName C σ μ ⊆ ZFSet.prod (domain σ.val) C.conditions := by
  exact fun _ hz => (ZFSet.mem_sep.mp hz).1


theorem restrictionName_valid (C : Context.{u,v} Q) (σ μ : C.Name) :
    IsName C.conditions (restrictionName C σ μ) := by
  exact bounded_subname_valid C σ _ (restrictionName_subset C σ μ)


theorem restrictionName_value (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (G : PFilter Q) (hG : GenericFor G C.groundFamily) (σ μ : C.Name)
    (hsub : (C.value G μ).val ⊆ (C.value G σ).val) :
    evaluation (C.filterCode G) (restrictionName C σ μ) = (C.value G μ).val := by
  ext x
  rw [evaluation_mem]
  constructor
  · rintro ⟨π,p,hpair,hp,he⟩
    obtain ⟨_,θ,q,hθ,hforce⟩ := ZFSet.mem_sep.mp hpair
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hθ
    obtain ⟨q',hq',hqq⟩ := (filterSet_mem C.conditions C.code G _).mp hp
    have hq : q = q' := C.code.injective (Subtype.ext hqq)
    subst q'
    have ht := hforce G hG hq'
    change (C.value G θ).val ∈ (C.value G μ).val at ht
    exact he ▸ ht
  · intro hx
    obtain ⟨π,q,hπ,hq,he⟩ := (name_value_member C G x σ).mp (hsub hx)
    have ht : setSatisfies (C.valueDomain G) (memScoped (0 : Fin 2) 1)
        (C.valueAssignment G ![π,μ]) := by
      change (C.value G π).val ∈ (C.value G μ).val
      exact he ▸ hx
    obtain ⟨r,hr,hrf⟩ := (ordinary_truth C hC G hG _ _).mp ht
    obtain ⟨p,hp,hpq,hpr⟩ := G.directed q hq r hr
    refine ⟨π.val,(C.code p).val,?_,(filterSet_mem _ _ _ _).mpr ⟨p,hp,rfl⟩,he⟩
    exact ZFSet.mem_sep.mpr ⟨ZFSet.pair_mem_prod.mpr
      ⟨domain_mem.mpr ⟨(C.code q).val,hπ⟩,(C.code p).property⟩,
      π,p,rfl,semantic_monotone C _ _ hpr hrf⟩


theorem powerBound_valid [OrderTop Q] (C : Context.{u,v} Q) (σ : C.Name)
    (A : ZFSet.{u}) (hA : InternalPowerSet C.ground (ZFSet.prod (domain σ.val) C.conditions) A) :
    (∀ τ ∈ A, IsName C.conditions τ) ∧ IsName C.conditions (topProductName C A) := by
  have hnames : ∀ τ ∈ A, IsName C.conditions τ := by
    intro τ hτ
    exact bounded_subname_valid C σ τ ((hA.2 τ).mp hτ).2
  exact ⟨hnames,topProductName_valid C A hnames⟩


theorem power_bound [OrderTop Q] (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (G : PFilter Q) (hG : GenericFor G C.groundFamily) (σ : C.Name)
    (A : ZFSet.{u}) (hA : InternalPowerSet C.ground (ZFSet.prod (domain σ.val) C.conditions) A)
    (hrest : ∀ μ : C.Name, restrictionName C σ μ ∈ C.ground) :
    ∀ y : C.valueDomain G, y.val ⊆ (C.value G σ).val →
      y.val ∈ evaluation (C.filterCode G) (topProductName C A) := by
  intro y hy
  obtain ⟨μ,rfl⟩ := name_value_surjective C G y
  let := Classical.allZFSetDefinable (fun a : Fin 1 → ZFSet.{u} => evaluation (C.filterCode G) (a 0))
  rw [topProductName_value]
  change _ ∈ ZFSet.image (evaluation (C.filterCode G)) A
  rw [ZFSet.mem_image]
  refine ⟨restrictionName C σ μ,?_,?_⟩
  · exact (hA.2 _).mpr ⟨hrest μ,restrictionName_subset C σ μ⟩
  · exact restrictionName_value C hC G hG σ μ hy


def powerSetName (C : Context.{u,v} Q) (σ B : C.Name) : ZFSet.{u} :=
  separationName C (subsetTest (1 : Fin 2) 0).toShared ![σ] B

theorem powerSetName_value (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (G : PFilter Q) (hG : GenericFor G C.groundFamily) (σ B : C.Name)
    (hbound : ∀ y : C.valueDomain G, y.val ⊆ (C.value G σ).val → y.val ∈ (C.value G B).val) :
    ∀ y : ZFSet.{u}, y ∈ evaluation (C.filterCode G) (powerSetName C σ B) ↔
      y ∈ C.valueDomain G ∧ y ⊆ (C.value G σ).val := by
  have hD : (C.valueDomain G).IsTransitive := extension_transitive C.conditions C.ground (C.filterCode G) C.transitive
  intro y
  rw [powerSetName,separationName_value C hC G hG,selectedSubset,ZFSet.mem_sep]
  constructor
  · rintro ⟨hy,hyD,hφ⟩
    rw [bounded_to_universe _ hD,subsetTest_correct] at hφ
    exact ⟨hyD,hφ⟩
  · rintro ⟨hyD,hsub⟩
    refine ⟨hbound ⟨y,hyD⟩ hsub,hyD,?_⟩
    rw [bounded_to_universe _ hD,subsetTest_correct]
    exact hsub


def powerSetSentence : membershipLanguage.Sentence := (powerSetFormula (1 : Fin 2) 0).ex.all

theorem powerSetSentence_realize (D : ZFSet.{u}) (hD : D.IsTransitive) :
    OrdinaryHolds D powerSetSentence ↔ ∀ x ∈ D, ∃ p ∈ D,
      ∀ y ∈ D, y ∈ p ↔ y ⊆ x := by
  let := actualMembershipStructure D
  change ((powerSetFormula (1 : Fin 2) 0).ex.all).Realize Empty.elim Fin.elim0 ↔ _
  simp only [BoundedFormula.realize_all,BoundedFormula.realize_ex]
  change (∀ x : D, ∃ p : D, setSatisfies D (powerSetFormula (1 : Fin 2) 0)
    (Fin.snoc (Fin.snoc Fin.elim0 x) p)) ↔ _
  simp only [powerFormula_set D hD,
    show (1 : Fin 2) = Fin.last 1 from rfl,
    show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl,
    show (0 : Fin 1) = Fin.last 0 from rfl,
    Fin.snoc_last,Fin.snoc_castSucc]
  constructor
  · intro h x hx
    obtain ⟨p,hp⟩ := h ⟨x,hx⟩
    exact ⟨p.val,p.property,fun y hy => hp ⟨y,hy⟩⟩
  · intro h x
    obtain ⟨p,hp,hpx⟩ := h x.val x.property
    exact ⟨⟨p,hp⟩,fun y => hpx y.val y.property⟩

def PowerBoundsClosed [OrderTop Q] (C : Context.{u,v} Q) : Prop :=
  ∀ σ : C.Name, ∃ A : ZFSet.{u},
    InternalPowerSet C.ground (ZFSet.prod (domain σ.val) C.conditions) A ∧
      topProductName C A ∈ C.ground ∧ ∀ μ : C.Name, restrictionName C σ μ ∈ C.ground

theorem extension_power_set [OrderTop Q] (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (hsep : SeparationNamesClosed C) (hpow : PowerBoundsClosed C)
    (G : PFilter Q) (hG : GenericFor G C.groundFamily) :
    OrdinaryHolds (C.valueDomain G) powerSetSentence := by
  apply (powerSetSentence_realize _ (extension_transitive _ _ _ C.transitive)).mpr
  intro x hx
  obtain ⟨σ,hσ⟩ := name_value_surjective C G ⟨x,hx⟩
  obtain ⟨A,hA,hBM,hrest⟩ := hpow σ
  let B : C.Name := ⟨topProductName C A,hBM,(powerBound_valid C σ A hA).2⟩
  have hbound := power_bound C hC G hG σ A hA hrest
  let Y : C.Name := ⟨powerSetName C σ B,
    hsep 1 (subsetTest (1 : Fin 2) 0).toShared ![σ] B,
    separationName_valid C _ ![σ] B⟩
  refine ⟨(C.value G Y).val,(C.value G Y).property,?_⟩
  intro y hy
  have hv := powerSetName_value C hC G hG σ B hbound y
  change y ∈ evaluation (C.filterCode G) (powerSetName C σ B) ↔ _
  have hxval : (C.value G σ).val = x := congrArg Subtype.val hσ
  rw [hxval] at hv
  exact ⟨fun h => (hv.mp h).2,fun h => hv.mpr ⟨hy,h⟩⟩


def enumerationName [OrderTop Q] (C : Context.{u,v} Q) (σ : C.Name)
    (α : Ordinal.{u}) (e : α.toZFSet ≃ domain σ.val) : ZFSet.{u} :=
  ZFSet.range (fun γ : α.toZFSet =>
    ZFSet.pair (orderedPairName (C.code ⊤).val
      (checkName (C.code ⊤).val γ.val) (e γ).val) (C.code ⊤).val)

def enumerationGraph (C : Context.{u,v} Q) (G : PFilter Q) (σ : C.Name)
    (α : Ordinal.{u}) (e : α.toZFSet ≃ domain σ.val) : ZFSet.{u} :=
  ZFSet.range (fun γ : α.toZFSet =>
    ZFSet.pair γ.val (evaluation (C.filterCode G) (e γ).val))

theorem enumerationName_valid [OrderTop Q] (C : Context.{u,v} Q) (σ : C.Name)
    (α : Ordinal.{u}) (e : α.toZFSet ≃ domain σ.val) :
    IsName C.conditions (enumerationName C σ α e) := by
  apply (isName_iff C.conditions _).mpr
  intro z hz
  obtain ⟨γ,rfl⟩ := ZFSet.mem_range.mp hz
  exact ⟨_,(C.code ⊤).val,rfl,(C.code ⊤).property,
    orderedPairName_isName C.conditions _ _ _ (C.code ⊤).property
      (checkName_isName C.conditions _ _ (C.code ⊤).property)
      (attached_child_name C.conditions (e γ).val σ.val σ.property.2
        (domain_mem.mp (e γ).property))⟩

theorem enumerationName_value [OrderTop Q] (C : Context.{u,v} Q) (G : PFilter Q)
    (σ : C.Name) (α : Ordinal.{u}) (e : α.toZFSet ≃ domain σ.val) :
    evaluation (C.filterCode G) (enumerationName C σ α e) = enumerationGraph C G σ α e := by
  have hv (γ : α.toZFSet) : evaluation (C.filterCode G)
      (orderedPairName (C.code ⊤).val (checkName (C.code ⊤).val γ.val) (e γ).val) =
      ZFSet.pair γ.val (evaluation (C.filterCode G) (e γ).val) := by
    rw [orderedPairName_value _ _ _ _ (coded_top_in_filter C G),
      checkName_value _ _ _ (coded_top_in_filter C G)]
  ext z
  rw [evaluation_mem,enumerationGraph,ZFSet.mem_range]
  constructor
  · rintro ⟨π,p,hπp,hp,he⟩
    obtain ⟨γ,hγ⟩ := ZFSet.mem_range.mp hπp
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hγ
    exact ⟨γ,(he.trans (hv γ)).symm⟩
  · rintro ⟨γ,rfl⟩
    exact ⟨_,(C.code ⊤).val,ZFSet.mem_range_self (f := fun δ : α.toZFSet =>
      ZFSet.pair (orderedPairName (C.code ⊤).val (checkName (C.code ⊤).val δ.val) (e δ).val)
        (C.code ⊤).val) γ,coded_top_in_filter C G,(hv γ).symm⟩

theorem enumerationGraph_function (C : Context.{u,v} Q) (G : PFilter Q)
    (σ : C.Name) (α : Ordinal.{u}) (e : α.toZFSet ≃ domain σ.val) :
    ZFSet.IsFunc α.toZFSet (C.valueDomain G) (enumerationGraph C G σ α e) := by
  refine ⟨?_,?_⟩
  · intro p hp
    obtain ⟨γ,rfl⟩ := ZFSet.mem_range.mp hp
    have hc : Child (e γ).val σ.val := domain_mem.mp (e γ).property
    have hn : IsName C.conditions (e γ).val := attached_child_name _ _ _ σ.property.2 hc
    have hm : (e γ).val ∈ C.ground := child_in_transitive_domain _ C.transitive σ.property.1 hc
    exact ZFSet.pair_mem_prod.mpr ⟨γ.property,(extension_mem _ _ _ _).mpr ⟨_,hm,hn,rfl⟩⟩
  · intro z hz
    refine ⟨evaluation (C.filterCode G) (e ⟨z,hz⟩).val,?_,?_⟩
    · exact ZFSet.mem_range_self (f := fun γ : α.toZFSet =>
        ZFSet.pair γ.val (evaluation (C.filterCode G) (e γ).val)) ⟨z,hz⟩
    · intro w hw
      obtain ⟨γ,hγ⟩ := ZFSet.mem_range.mp hw
      obtain ⟨he,hw⟩ := ZFSet.pair_inj.mp hγ
      have he' : γ = ⟨z,hz⟩ := Subtype.ext he
      exact hw.symm.trans (congrArg (fun δ : α.toZFSet => evaluation (C.filterCode G) (e δ).val) he')

theorem enumerationGraph_covers (C : Context.{u,v} Q) (G : PFilter Q)
    (σ : C.Name) (α : Ordinal.{u}) (e : α.toZFSet ≃ domain σ.val) :
    ∀ x ∈ (C.value G σ).val, ∃ γ ∈ α.toZFSet, ZFSet.pair γ x ∈ enumerationGraph C G σ α e := by
  intro x hx
  obtain ⟨π,p,hπp,hp,he⟩ := (evaluation_mem (C.filterCode G) σ.val x).mp hx
  let γ := e.symm ⟨π,domain_mem.mpr ⟨p,hπp⟩⟩
  have hγ : (e γ).val = π := congrArg Subtype.val (e.apply_symm_apply _)
  refine ⟨γ.val,γ.property,ZFSet.mem_range.mpr ⟨γ,?_⟩⟩
  rw [hγ,← he]

theorem enumerationGraph_in_extension [OrderTop Q] (C : Context.{u,v} Q) (G : PFilter Q)
    (σ : C.Name) (α : Ordinal.{u}) (e : α.toZFSet ≃ domain σ.val)
    (hname : enumerationName C σ α e ∈ C.ground) :
    enumerationGraph C G σ α e ∈ C.valueDomain G := by
  exact (extension_mem _ _ _ _).mpr ⟨enumerationName C σ α e,hname,
    enumerationName_valid C σ α e,enumerationName_value C G σ α e⟩

def leastPreimage (α : Ordinal.{u}) (f : α.toZFSet → ZFSet.{u}) (z : ZFSet.{u}) : Ordinal.{u} :=
  sInf {β | ∃ h : β < α, f ⟨β.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr h⟩ = z}

theorem leastPreimage_spec (α : Ordinal.{u}) (f : α.toZFSet → ZFSet.{u}) (z : ZFSet.{u})
    (hz : ∃ γ : α.toZFSet, f γ = z) :
    (∃ h : leastPreimage α f z < α,
      f ⟨(leastPreimage α f z).toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr h⟩ = z) ∧
      ∀ γ : α.toZFSet, f γ = z → leastPreimage α f z ≤ ZFSet.rank γ.val := by
  have hne : {β : Ordinal.{u} | ∃ h : β < α,
      f ⟨β.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr h⟩ = z}.Nonempty := by
    obtain ⟨γ,hγ⟩ := hz
    obtain ⟨β,hβ,he⟩ := Ordinal.mem_toZFSet_iff.mp γ.property
    refine ⟨β,hβ,?_⟩
    have hh : (⟨β.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hβ⟩ : α.toZFSet) = γ := Subtype.ext he
    exact hh.symm ▸ hγ
  refine ⟨csInf_mem hne,?_⟩
  intro γ hγ
  obtain ⟨β,hβ,he⟩ := Ordinal.mem_toZFSet_iff.mp γ.property
  have hh : (⟨β.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hβ⟩ : α.toZFSet) = γ := Subtype.ext he
  have hb : leastPreimage α f z ≤ β :=
    csInf_le ⟨0,fun _ _ => bot_le⟩ ⟨hβ,hh.symm ▸ hγ⟩
  simpa only [← he,Ordinal.rank_toZFSet] using hb

def leastPreimageGraph (x : ZFSet.{u}) (α : Ordinal.{u})
    (f : α.toZFSet → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun z : x => ZFSet.pair z.val (leastPreimage α f z.val).toZFSet)

def preimageWellOrder (x : ZFSet.{u}) (α : Ordinal.{u})
    (f : α.toZFSet → ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.prod x x).sep (fun zw => ∃ z ∈ x, ∃ w ∈ x,
    zw = ZFSet.pair z w ∧ leastPreimage α f z < leastPreimage α f w)

theorem leastPreimage_injective (x : ZFSet.{u}) (α : Ordinal.{u})
    (f : α.toZFSet → ZFSet.{u}) (hcover : ∀ z ∈ x, ∃ γ : α.toZFSet, f γ = z) :
    Function.Injective (fun z : x => leastPreimage α f z.val) := by
  intro z w h
  obtain ⟨hz,hfz⟩ := (leastPreimage_spec α f z.val (hcover z.val z.property)).1
  obtain ⟨hw,hfw⟩ := (leastPreimage_spec α f w.val (hcover w.val w.property)).1
  have he : (⟨(leastPreimage α f z.val).toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hz⟩ : α.toZFSet) =
      ⟨(leastPreimage α f w.val).toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hw⟩ :=
    Subtype.ext (congrArg Ordinal.toZFSet h)
  exact Subtype.ext (hfz.symm.trans ((congrArg f he).trans hfw))

theorem leastPreimageGraph_function (x : ZFSet.{u}) (α : Ordinal.{u})
    (f : α.toZFSet → ZFSet.{u}) (hcover : ∀ z ∈ x, ∃ γ : α.toZFSet, f γ = z) :
    ZFSet.IsFunc x α.toZFSet (leastPreimageGraph x α f) := by
  refine ⟨?_,?_⟩
  · intro p hp
    obtain ⟨z,rfl⟩ := ZFSet.mem_range.mp hp
    exact ZFSet.pair_mem_prod.mpr ⟨z.property,Ordinal.toZFSet_mem_toZFSet_iff.mpr
      ((leastPreimage_spec α f z.val (hcover z.val z.property)).1.choose)⟩
  · intro z hz
    refine ⟨(leastPreimage α f z).toZFSet,?_,?_⟩
    · exact ZFSet.mem_range_self (f := fun w : x => ZFSet.pair w.val (leastPreimage α f w.val).toZFSet) ⟨z,hz⟩
    · intro w hw
      obtain ⟨z',he⟩ := ZFSet.mem_range.mp hw
      obtain ⟨hz',hw'⟩ := ZFSet.pair_inj.mp he
      simpa only [hz'] using hw'.symm

theorem preimageWellOrder_correct (x : ZFSet.{u}) (α : Ordinal.{u})
    (f : α.toZFSet → ZFSet.{u}) (z w : x) :
    ZFSet.pair z.val w.val ∈ preimageWellOrder x α f ↔
      leastPreimage α f z.val < leastPreimage α f w.val := by
  rw [preimageWellOrder,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,a,ha,b,hb,he,hr⟩
    obtain ⟨he1,he2⟩ := ZFSet.pair_inj.mp he
    simpa only [he1,he2] using hr
  · intro h
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨z.property,w.property⟩,z.val,z.property,w.val,w.property,rfl,h⟩

theorem preimageWellOrder_isWellOrder (x : ZFSet.{u}) (α : Ordinal.{u})
    (f : α.toZFSet → ZFSet.{u}) (hcover : ∀ z ∈ x, ∃ γ : α.toZFSet, f γ = z) :
    IsWellOrder x (fun z w => ZFSet.pair z.val w.val ∈ preimageWellOrder x α f) := by
  let : IsWellOrder Ordinal.{u} ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop) :=
    { wf := Ordinal.lt_wf, trichotomous := fun a b hab hba =>
        le_antisymm (le_of_not_gt hba) (le_of_not_gt hab) }
  let e : x → Ordinal.{u} := fun z => leastPreimage α f z.val
  have he := leastPreimage_injective x α f hcover
  have hw := he.isWellOrder (· < ·)
  have hr : (fun z w : x => ZFSet.pair z.val w.val ∈ preimageWellOrder x α f) =
      ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop).onFun e := by
    funext z w
    exact propext (preimageWellOrder_correct x α f z w)
  rw [hr]
  exact hw

def ClassTransitive (N : ZFSet.{u} → Prop) : Prop :=
  ∀ x, N x → ∀ y ∈ x, N y

theorem class_evaluation_agreement (N : ZFSet.{u} → Prop) (hN : ClassTransitive N)
    (G : ZFSet.{u}) (F : {τ // N τ} → {x // N x})
    (hF : ∀ (τ : {τ // N τ}) x, x ∈ (F τ).val ↔
      ∃ σ : {σ // N σ}, ∃ p ∈ G, ZFSet.pair σ.val p ∈ τ.val ∧ x = (F σ).val) :
    ∀ τ : {τ // N τ}, (F τ).val = evaluation G τ.val := by
  have hchild {σ τ : ZFSet.{u}} (hτ : N τ) (h : Child σ τ) : N σ := by
    obtain ⟨p,hp⟩ := h
    have hpair := hN τ hτ _ hp
    have hs := hN _ hpair ({σ} : ZFSet.{u}) (by simp [ZFSet.pair])
    exact hN _ hs σ (by simp)
  have hall : ∀ t : ZFSet.{u}, ∀ ht : N t, (F ⟨t,ht⟩).val = evaluation G t := by
    intro t
    induction t using child_wellFounded.induction with
    | h t ih =>
      intro ht
      apply ZFSet.ext
      intro x
      rw [hF,evaluation_mem]
      constructor
      · rintro ⟨σ,p,hp,hσp,he⟩
        exact ⟨σ.val,p,hσp,hp,he.trans (ih σ.val ⟨p,hσp⟩ σ.property)⟩
      · rintro ⟨σ,p,hσp,hp,he⟩
        have hs := hchild ht ⟨p,hσp⟩
        exact ⟨⟨σ,hs⟩,p,hp,hσp,he.trans (ih σ ⟨p,hσp⟩ hs).symm⟩
  exact fun τ => hall τ.val τ.property

theorem minimality_with_recursion (C : Context.{u,v} Q) (G : PFilter Q)
    (N : ZFSet.{u} → Prop) (hN : ClassTransitive N)
    (hM : ∀ x ∈ C.ground, N x) (F : {τ // N τ} → {x // N x})
    (hF : ∀ (τ : {τ // N τ}) x, x ∈ (F τ).val ↔
      ∃ σ : {σ // N σ}, ∃ p ∈ C.filterCode G,
        ZFSet.pair σ.val p ∈ τ.val ∧ x = (F σ).val) :
    ∀ x ∈ C.valueDomain G, N x := by
  intro x hx
  obtain ⟨τ,hτ,hn,hvalue⟩ := (extension_mem _ _ _ x).mp hx
  have ht : N τ := hM τ hτ
  have he := class_evaluation_agreement N hN (C.filterCode G) F hF ⟨τ,ht⟩
  exact (he.trans hvalue) ▸ (F ⟨τ,ht⟩).property

def binarySubset (f : ℕ → Bool) : ZFSet.{u} :=
  ZFSet.omega.sep (fun x => ∃ n, f n = true ∧ naturalSet n = x)

theorem binarySubset_subset (f : ℕ → Bool) : binarySubset.{u} f ⊆ ZFSet.omega := by
  exact fun _ h => (ZFSet.mem_sep.mp h).1

theorem binarySubset_injective : Function.Injective (binarySubset.{u}) := by
  have hnat : Function.Injective (naturalSet.{u}) := by
    intro m n h
    exact Nat.le_antisymm ((naturalSet_order m n).2.mp (fun _ hz => h ▸ hz))
      ((naturalSet_order n m).2.mp (fun _ hz => h.symm ▸ hz))
  have hb (f : ℕ → Bool) (n : ℕ) : naturalSet.{u} n ∈ binarySubset f ↔ f n = true := by
    rw [binarySubset,ZFSet.mem_sep]
    constructor
    · rintro ⟨_,m,hm,he⟩
      have hmn := hnat he
      subst m
      exact hm
    · intro hf
      exact ⟨(omega_members _).mpr ⟨n,rfl⟩,n,hf,rfl⟩
  intro f g he
  funext n
  have hbit : f n = true ↔ g n = true := by
    rw [← hb f n,he,hb g n]
  cases hf : f n <;> cases hg : g n <;> simp_all

theorem missing_ambient_subset (D : ZFSet.{u}) (hD : (D : Set ZFSet.{u}).Countable) :
    ∃ S : ZFSet.{u}, S ⊆ ZFSet.omega ∧ S ∉ D := by
  classical
  by_contra h
  push Not at h
  let : Countable D := hD.to_subtype
  let : Encodable D := Encodable.ofCountable D
  let bits (s : Set ℕ) : ℕ → Bool := fun n => decide (n ∈ s)
  let F (s : Set ℕ) : D := ⟨binarySubset.{u} (bits s),h _ (binarySubset_subset _)⟩
  have hi : Function.Injective F := by
    intro s t he
    have hb := binarySubset_injective (congrArg Subtype.val he)
    ext n
    have hn := congrFun hb n
    by_cases hs : n ∈ s <;> by_cases ht : n ∈ t <;> simp_all [bits]
  exact Function.cantor_injective (fun s : Set ℕ => Encodable.encode (F s))
    (Encodable.encode_injective.comp hi)

end
end Lemmatheca.SetTheory.ForcingExtensions
