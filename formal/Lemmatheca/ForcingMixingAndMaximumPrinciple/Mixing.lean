import Lemmatheca.ForcingTheorem.ForcingTheorem
import Lemmatheca.ForcingChainConditions.Orders

namespace Lemmatheca.SetTheory.ForcingMixingAndMaximumPrinciple
open Set Order FirstOrder FirstOrder.Language
open scoped ZFSet
open Lemmatheca.SetTheory.ForcingNames
open Lemmatheca.SetTheory.ForcingTheorem
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.ForcingChainConditions
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
universe u v
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Q : Type v} [PartialOrder Q]

/-- The actual set of branch-name/branch-condition pairs. -/
def branchBundle (C : Context.{u,v} Q) (A : Set Q) (τ : A → ZFSet.{u}) : ZFSet.{u} :=
  letI : Small.{u} Q := small_of_injective C.code.injective
  ZFSet.range (fun a : A => ZFSet.pair (τ a) (C.code a.val).val)

/-- The common-refinement constructor applied to the actual branch bundle. -/
def mixedName (C : Context.{u,v} Q) (A : Set Q) (τ : A → ZFSet.{u}) : ZFSet.{u} :=
  unionName C.conditions C.relation (branchBundle C A τ)

theorem branchBundle_mem (C : Context.{u,v} Q) (A : Set Q) (τ : A → ZFSet.{u})
    (z : ZFSet.{u}) : z ∈ branchBundle C A τ ↔
      ∃ a : A, z = ZFSet.pair (τ a) (C.code a.val).val := by
  let : Small.{u} Q := small_of_injective C.code.injective
  change z ∈ ZFSet.range (fun a : A => ZFSet.pair (τ a) (C.code a.val).val) ↔ _
  rw [ZFSet.mem_range]
  exact ⟨fun ⟨a,ha⟩ => ⟨a,ha.symm⟩, fun ⟨a,ha⟩ => ⟨a,ha.symm⟩⟩

theorem branchBundle_valid (C : Context.{u,v} Q) (A : Set Q) (τ : A → ZFSet.{u})
    (hτ : ∀ a, IsName C.conditions (τ a)) : IsName C.conditions (branchBundle C A τ) := by
  apply (isName_iff C.conditions _).mpr
  intro z hz
  obtain ⟨a,rfl⟩ := (branchBundle_mem C A τ z).mp hz
  exact ⟨τ a,(C.code a.val).val,rfl,(C.code a.val).property,hτ a⟩

theorem mixedName_mem (C : Context.{u,v} Q) (A : Set Q) (τ : A → ZFSet.{u})
    (hτ : ∀ a, IsName C.conditions (τ a)) (σ : ZFSet.{u}) (r : Q) :
    ZFSet.pair σ (C.code r).val ∈ mixedName C A τ ↔
      ∃ a : A, ∃ q : Q, ZFSet.pair σ (C.code q).val ∈ τ a ∧ r ≤ a.val ∧ r ≤ q := by
  rw [mixedName,unionName_mem]
  constructor
  · rintro ⟨_,π,p,hπ,q,hσ,hrp,hrq⟩
    obtain ⟨a,he⟩ := (branchBundle_mem C A τ _).mp hπ
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    obtain ⟨σ',q',he,hqP,_⟩ := (isName_iff C.conditions (τ a)).mp (hτ a) _ hσ
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    let qcond := C.code.symm ⟨q,hqP⟩
    have hcode : (C.code qcond).val = q := congrArg Subtype.val (C.code.apply_symm_apply _)
    refine ⟨a,qcond,?_,(C.order_correct r a.val).mp hrp,?_⟩
    · rw [hcode]
      exact hσ
    · apply (C.order_correct r qcond).mp
      rw [hcode]
      exact hrq
  · rintro ⟨a,q,hσ,hra,hrq⟩
    exact ⟨(C.code r).property,τ a,(C.code a.val).val,
      (branchBundle_mem C A τ _).mpr ⟨a,rfl⟩,(C.code q).val,hσ,
      (C.order_correct r a.val).mpr hra,(C.order_correct r q).mpr hrq⟩

theorem mixedName_valid (C : Context.{u,v} Q) (A : Set Q) (τ : A → ZFSet.{u})
    (hτ : ∀ a, IsName C.conditions (τ a)) : IsName C.conditions (mixedName C A τ) := by
  exact unionName_isName C.conditions C.relation _ (branchBundle_valid C A τ hτ)

theorem mixedName_value (C : Context.{u,v} Q) (A : Set Q) (τ : A → ZFSet.{u})
    (hτ : ∀ a, IsName C.conditions (τ a)) (hA : Antichain A)
    (G : PFilter Q) (a : A) (ha : a.val ∈ G) :
    evaluation (C.filterCode G) (mixedName C A τ) =
      evaluation (C.filterCode G) (τ a) := by
  have hbundle : evaluation (C.filterCode G) (branchBundle C A τ) =
      {evaluation (C.filterCode G) (τ a)} := by
    ext z
    rw [evaluation_mem,ZFSet.mem_singleton]
    constructor
    · rintro ⟨σ,p,hσ,hp,he⟩
      obtain ⟨b,hb⟩ := (branchBundle_mem C A τ _).mp hσ
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hb
      obtain ⟨q,hqG,hq⟩ := (filterSet_mem C.conditions C.code G _).mp hp
      have hqb : q = b.val := C.code.injective (Subtype.ext hq.symm)
      have hbG : b.val ∈ G := hqb ▸ hqG
      have hba : b = a := Subtype.ext
        ((antichain_filter_subsingleton G hA) ⟨hbG,b.property⟩ ⟨ha,a.property⟩)
      simpa only [hba] using he
    · intro hz
      exact ⟨τ a,(C.code a.val).val,(branchBundle_mem C A τ _).mpr ⟨a,rfl⟩,
        (filterSet_mem C.conditions C.code G _).mpr ⟨a.val,ha,rfl⟩,hz⟩
  rw [mixedName,unionName_value C.conditions C.relation (C.filterCode G) _
    (coded_filter_bridge C.conditions C.relation C.code C.order_correct G)
    (branchBundle_valid C A τ hτ),hbundle]
  simp

/-- Promotion requires actual membership of this specified output in the ground set. -/
def mixedGroundName (C : Context.{u,v} Q) (A : Set Q) (τ : A → C.Name)
    (hM : mixedName C A (fun a => (τ a).val) ∈ C.ground) : C.Name :=
  ⟨mixedName C A (fun a => (τ a).val), hM,
    mixedName_valid C A _ (fun a => (τ a).property.2)⟩

theorem mixedGroundName_value (C : Context.{u,v} Q) (A : Set Q) (τ : A → C.Name)
    (hM : mixedName C A (fun a => (τ a).val) ∈ C.ground) (hA : Antichain A)
    (G : PFilter Q) (a : A) (ha : a.val ∈ G) :
    C.value G (mixedGroundName C A τ hM) = C.value G (τ a) := by
  apply Subtype.ext
  exact mixedName_value C A (fun a => (τ a).val) (fun a => (τ a).property.2) hA G a ha

/-- The ordinary native formula is evaluated on the original named parameters and
    the specified mixed witness in its newest protected slot. -/
theorem supplied_family_witness (C : Context.{u,v} Q) (A : Set Q) (τ : A → C.Name)
    (hM : mixedName C A (fun a => (τ a).val) ∈ C.ground) (hA : Antichain A)
    (p : Q) (hpred : PredenseBelow A p)
    (hE : downwardClosure A ∪ {q | ¬Compatible q p} ∈ C.groundFamily) {n : ℕ}
    (φ : membershipLanguage.BoundedFormula Empty (n+1)) (ρ : Fin n → C.Name)
    (hforce : ∀ a : A, C.semanticForce φ (Fin.snoc ρ (τ a)) a.val) :
    C.semanticForce φ (Fin.snoc ρ (mixedGroundName C A τ hM)) p := by
  intro G hG hp
  obtain ⟨a,haG,haA⟩ := generic_meets_predense G C.groundFamily hG hp hpred hE
  let b : A := ⟨a,haA⟩
  have hbG : b.val ∈ G := haG
  have htruth := hforce b G hG hbG
  have he : C.valueAssignment G (Fin.snoc ρ (mixedGroundName C A τ hM)) =
      C.valueAssignment G (Fin.snoc ρ (τ b)) := by
    change (C.value G) ∘ Fin.snoc ρ (mixedGroundName C A τ hM) =
      (C.value G) ∘ Fin.snoc ρ (τ b)
    rw [Fin.comp_snoc,Fin.comp_snoc,mixedGroundName_value C A τ hM hA G b hbG]
  rw [he]
  exact htruth

/-- Existential introduction for the same native formula and semantic forcing. -/
theorem witness_implies_exists (C : Context.{u,v} Q) {n : ℕ}
    (φ : membershipLanguage.BoundedFormula Empty (n+1)) (ρ : Fin n → C.Name)
    (τ : C.Name) (p : Q) (h : C.semanticForce φ (Fin.snoc ρ τ) p) :
    C.semanticForce φ.ex ρ p := by
  intro G hG hp
  let := actualMembershipStructure (C.valueDomain G)
  change φ.ex.Realize Empty.elim (C.valueAssignment G ρ)
  rw [BoundedFormula.realize_ex]
  refine ⟨C.value G τ,?_⟩
  have hs : C.valueAssignment G (Fin.snoc ρ τ) =
      Fin.snoc (C.valueAssignment G ρ) (C.value G τ) := Fin.comp_snoc (C.value G) ρ τ
  rw [← hs]
  exact h G hG hp

def witnessConditions (C : Context.{u,v} Q) {n : ℕ}
    (φ : membershipLanguage.BoundedFormula Empty (n+1)) (ρ : Fin n → C.Name)
    (p : Q) : Set Q :=
  {q | q ≤ p ∧ ∃ τ : C.Name, C.semanticForce φ (Fin.snoc ρ τ) q}

theorem witnessConditions_dense (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (hM : (C.ground : Set ZFSet.{u}).Countable) {n : ℕ}
    (φ : membershipLanguage.BoundedFormula Empty (n+1)) (ρ : Fin n → C.Name)
    (p : Q) (h : C.semanticForce φ.ex ρ p) :
    DenseBelow (witnessConditions C φ ρ p) p := by
  intro q hqp
  obtain ⟨r,hrq,τ,hτ⟩ := refining_existential C hC hM φ ρ q
    (semantic_monotone C φ.ex ρ hqp h)
  exact ⟨r,⟨hrq.trans hqp,τ,hτ⟩,hrq⟩

end
end Lemmatheca.SetTheory.ForcingMixingAndMaximumPrinciple
