import Lemmatheca.ForcingChainConditions.Orders
import Lemmatheca.ForcingTheorem.ForcingTheorem

namespace Lemmatheca.SetTheory.ForcingChainConditions
open Set Order FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.ForcingNames
open Lemmatheca.SetTheory.ForcingTheorem
open Lemmatheca.SetTheory.MembershipModels
universe u v
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Q : Type v} [PartialOrder Q]

def ForceValue (C : Context.{u,v} Q) (τ : C.Name) (p : Q) (b : ZFSet.{u}) : Prop :=
  ∀ H : PFilter Q, GenericFor H C.groundFamily → p ∈ H →
    evaluation (C.filterCode H) τ.val = b

theorem force_value_monotone (C : Context.{u,v} Q) (τ : C.Name)
    {p q : Q} {b : ZFSet.{u}} (hqp : q ≤ p) (hp : ForceValue C τ p b) :
    ForceValue C τ q b := by
  intro H hH hq
  exact hp H hH (PFilter.mem_of_le hqp hq)

theorem force_value_unique (C : Context.{u,v} Q)
    (hM : (C.ground : Set ZFSet.{u}).Countable) (τ : C.Name)
    {p : Q} {b c : ZFSet.{u}} (hb : ForceValue C τ p b) (hc : ForceValue C τ p c) :
    b = c := by
  obtain ⟨H, hH, hp⟩ := generic_through_condition C hM p
  exact (hb H hH hp).symm.trans (hc H hH hp)

theorem compatible_force_values_eq (C : Context.{u,v} Q)
    (hM : (C.ground : Set ZFSet.{u}).Countable) (τ : C.Name)
    {p q : Q} {b c : ZFSet.{u}} (hpq : Compatible p q)
    (hb : ForceValue C τ p b) (hc : ForceValue C τ q c) : b = c := by
  obtain ⟨r, hrp, hrq⟩ := hpq
  exact force_value_unique C hM τ (force_value_monotone C τ hrp hb)
    (force_value_monotone C τ hrq hc)

theorem forced_value_mem (C : Context.{u,v} Q)
    (hM : (C.ground : Set ZFSet.{u}).Countable) (τ : C.Name)
    {p q : Q} {b δ : ZFSet.{u}} (hqp : q ≤ p)
    (hδ : ∀ H : PFilter Q, GenericFor H C.groundFamily → p ∈ H →
      evaluation (C.filterCode H) τ.val ∈ δ)
    (hb : ForceValue C τ q b) : b ∈ δ := by
  obtain ⟨H, hH, hq⟩ := generic_through_condition C hM q
  have hm := hδ H hH (PFilter.mem_of_le hqp hq)
  rw [hb H hH hq] at hm
  exact hm


theorem force_ordinal_ordinary (C : Context.{u,v} Q) (τ : C.Name) (p : Q) :
    C.semanticForce (Absoluteness.ordinalTest (0 : Fin 1)).toShared ![τ] p ↔
      ∀ H : PFilter Q, GenericFor H C.groundFamily → p ∈ H →
        (evaluation (C.filterCode H) τ.val).IsOrdinal := by
  unfold Context.semanticForce
  apply forall_congr'
  intro H
  apply forall_congr'
  intro hH
  apply forall_congr'
  intro hp
  have ht : (C.valueDomain H).IsTransitive :=
    extension_transitive C.conditions C.ground (C.filterCode H) C.transitive
  have h := (Absoluteness.bounded_to_universe (C.valueDomain H) ht
    (Absoluteness.ordinalTest (0 : Fin 1)) (C.valueAssignment H ![τ])).trans
      (Absoluteness.ordinalTest_correct _ _)
  simpa only [Context.valueAssignment, Context.value, Matrix.cons_val_zero] using h

section Top
variable [OrderTop Q]

def groundCheck (C : Context.{u,v} Q)
    (hcheck : ∀ b ∈ C.ground, checkName (C.code ⊤).val b ∈ C.ground)
    (b : C.ground) : C.Name :=
  ⟨checkName (C.code ⊤).val b.val, hcheck b.val b.property,
    checkName_isName C.conditions (C.code ⊤).val b.val (C.code ⊤).property⟩

theorem ground_check_value (C : Context.{u,v} Q)
    (hcheck : ∀ b ∈ C.ground, checkName (C.code ⊤).val b ∈ C.ground)
    (b : C.ground) (H : PFilter Q) :
    evaluation (C.filterCode H) (groundCheck C hcheck b).val = b.val := by
  apply checkName_value
  exact (filterSet_mem C.conditions C.code H _).mpr ⟨⊤, PFilter.top_mem, rfl⟩

theorem force_value_ordinary_equality (C : Context.{u,v} Q)
    (hcheck : ∀ b ∈ C.ground, checkName (C.code ⊤).val b ∈ C.ground)
    (τ : C.Name) (b : C.ground) (p : Q) :
    C.semanticForce (.equal (.var (.inr 0)) (.var (.inr 1)))
      ![τ, groundCheck C hcheck b] p ↔ ForceValue C τ p b.val := by
  change (∀ H : PFilter Q, GenericFor H C.groundFamily → p ∈ H →
    C.value H τ = C.value H (groundCheck C hcheck b)) ↔ _
  constructor
  · intro h H hH hp
    have he := congrArg Subtype.val (h H hH hp)
    change evaluation (C.filterCode H) τ.val =
      evaluation (C.filterCode H) (groundCheck C hcheck b).val at he
    rw [ground_check_value] at he
    exact he
  · intro h H hH hp
    apply Subtype.ext
    change evaluation (C.filterCode H) τ.val =
      evaluation (C.filterCode H) (groundCheck C hcheck b).val
    rw [ground_check_value]
    exact h H hH hp


theorem force_membership_ordinary (C : Context.{u,v} Q)
    (hcheck : ∀ b ∈ C.ground, checkName (C.code ⊤).val b ∈ C.ground)
    (τ : C.Name) (b : C.ground) (p : Q) :
    C.semanticForce (Absoluteness.DeltaZero.mem (0 : Fin 2) 1).toShared
      ![τ, groundCheck C hcheck b] p ↔
      ∀ H : PFilter Q, GenericFor H C.groundFamily → p ∈ H →
        evaluation (C.filterCode H) τ.val ∈ b.val := by
  change (∀ H : PFilter Q, GenericFor H C.groundFamily → p ∈ H →
    evaluation (C.filterCode H) τ.val ∈
      evaluation (C.filterCode H) (groundCheck C hcheck b).val) ↔ _
  simp only [ground_check_value]

theorem ordinal_value_ground (C : Context.{u,v} Q)
    (hcheck : ∀ b ∈ C.ground, checkName (C.code ⊤).val b ∈ C.ground)
    (hrank : ∀ τ ∈ C.ground, IsName C.conditions τ → (nameRank τ).toZFSet ∈ C.ground)
    (τ : C.Name) (H : PFilter Q)
    (hord : (evaluation (C.filterCode H) τ.val).IsOrdinal) :
    evaluation (C.filterCode H) τ.val ∈ C.ground := by
  have hground : C.ground ⊆ C.valueDomain H := by
    intro b hb
    let σ := groundCheck C hcheck (⟨b, hb⟩ : C.ground)
    apply (extension_mem C.conditions C.ground (C.filterCode H) b).mpr
    exact ⟨σ.val, σ.property.1, σ.property.2, ground_check_value C hcheck _ H⟩
  apply ((extension_same_ordinals C.conditions C.ground (C.filterCode H)
    C.transitive hground hrank) _ hord).mp
  exact (C.value H τ).property

def decidingValues (C : Context.{u,v} Q) (τ : C.Name) (p : Q) : Set Q :=
  {q | q ≤ p ∧ ∃ b ∈ C.ground, b.IsOrdinal ∧ ForceValue C τ q b}

theorem ordinal_deciding_dense (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (hM : (C.ground : Set ZFSet.{u}).Countable)
    (hcheck : ∀ b ∈ C.ground, checkName (C.code ⊤).val b ∈ C.ground)
    (hrank : ∀ τ ∈ C.ground, IsName C.conditions τ → (nameRank τ).toZFSet ∈ C.ground)
    (τ : C.Name) (p : Q)
    (hord : ∀ H : PFilter Q, GenericFor H C.groundFamily → p ∈ H →
      (evaluation (C.filterCode H) τ.val).IsOrdinal) :
    DenseBelow (decidingValues C τ p) p := by
  intro r hrp
  obtain ⟨H, hH, hrH⟩ := generic_through_condition C hM r
  have hOrdinal := hord H hH (PFilter.mem_of_le hrp hrH)
  have hground := ordinal_value_ground C hcheck hrank τ H hOrdinal
  let b : C.ground := ⟨evaluation (C.filterCode H) τ.val, hground⟩
  have htrue : Absoluteness.setSatisfies (C.valueDomain H)
      (.equal (.var (.inr 0)) (.var (.inr 1)))
      (C.valueAssignment H ![τ, groundCheck C hcheck b]) := by
    change C.value H τ = C.value H (groundCheck C hcheck b)
    apply Subtype.ext
    exact (ground_check_value C hcheck b H).symm
  obtain ⟨s, hsH, hsForce⟩ := (ordinary_truth C hC H hH
    (.equal (.var (.inr 0)) (.var (.inr 1))) ![τ, groundCheck C hcheck b]).mp htrue
  obtain ⟨q, hqH, hqs, hqr⟩ := H.directed s hsH r hrH
  have hsq : ForceValue C τ q b.val := force_value_monotone C τ hqs
    ((force_value_ordinary_equality C hcheck τ b s).mp hsForce)
  exact ⟨q, ⟨hqr.trans hrp, b.val, b.property, hOrdinal, hsq⟩, hqr⟩

theorem ordinal_deciding_antichain (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (hM : (C.ground : Set ZFSet.{u}).Countable)
    (hcheck : ∀ b ∈ C.ground, checkName (C.code ⊤).val b ∈ C.ground)
    (hrank : ∀ τ ∈ C.ground, IsName C.conditions τ → (nameRank τ).toZFSet ∈ C.ground)
    (hccc : CCC Q) (τ : C.Name) (p : Q)
    (hord : ∀ H : PFilter Q, GenericFor H C.groundFamily → p ∈ H →
      (evaluation (C.filterCode H) τ.val).IsOrdinal) :
    ∃ A : Set Q, A ⊆ decidingValues C τ p ∧ A ⊆ Set.Iic p ∧ Antichain A ∧
      PredenseBelow A p ∧ A.Countable := by
  exact exists_countable_antichain_below hccc
    (ordinal_deciding_dense C hC hM hcheck hrank τ p hord)


theorem ordinal_antichain_labels (C : Context.{u,v} Q) (τ : C.Name)
    {p : Q} {A : Set Q} (hA : A ⊆ decidingValues C τ p) :
    ∃ label : A → ZFSet.{u}, ∀ a : A,
      label a ∈ C.ground ∧ (label a).IsOrdinal ∧ ForceValue C τ a.val (label a) := by
  classical
  have _hTop : Nonempty Q := ⟨⊤⟩
  have hex (a : A) : ∃ b : ZFSet.{u},
      b ∈ C.ground ∧ b.IsOrdinal ∧ ForceValue C τ a.val b :=
    (hA a.property).2
  choose label hlabel using hex
  exact ⟨label, hlabel⟩

end Top

theorem countable_name_value_cover (C : Context.{u,v} Q) (τ : C.Name)
    {p : Q} {A : Set Q} (hA : A.Countable) (hpred : PredenseBelow A p)
    (hE : downwardClosure A ∪ {q | ¬Compatible q p} ∈ C.groundFamily)
    (label : A → ZFSet.{u}) (hlabel : ∀ a : A, ForceValue C τ a.val (label a)) :
    (Set.range label).Countable ∧
      ∀ H : PFilter Q, GenericFor H C.groundFamily → p ∈ H →
        evaluation (C.filterCode H) τ.val ∈ Set.range label := by
  let : Countable A := hA.to_subtype
  refine ⟨Set.countable_range label, ?_⟩
  intro H hH hp
  obtain ⟨a, haH, haA⟩ := generic_meets_predense H C.groundFamily hH hp hpred hE
  exact ⟨⟨a, haA⟩, (hlabel ⟨a, haA⟩ H hH haH).symm⟩

end
end Lemmatheca.SetTheory.ForcingChainConditions
