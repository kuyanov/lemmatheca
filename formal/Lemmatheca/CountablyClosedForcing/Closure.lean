import Lemmatheca.ForcingChainConditions.Values
import Lemmatheca.ForcingNames.CohenName

namespace Lemmatheca.SetTheory.CountablyClosedForcing
open Set Order
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.ForcingNames
open Lemmatheca.SetTheory.NaturalNumbersAsSets
open Lemmatheca.SetTheory.ForcingTheorem
open Lemmatheca.SetTheory.ForcingChainConditions
universe u v
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Q : Type v} [PartialOrder Q]

def CountablyClosed (Q : Type v) [PartialOrder Q] : Prop :=
  ∀ s : ℕ → Q, Antitone s → ∃ q, ∀ n, q ≤ s n

def decisionNext (D : ℕ → Set Q) (p : Q) (hD : ∀ n, DenseBelow (D n) p)
    (n : ℕ) (q : Set.Iic p) : Set.Iic p :=
  let r := Classical.choose (hD n q.val q.property)
  ⟨r, (Classical.choose_spec (hD n q.val q.property)).2.trans q.property⟩

def decisionChain (D : ℕ → Set Q) (p : Q) (hD : ∀ n, DenseBelow (D n) p)
    (r : Set.Iic p) : ℕ → Set.Iic p
  | 0 => r
  | n + 1 => decisionNext D p hD n (decisionChain D p hD r n)

theorem decision_chain_spec (D : ℕ → Set Q) (p : Q)
    (hD : ∀ n, DenseBelow (D n) p) (r : Set.Iic p) :
    (decisionChain D p hD r 0).val = r.val ∧
    Antitone (fun n => (decisionChain D p hD r n).val) ∧
    ∀ n, (decisionChain D p hD r (n+1)).val ∈ D n := by
  refine ⟨rfl,?_,?_⟩
  · apply antitone_nat_of_succ_le
    intro n
    exact (Classical.choose_spec (hD n (decisionChain D p hD r n).val
      (decisionChain D p hD r n).property)).2
  · intro n
    exact (Classical.choose_spec (hD n (decisionChain D p hD r n).val
      (decisionChain D p hD r n).property)).1

theorem dense_fusion (hc : CountablyClosed Q) (D : ℕ → Set Q) (p : Q)
    (hD : ∀ n, DenseBelow (D n) p) (ho : ∀ n, Open (D n)) :
    DenseBelow (⋂ n, D n) p := by
  intro r hrp
  have hs := decision_chain_spec D p hD ⟨r,hrp⟩
  obtain ⟨q,hq⟩ := hc (fun n => (decisionChain D p hD ⟨r,hrp⟩ n).val) hs.2.1
  refine ⟨q,Set.mem_iInter.mpr (fun n => ho n (hs.2.2 n) (hq (n+1))),?_⟩
  exact (hq 0).trans_eq hs.1

def sequenceGraph (h : ℕ → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun n => ZFSet.pair (naturalSet n) (h n))

private theorem nat_code_injective : Function.Injective (naturalSet.{u}) := by
  intro m n h
  exact Nat.le_antisymm ((naturalSet_order m n).2.mp (fun _ hz => h ▸ hz))
    ((naturalSet_order n m).2.mp (fun _ hz => h.symm ▸ hz))

private theorem sequence_members (h : ℕ → ZFSet.{u}) (x : ZFSet.{u}) :
    x ∈ sequenceGraph h ↔ ∃ n, x = ZFSet.pair (naturalSet n) (h n) := by
  simp only [sequenceGraph,ZFSet.mem_range]
  exact ⟨fun ⟨n,hn⟩ => ⟨n,hn.symm⟩,fun ⟨n,hn⟩ => ⟨n,hn.symm⟩⟩

def ForceCoordinate (C : Context.{u,v} Q) (σ : C.Name)
    (p : Q) (n : ℕ) (b : ZFSet.{u}) : Prop :=
  ∀ H : PFilter Q, GenericFor H C.groundFamily → p ∈ H →
    ZFSet.pair (naturalSet n) b ∈ evaluation (C.filterCode H) σ.val

def coordinateDecisions (C : Context.{u,v} Q) (σ : C.Name)
    (p : Q) (δ : ZFSet.{u}) (n : ℕ) : Set Q :=
  {q | q ≤ p ∧ ∃ b ∈ δ, ForceCoordinate C σ q n b}

def wholeDecisions (C : Context.{u,v} Q) (σ : C.Name)
    (p : Q) (δ : ZFSet.{u}) : Set Q :=
  {q | q ≤ p ∧ ∃ h : ℕ → ZFSet.{u}, (∀ n, h n ∈ δ) ∧
    ForceValue C σ q (sequenceGraph h)}

theorem sequence_graph_function (h : ℕ → ZFSet.{u}) (δ : ZFSet.{u})
    (hh : ∀ n, h n ∈ δ) : ZFSet.IsFunc ZFSet.omega δ (sequenceGraph h) := by
  refine ⟨?_,?_⟩
  · intro x hx
    obtain ⟨n,rfl⟩ := (sequence_members h x).mp hx
    exact ZFSet.pair_mem_prod.mpr ⟨(omega_members _).mpr ⟨n,rfl⟩,hh n⟩
  · intro z hz
    obtain ⟨n,rfl⟩ := (omega_members z).mp hz
    refine ⟨h n,(sequence_members h _).mpr ⟨n,rfl⟩,?_⟩
    intro w hw
    obtain ⟨m,hm⟩ := (sequence_members h _).mp hw
    obtain ⟨hn,he⟩ := ZFSet.pair_inj.mp hm
    have heq := nat_code_injective hn
    subst m
    exact he

theorem sequence_graph_of_coordinates (x δ : ZFSet.{u})
    (hx : ZFSet.IsFunc ZFSet.omega δ x) (h : ℕ → ZFSet.{u})
    (hh : ∀ n, ZFSet.pair (naturalSet n) (h n) ∈ x) :
    x = sequenceGraph h := by
  ext z
  constructor
  · intro hz
    obtain ⟨a,ha,b,_,rfl⟩ := ZFSet.mem_prod.mp (hx.1 hz)
    obtain ⟨n,rfl⟩ := (omega_members a).mp ha
    obtain ⟨w,_,hw⟩ := hx.2 (naturalSet n) ((omega_members _).mpr ⟨n,rfl⟩)
    have hb : b = h n := (hw b hz).trans (hw (h n) (hh n)).symm
    exact (sequence_members h _).mpr ⟨n,congrArg (ZFSet.pair (naturalSet n)) hb⟩
  · intro hz
    obtain ⟨n,rfl⟩ := (sequence_members h z).mp hz
    exact hh n

theorem force_coordinate_monotone (C : Context.{u,v} Q) (σ : C.Name)
    {p q : Q} {n : ℕ} {b : ZFSet.{u}} (hqp : q ≤ p)
    (hp : ForceCoordinate C σ p n b) : ForceCoordinate C σ q n b := by
  intro H hH hq
  exact hp H hH (PFilter.mem_of_le hqp hq)

theorem force_coordinate_unique (C : Context.{u,v} Q)
    (hM : (C.ground : Set ZFSet.{u}).Countable) (σ : C.Name)
    (p : Q) (δ : ZFSet.{u})
    (hf : ∀ H : PFilter Q, GenericFor H C.groundFamily → p ∈ H →
      ZFSet.IsFunc ZFSet.omega δ (evaluation (C.filterCode H) σ.val))
    (n : ℕ) (b c : ZFSet.{u}) (hb : ForceCoordinate C σ p n b)
    (hc : ForceCoordinate C σ p n c) : b = c := by
  obtain ⟨H,hH,hp⟩ := generic_through_condition C hM p
  obtain ⟨w,_,hw⟩ := (hf H hH hp).2 (naturalSet n) ((omega_members _).mpr ⟨n,rfl⟩)
  exact (hw b (hb H hH hp)).trans (hw c (hc H hH hp)).symm

section Top
variable [OrderTop Q]

theorem force_coordinate_ordinary (C : Context.{u,v} Q)
    (hcheck : ∀ b ∈ C.ground, checkName (C.code ⊤).val b ∈ C.ground)
    (σ : C.Name) (n : ℕ) (hn : naturalSet n ∈ C.ground)
    (b : C.ground) (p : Q) :
    C.semanticForce (Absoluteness.relationTest (1 : Fin 3) 2 0).toShared
      ![σ, groundCheck C hcheck ⟨naturalSet n, hn⟩, groundCheck C hcheck b] p ↔
      ForceCoordinate C σ p n b.val := by
  unfold Context.semanticForce
  apply forall_congr'
  intro H
  apply forall_congr'
  intro hH
  apply forall_congr'
  intro hp
  have ht : (C.valueDomain H).IsTransitive :=
    extension_transitive C.conditions C.ground (C.filterCode H) C.transitive
  have he := (Absoluteness.bounded_to_universe (C.valueDomain H) ht
    (Absoluteness.relationTest (1 : Fin 3) 2 0)
    (C.valueAssignment H ![σ,groundCheck C hcheck ⟨naturalSet n,hn⟩,groundCheck C hcheck b])).trans
      (Absoluteness.relationTest_correct _ _ _ _)
  simpa [Context.valueAssignment,Context.value,ground_check_value] using he

theorem coordinate_decisions_dense (C : Context.{u,v} Q) (hC : DecisionClosed C)
    (hM : (C.ground : Set ZFSet.{u}).Countable)
    (hcheck : ∀ b ∈ C.ground, checkName (C.code ⊤).val b ∈ C.ground)
    (hn : ∀ n, naturalSet n ∈ C.ground) (δ : ZFSet.{u}) (hδ : δ ∈ C.ground)
    (σ : C.Name) (p : Q)
    (hf : ∀ H : PFilter Q, GenericFor H C.groundFamily → p ∈ H →
      ZFSet.IsFunc ZFSet.omega δ (evaluation (C.filterCode H) σ.val)) :
    ∀ n, DenseBelow (coordinateDecisions C σ p δ n) p := by
  intro n r hrp
  obtain ⟨H,hH,hrH⟩ := generic_through_condition C hM r
  have hfun := hf H hH (PFilter.mem_of_le hrp hrH)
  obtain ⟨b,hb,huniq⟩ := hfun.2 (naturalSet n) ((omega_members _).mpr ⟨n,rfl⟩)
  have hbδ : b ∈ δ := (ZFSet.pair_mem_prod.mp (hfun.1 hb)).2
  have hbM : b ∈ C.ground := C.transitive δ hδ hbδ
  let bM : C.ground := ⟨b,hbM⟩
  let a : Fin 3 → C.Name := ![σ,groundCheck C hcheck ⟨naturalSet n,hn n⟩,groundCheck C hcheck bM]
  have ht : (C.valueDomain H).IsTransitive :=
    extension_transitive C.conditions C.ground (C.filterCode H) C.transitive
  have htrue : Absoluteness.setSatisfies (C.valueDomain H)
      (Absoluteness.relationTest (1 : Fin 3) 2 0).toShared (C.valueAssignment H a) := by
    apply ((Absoluteness.bounded_to_universe (C.valueDomain H) ht
      (Absoluteness.relationTest (1 : Fin 3) 2 0) (C.valueAssignment H a)).trans
        (Absoluteness.relationTest_correct _ _ _ _)).mpr
    simpa [a,Context.valueAssignment,Context.value,ground_check_value,bM] using hb
  obtain ⟨t,htH,htforce⟩ := (ordinary_truth C hC H hH
    (Absoluteness.relationTest (1 : Fin 3) 2 0).toShared a).mp htrue
  obtain ⟨q,_,hqt,hqr⟩ := H.directed t htH r hrH
  have hforce : ForceCoordinate C σ q n b :=
    force_coordinate_monotone C σ hqt
      ((force_coordinate_ordinary C hcheck σ n (hn n) bM t).mp htforce)
  exact ⟨q,⟨hqr.trans hrp,b,hbδ,hforce⟩,hqr⟩

end Top

theorem coordinate_decisions_open (C : Context.{u,v} Q) (σ : C.Name)
    (p : Q) (δ : ZFSet.{u}) (n : ℕ) : Open (coordinateDecisions C σ p δ n) := by
  rintro q r ⟨hqp,b,hb,hforce⟩ hrq
  exact ⟨hrq.trans hqp,b,hb,force_coordinate_monotone C σ hrq hforce⟩

theorem whole_decisions_dense (C : Context.{u,v} Q) (hc : CountablyClosed Q)
    (σ : C.Name) (p : Q) (δ : ZFSet.{u})
    (hf : ∀ H : PFilter Q, GenericFor H C.groundFamily → p ∈ H →
      ZFSet.IsFunc ZFSet.omega δ (evaluation (C.filterCode H) σ.val))
    (hD : ∀ n, DenseBelow (coordinateDecisions C σ p δ n) p) :
    DenseBelow (wholeDecisions C σ p δ) p := by
  intro r hrp
  obtain ⟨q,hq,hqr⟩ := dense_fusion hc (coordinateDecisions C σ p δ) p hD
    (coordinate_decisions_open C σ p δ) r hrp
  have hex : ∀ n, ∃ b ∈ δ, ForceCoordinate C σ q n b :=
    fun n => (Set.mem_iInter.mp hq n).2
  choose h hh hforce using hex
  refine ⟨q,⟨hqr.trans hrp,h,hh,?_⟩,hqr⟩
  intro H hH hqH
  exact sequence_graph_of_coordinates _ δ
    (hf H hH (PFilter.mem_of_le (hqr.trans hrp) hqH)) h
    (fun n => hforce n H hH hqH)

theorem generic_whole_decision (C : Context.{u,v} Q) (σ : C.Name)
    (p : Q) (δ : ZFSet.{u}) (G : PFilter Q)
    (hG : GenericFor G C.groundFamily) (hp : p ∈ G)
    (hE : DenseBelow (wholeDecisions C σ p δ) p)
    (hground : wholeDecisions C σ p δ ∪ {q | ¬Compatible q p} ∈ C.groundFamily) :
    ∃ h : ℕ → ZFSet.{u}, (∀ n, h n ∈ δ) ∧
      evaluation (C.filterCode G) σ.val = sequenceGraph h := by
  obtain ⟨q,hq,_,h,hh,hforce⟩ := generic_dense_below G C.groundFamily hG hp hE hground
  exact ⟨h,hh,hforce G hG hq⟩

end
end Lemmatheca.SetTheory.CountablyClosedForcing
