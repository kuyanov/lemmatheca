import Lemmatheca.ForcingChainConditions.Values
import Lemmatheca.ManyCohenReals.Names

namespace Lemmatheca.SetTheory.NiceNamesAndCohenContinuum
open Set Order FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.ForcingChainConditions
open Lemmatheca.SetTheory.ForcingNames
open Lemmatheca.SetTheory.ForcingTheorem
open Lemmatheca.SetTheory.NaturalNumbersAsSets
open Lemmatheca.SetTheory.MembershipModels
open scoped ZFSet
universe u
noncomputable section
local instance niceNamesPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {Q : Type u} [PartialOrder Q] [OrderTop Q]

/-- The exact antichain attachment construction, valid even for empty rows. -/
def niceName (C : Context.{u,u} Q) (B : ℕ → Set Q) : ZFSet.{u} :=
  ZFSet.range (fun np : {np : ℕ × Q // np.2 ∈ B np.1} =>
    ZFSet.pair (checkName (C.code ⊤).val (naturalSet np.val.1)) (C.code np.val.2).val)

def rowCode (C : Context.{u,u} Q) (B : ℕ → Set Q) : ZFSet.{u} :=
  ZFSet.range (fun np : {np : ℕ × Q // np.2 ∈ B np.1} =>
    ZFSet.pair (naturalSet np.val.1) (C.code np.val.2).val)

def codeRow (C : Context.{u,u} Q) (b : ZFSet.{u}) (n : ℕ) : Set Q :=
  {p | ZFSet.pair (naturalSet n) (C.code p).val ∈ b}

def codeSet (C : Context.{u,u} Q) : ZFSet.{u} :=
  (ZFSet.powerset (ZFSet.prod ZFSet.omega C.conditions)).sep
    (fun b => b ∈ C.ground ∧ ∀ n, Antichain (codeRow C b n))

def codeName (C : Context.{u,u} Q) (b : ZFSet.{u}) : ZFSet.{u} :=
  niceName C (codeRow C b)

theorem nice_name_attachments (C : Context.{u,u} Q) (B : ℕ → Set Q) (z : ZFSet.{u}) :
    z ∈ niceName C B ↔ ∃ n p, p ∈ B n ∧
      z = ZFSet.pair (checkName (C.code ⊤).val (naturalSet n)) (C.code p).val := by
  rw [niceName, ZFSet.mem_range]
  constructor
  · rintro ⟨np, he⟩
    exact ⟨np.val.1, np.val.2, np.property, he.symm⟩
  · rintro ⟨n, p, hp, he⟩
    exact ⟨⟨(n,p), hp⟩, he.symm⟩

theorem nice_name_valid (C : Context.{u,u} Q) (B : ℕ → Set Q) :
    IsName C.conditions (niceName C B) := by
  apply (isName_iff C.conditions _).mpr
  intro z hz
  obtain ⟨n,p,hp,rfl⟩ := (nice_name_attachments C B z).mp hz
  exact ⟨_, _, rfl, (C.code p).property,
    checkName_isName C.conditions _ _ (C.code ⊤).property⟩

theorem nice_name_value (C : Context.{u,u} Q) (B : ℕ → Set Q)
    (H : PFilter Q) (x : ZFSet.{u}) :
    x ∈ evaluation (C.filterCode H) (niceName C B) ↔
      ∃ n p, p ∈ H ∧ p ∈ B n ∧ x = naturalSet n := by
  have htop : (C.code ⊤).val ∈ C.filterCode H :=
    (filterSet_mem C.conditions C.code H _).mpr ⟨⊤, PFilter.top_mem, rfl⟩
  rw [evaluation_mem]
  constructor
  · rintro ⟨σ,q,hσq,hq,he⟩
    obtain ⟨n,p,hp,hpair⟩ := (nice_name_attachments C B _).mp hσq
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hpair
    obtain ⟨r,hr,hrp⟩ := (filterSet_mem C.conditions C.code H _).mp hq
    have hrp' : r = p := C.code.injective (Subtype.ext hrp.symm)
    subst r
    exact ⟨n,p,hr,hp,he.trans (checkName_value _ _ _ htop)⟩
  · rintro ⟨n,p,hpH,hpB,he⟩
    exact ⟨_, (C.code p).val,
      (nice_name_attachments C B _).mpr ⟨n,p,hpB,rfl⟩,
      (filterSet_mem C.conditions C.code H _).mpr ⟨p,hpH,rfl⟩,
      he.trans (checkName_value _ _ _ htop).symm⟩

theorem nice_name_subset_omega (C : Context.{u,u} Q) (B : ℕ → Set Q)
    (H : PFilter Q) : evaluation (C.filterCode H) (niceName C B) ⊆ ZFSet.omega := by
  intro x hx
  obtain ⟨n,p,_,_,rfl⟩ := (nice_name_value C B H x).mp hx
  exact (omega_members _).mpr ⟨n,rfl⟩

omit [OrderTop Q] in
theorem row_code_members (C : Context.{u,u} Q) (B : ℕ → Set Q) (z : ZFSet.{u}) :
    z ∈ rowCode C B ↔ ∃ n p, p ∈ B n ∧ z = ZFSet.pair (naturalSet n) (C.code p).val := by
  rw [rowCode, ZFSet.mem_range]
  constructor
  · rintro ⟨np,he⟩
    exact ⟨np.val.1,np.val.2,np.property,he.symm⟩
  · rintro ⟨n,p,hp,he⟩
    exact ⟨⟨(n,p),hp⟩,he.symm⟩

omit [OrderTop Q] in
theorem row_code_subset (C : Context.{u,u} Q) (B : ℕ → Set Q) :
    rowCode C B ⊆ ZFSet.prod ZFSet.omega C.conditions := by
  intro z hz
  obtain ⟨n,p,hp,rfl⟩ := (row_code_members C B z).mp hz
  exact ZFSet.pair_mem_prod.mpr ⟨(omega_members _).mpr ⟨n,rfl⟩,(C.code p).property⟩

omit [OrderTop Q] in
theorem code_row_inverse (C : Context.{u,u} Q) (B : ℕ → Set Q) :
    codeRow C (rowCode C B) = B := by
  funext n
  ext p
  change ZFSet.pair (naturalSet n) (C.code p).val ∈ rowCode C B ↔ p ∈ B n
  rw [row_code_members]
  constructor
  · rintro ⟨m,q,hq,he⟩
    obtain ⟨hn,hp⟩ := ZFSet.pair_inj.mp he
    have hnm : n = m := Nat.le_antisymm
      ((naturalSet_order n m).2.mp (fun x hx => hn ▸ hx))
      ((naturalSet_order m n).2.mp (fun x hx => hn.symm ▸ hx))
    have hpq : p = q := C.code.injective (Subtype.ext hp)
    subst m; subst q
    exact hq
  · intro hp
    exact ⟨n,p,hp,rfl⟩

omit [OrderTop Q] in
theorem row_code_inverse (C : Context.{u,u} Q) (b : ZFSet.{u})
    (hb : b ⊆ ZFSet.prod ZFSet.omega C.conditions) : rowCode C (codeRow C b) = b := by
  ext z
  rw [row_code_members]
  constructor
  · rintro ⟨n,p,hp,rfl⟩
    exact hp
  · intro hz
    obtain ⟨n,hn,p,hp,rfl⟩ := ZFSet.mem_prod.mp (hb hz)
    obtain ⟨k,rfl⟩ := (omega_members n).mp hn
    let q := C.code.symm ⟨p,hp⟩
    have he : (C.code q).val = p := congrArg Subtype.val (C.code.apply_symm_apply _)
    refine ⟨k,q,?_,?_⟩
    · change ZFSet.pair (naturalSet k) (C.code q).val ∈ b
      rw [he]; exact hz
    · rw [he]

omit [OrderTop Q] in
theorem code_set_members (C : Context.{u,u} Q) (b : ZFSet.{u}) :
    b ∈ codeSet C ↔ b ⊆ ZFSet.prod ZFSet.omega C.conditions ∧
      b ∈ C.ground ∧ ∀ n, Antichain (codeRow C b n) := by
  simp only [codeSet, ZFSet.mem_sep, ZFSet.mem_powerset]


omit [OrderTop Q] in
theorem empty_code_member (C : Context.{u,u} Q) (hempty : (∅ : ZFSet.{u}) ∈ C.ground) :
    (∅ : ZFSet.{u}) ∈ codeSet C := by
  apply (code_set_members C _).mpr
  refine ⟨ZFSet.empty_subset _,hempty,?_⟩
  intro n p hp
  exact False.elim (ZFSet.notMem_empty _ hp)

theorem empty_nice_value (C : Context.{u,u} Q) (H : PFilter Q) :
    evaluation (C.filterCode H) (niceName C (fun _ => ∅)) = ∅ := by
  ext x
  rw [nice_name_value]
  simp

def ForceMember (C : Context.{u,u} Q) (τ : C.Name) (n : ℕ) (p : Q) : Prop :=
  ∀ H : PFilter Q, GenericFor H C.groundFamily → p ∈ H →
    naturalSet n ∈ evaluation (C.filterCode H) τ.val

def ForceNotMember (C : Context.{u,u} Q) (τ : C.Name) (n : ℕ) (p : Q) : Prop :=
  ∀ H : PFilter Q, GenericFor H C.groundFamily → p ∈ H →
    naturalSet n ∉ evaluation (C.filterCode H) τ.val

def deciding (C : Context.{u,u} Q) (τ : C.Name) (n : ℕ) : Set Q :=
  {p | ForceMember C τ n p ∨ ForceNotMember C τ n p}

theorem deciding_dense (C : Context.{u,u} Q) (hC : DecisionClosed C)
    (hM : (C.ground : Set ZFSet.{u}).Countable)
    (hcheck : ∀ b ∈ C.ground, checkName (C.code ⊤).val b ∈ C.ground)
    (hnat : ∀ n, naturalSet n ∈ C.ground) (τ : C.Name) (n : ℕ) :
    Dense (deciding C τ n) := by
  intro p
  obtain ⟨H,hH,hp⟩ := generic_through_condition C hM p
  let ν := groundCheck C hcheck (⟨naturalSet n,hnat n⟩ : C.ground)
  let φ := (Absoluteness.DeltaZero.mem (0 : Fin 2) 1).toShared
  let a : Fin 2 → C.Name := ![ν,τ]
  by_cases hn : naturalSet n ∈ evaluation (C.filterCode H) τ.val
  · have ht : Absoluteness.setSatisfies (C.valueDomain H) φ (C.valueAssignment H a) := by
      change evaluation (C.filterCode H) ν.val ∈ evaluation (C.filterCode H) τ.val
      rw [ground_check_value]
      exact hn
    obtain ⟨r,hr,hrf⟩ := (ordinary_truth C hC H hH φ a).mp ht
    obtain ⟨q,hq,hqr,hqp⟩ := H.directed r hr p hp
    refine ⟨q,Or.inl ?_,hqp⟩
    intro J hJ hqJ
    have hm := hrf J hJ (PFilter.mem_of_le hqr hqJ)
    change evaluation (C.filterCode J) ν.val ∈ evaluation (C.filterCode J) τ.val at hm
    rw [ground_check_value] at hm
    exact hm
  · have ht : Absoluteness.setSatisfies (C.valueDomain H) φ.not (C.valueAssignment H a) := by
      change ¬ evaluation (C.filterCode H) ν.val ∈ evaluation (C.filterCode H) τ.val
      rw [ground_check_value]
      exact hn
    obtain ⟨r,hr,hrf⟩ := (ordinary_truth C hC H hH φ.not a).mp ht
    obtain ⟨q,hq,hqr,hqp⟩ := H.directed r hr p hp
    refine ⟨q,Or.inr ?_,hqp⟩
    intro J hJ hqJ
    have hm := hrf J hJ (PFilter.mem_of_le hqr hqJ)
    change ¬ evaluation (C.filterCode J) ν.val ∈ evaluation (C.filterCode J) τ.val at hm
    rw [ground_check_value] at hm
    exact hm

theorem maximal_deciding_antichain (C : Context.{u,u} Q) (hC : DecisionClosed C)
    (hM : (C.ground : Set ZFSet.{u}).Countable)
    (hcheck : ∀ b ∈ C.ground, checkName (C.code ⊤).val b ∈ C.ground)
    (hnat : ∀ n, naturalSet n ∈ C.ground) (τ : C.Name) :
    ∃ A : ℕ → Set Q, ∀ n, A n ⊆ deciding C τ n ∧ MaximalAntichain (A n) := by
  have h (n : ℕ) := exists_maximal_antichain_in_dense
    (deciding_dense C hC hM hcheck hnat τ n)
  choose A hsub hmax using h
  exact ⟨A,fun n => ⟨hsub n,hmax n⟩⟩

def positiveRows (C : Context.{u,u} Q) (τ : C.Name) (A : ℕ → Set Q) : ℕ → Set Q :=
  fun n => {p | p ∈ A n ∧ ForceMember C τ n p}

omit [OrderTop Q] in
theorem positive_rows_antichain (C : Context.{u,u} Q) (τ : C.Name) (A : ℕ → Set Q)
    (hA : ∀ n, Antichain (A n)) : ∀ n, Antichain (positiveRows C τ A n) := by
  intro n p hp q hq hne
  exact hA n hp.1 hq.1 hne

theorem nice_replacement_value (C : Context.{u,u} Q) (τ : C.Name) (A : ℕ → Set Q)
    (hA : ∀ n, A n ⊆ deciding C τ n ∧ MaximalAntichain (A n))
    (hground : ∀ n, downwardClosure (A n) ∈ C.groundFamily) :
    ∀ H : PFilter Q, GenericFor H C.groundFamily →
      evaluation (C.filterCode H) (niceName C (positiveRows C τ A)) =
        (evaluation (C.filterCode H) τ.val).sep (fun n => n ∈ ZFSet.omega) := by
  intro H hH
  ext x
  rw [nice_name_value, ZFSet.mem_sep]
  constructor
  · rintro ⟨n,p,hpH,hpB,rfl⟩
    exact ⟨hpB.2 H hH hpH,(omega_members _).mpr ⟨n,rfl⟩⟩
  · rintro ⟨hx,hn⟩
    obtain ⟨n,rfl⟩ := (omega_members x).mp hn
    obtain ⟨q,hqH,a,ha,hqa⟩ := hH _ (hground n)
      (maximal_antichain_downward_dense (hA n).2)
    have haH : a ∈ H := PFilter.mem_of_le hqa hqH
    have haPositive : ForceMember C τ n a :=
      ((hA n).1 ha).resolve_right (fun hn => hn H hH haH hx)
    exact ⟨n,a,haH,⟨ha,haPositive⟩,rfl⟩

/-- The actual top-attached name of the evaluation graph over all ground nice codes. -/
def evaluationName (C : Context.{u,u} Q) : ZFSet.{u} :=
  Lemmatheca.SetTheory.ManyCohenReals.indexedFamilyName
    (codeSet C) (C.code ⊤).val (fun b => codeName C b.val)

def evaluationGraph (C : Context.{u,u} Q) (H : PFilter Q) : ZFSet.{u} :=
  ZFSet.range (fun b : codeSet C =>
    ZFSet.pair b.val (evaluation (C.filterCode H) (codeName C b.val)))

theorem evaluation_name_valid (C : Context.{u,u} Q) :
    IsName C.conditions (evaluationName C) := by
  exact Lemmatheca.SetTheory.ManyCohenReals.indexedFamilyName_isName
    C.conditions (codeSet C) _ _ (C.code ⊤).property
    (fun _ => nice_name_valid C _)

theorem evaluation_name_value (C : Context.{u,u} Q) (H : PFilter Q) :
    evaluation (C.filterCode H) (evaluationName C) = evaluationGraph C H := by
  exact Lemmatheca.SetTheory.ManyCohenReals.indexedFamilyName_value
    (codeSet C) _ _ _
    ((filterSet_mem C.conditions C.code H _).mpr ⟨⊤,PFilter.top_mem,rfl⟩)

theorem evaluation_graph_members (C : Context.{u,u} Q) (H : PFilter Q)
    (b x : ZFSet.{u}) :
    ZFSet.pair b x ∈ evaluationGraph C H ↔
      b ∈ codeSet C ∧ x = evaluation (C.filterCode H) (codeName C b) := by
  rw [evaluationGraph,ZFSet.mem_range]
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨hcb,hcx⟩ := ZFSet.pair_inj.mp hc
    subst b
    exact ⟨c.property,hcx.symm⟩
  · rintro ⟨hb,rfl⟩
    exact ⟨⟨b,hb⟩,rfl⟩

theorem evaluation_graph_in_extension (C : Context.{u,u} Q) (H : PFilter Q)
    (hname : evaluationName C ∈ C.ground) :
    evaluationGraph C H ∈ C.valueDomain H := by
  exact (extension_mem _ _ _ _).mpr
    ⟨evaluationName C,hname,evaluation_name_valid C,evaluation_name_value C H⟩

theorem evaluation_graph_surjective (C : Context.{u,u} Q)
    (A : C.Name → ℕ → Set Q)
    (hA : ∀ τ n, A τ n ⊆ deciding C τ n ∧ MaximalAntichain (A τ n))
    (hground : ∀ τ n, downwardClosure (A τ n) ∈ C.groundFamily)
    (hcodes : ∀ τ, rowCode C (positiveRows C τ (A τ)) ∈ C.ground)
    (H : PFilter Q) (hH : GenericFor H C.groundFamily) :
    ∀ x ∈ C.valueDomain H, x ⊆ ZFSet.omega →
      ∃ b ∈ codeSet C, ZFSet.pair b x ∈ evaluationGraph C H := by
  intro x hx hxω
  obtain ⟨τ,hτ,hτname,hτval⟩ := (extension_mem _ _ _ x).mp hx
  let σ : C.Name := ⟨τ,hτ,hτname⟩
  let B := positiveRows C σ (A σ)
  let b := rowCode C B
  have hB : ∀ n, Antichain (B n) :=
    positive_rows_antichain C σ (A σ) (fun n => (hA σ n).2.1)
  have hb : b ∈ codeSet C := (code_set_members C b).mpr
    ⟨row_code_subset C B,hcodes σ,by rw [code_row_inverse]; exact hB⟩
  refine ⟨b,hb,(evaluation_graph_members C H b x).mpr ⟨hb,?_⟩⟩
  change x = evaluation (C.filterCode H) (niceName C (codeRow C (rowCode C B)))
  rw [code_row_inverse, nice_replacement_value C σ (A σ) (hA σ) (hground σ) H hH]
  change x = (evaluation (C.filterCode H) τ).sep (fun n => n ∈ ZFSet.omega)
  rw [hτval]
  ext n
  simp only [ZFSet.mem_sep]
  exact ⟨fun hn => ⟨hn,hxω hn⟩,And.left⟩

end
end Lemmatheca.SetTheory.NiceNamesAndCohenContinuum
