import Lemmatheca.ConstructibleInnerModel.Axioms
import Lemmatheca.InaccessibleCardinals.WellOrders
import Mathlib.ModelTheory.Encoding
import Mathlib.Order.Fin.Tuple
import Mathlib.Data.Sum.Order

namespace Lemmatheca.SetTheory.ConstructibleInnerModel
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
open Lemmatheca.SetTheory.ConstructibleHierarchy
open Lemmatheca.SetTheory.InaccessibleCardinals
universe u
noncomputable section

abbrev FormulaShape := Σ n : ℕ, membershipLanguage.BoundedFormula Empty (n+1)
def formulaNumber (p : FormulaShape) : ℕ := by
  let : Countable membershipLanguage.Symbols := countable_membership_symbols
  let : Countable FormulaShape :=
    Function.Injective.countable
      (f := fun p : FormulaShape => (⟨p.1+1,p.2⟩ : Σ n, membershipLanguage.BoundedFormula Empty n))
      (by
        rintro ⟨n,p⟩ ⟨m,q⟩ h
        have hnm : n = m := Nat.add_right_cancel (congrArg Sigma.fst h)
        subst m
        have hpq : HEq p q := (Sigma.mk.inj h).2
        cases hpq
        rfl)
  exact @Encodable.encode FormulaShape (Encodable.ofCountable FormulaShape) p
theorem formulaNumber_injective : Function.Injective formulaNumber := by
  let : Countable membershipLanguage.Symbols := countable_membership_symbols
  let : Countable FormulaShape :=
    Function.Injective.countable
      (f := fun p : FormulaShape => (⟨p.1+1,p.2⟩ : Σ n, membershipLanguage.BoundedFormula Empty n))
      (by
        rintro ⟨n,p⟩ ⟨m,q⟩ h
        have hnm : n = m := Nat.add_right_cancel (congrArg Sigma.fst h)
        subst m
        have hpq : HEq p q := (Sigma.mk.inj h).2
        cases hpq
        rfl)
  let : Encodable FormulaShape := Encodable.ofCountable FormulaShape
  change Function.Injective (@Encodable.encode FormulaShape inferInstance)
  exact Encodable.encode_injective

def tupleLex {M : Type u} (r : M → M → Prop) {n} (a b : Fin n → M) : Prop :=
  ∃ i, (∀ j, j < i → a j = b j) ∧ r (a i) (b i)
theorem tupleLex_wellOrder {M : Type u} (r : M → M → Prop) [IsWellOrder M r]
    (n : ℕ) : IsWellOrder (Fin n → M) (tupleLex r) := by
  classical
  induction n with
  | zero =>
    exact {wf := WellFounded.intro (fun a => Acc.intro a (fun b hb => Fin.elim0 hb.choose))
           trichotomous := fun a b _ _ => Subsingleton.elim a b}
  | succ n ih =>
    let : IsWellOrder (Fin n → M) (tupleLex r) := ih
    let e : (Fin (n+1) → M) ≃ M × (Fin n → M) := (Fin.consEquiv (fun _ : Fin (n+1) => M)).symm
    have he (a b : Fin (n+1) → M) : tupleLex r a b ↔
        Prod.Lex r (tupleLex r) (e a) (e b) := by
      rw [Prod.lex_iff]
      change Pi.Lex (· < ·) (fun {_} => r) a b ↔ _
      conv_lhs => rw [← Fin.cons_self_tail a,← Fin.cons_self_tail b]
      exact Fin.pi_lex_lt_cons_cons (fun {_} => r)
    have hh := Function.Injective.isWellOrder (Prod.Lex r (tupleLex r)) e.injective
    have hrel : tupleLex r = (Prod.Lex r (tupleLex r)).onFun e := by
      funext a b
      exact propext (he a b)
    rw [hrel]
    exact hh

def codeShape (M : ZFSet.{u}) (c : DefinitionCode M) : FormulaShape := ⟨c.1,c.2.1⟩
def codeLt (M : ZFSet.{u}) (r : M → M → Prop) (c d : DefinitionCode M) : Prop :=
  formulaNumber (codeShape M c) < formulaNumber (codeShape M d) ∨
    ∃ h : c.1 = d.1, formulaNumber (codeShape M c) = formulaNumber (codeShape M d) ∧
      tupleLex r c.2.2 (fun i => d.2.2 (Fin.cast h i))
theorem codeLt_wellOrder (M : ZFSet.{u}) (r : M → M → Prop) [IsWellOrder M r] :
    IsWellOrder (DefinitionCode M) (codeLt M r) := by
  classical
  refine {wf := ?_,trichotomous := ?_}
  · intro c d hcd hdc
    have heq : formulaNumber (codeShape M c) = formulaNumber (codeShape M d) := by
      apply le_antisymm
      · exact le_of_not_gt (fun h => hdc (Or.inl h))
      · exact le_of_not_gt (fun h => hcd (Or.inl h))
    have hshape := formulaNumber_injective heq
    obtain ⟨n,p,a⟩ := c
    obtain ⟨m,q,b⟩ := d
    change (⟨n,p⟩ : FormulaShape) = ⟨m,q⟩ at hshape
    cases hshape
    let := tupleLex_wellOrder r n
    have hab : a = b := Std.Trichotomous.trichotomous a b
      (fun h => hcd (Or.inr ⟨rfl,rfl,h⟩)) (fun h => hdc (Or.inr ⟨rfl,rfl,h⟩))
    cases hab
    rfl
  · apply WellFounded.wellFounded_iff_has_min.mpr
    intro S hS
    obtain ⟨c0,hc0,hminnum⟩ := (measure (fun c : DefinitionCode M => formulaNumber (codeShape M c))).wf.has_min S hS
    obtain ⟨n,p,a0⟩ := c0
    let T : Set (Fin n → M) := {a | (⟨n,p,a⟩ : DefinitionCode M) ∈ S}
    let hw := tupleLex_wellOrder r n
    obtain ⟨a,ha,hmina⟩ := hw.wf.has_min T ⟨a0,hc0⟩
    refine ⟨⟨n,p,a⟩,ha,?_⟩
    intro d hd hlt
    rcases hlt with hn | ⟨hAr,heq,hlex⟩
    · exact hminnum d hd hn
    · have hshape := formulaNumber_injective heq
      obtain ⟨m,q,b⟩ := d
      change (⟨m,q⟩ : FormulaShape) = ⟨n,p⟩ at hshape
      cases hshape
      exact hmina b hd (by simpa using hlex)

def leastCode (M : ZFSet.{u}) (r : M → M → Prop) [IsWellOrder M r] (X : Def M) :
    DefinitionCode M := by
  let := codeLt_wellOrder M r
  exact (IsWellOrder.wf : WellFounded (codeLt M r)).min
    {c | definedSubset M c = X.val} ((Def_members M X.val).mp X.property)
theorem leastCode_spec (M : ZFSet.{u}) (r : M → M → Prop) [IsWellOrder M r]
    (X : Def M) : definedSubset M (leastCode M r X) = X.val ∧
      ∀ c, definedSubset M c = X.val → ¬codeLt M r c (leastCode M r X) := by
  let := codeLt_wellOrder M r
  let wf : WellFounded (codeLt M r) := IsWellOrder.wf
  have he : ({c | definedSubset M c = X.val} : Set (DefinitionCode M)).Nonempty :=
    (Def_members M X.val).mp X.property
  exact ⟨wf.min_mem _ he,fun c hc => wf.not_lt_min _ hc⟩
theorem leastCode_injective (M : ZFSet.{u}) (r : M → M → Prop) [IsWellOrder M r] :
    Function.Injective (leastCode M r) := by
  intro X Y h
  apply Subtype.ext
  exact (leastCode_spec M r X).1.symm.trans
    ((congrArg (definedSubset M) h).trans (leastCode_spec M r Y).1)
def defOrder (M : ZFSet.{u}) (r : M → M → Prop) [IsWellOrder M r] (X Y : Def M) : Prop :=
  codeLt M r (leastCode M r X) (leastCode M r Y)
theorem defOrder_wellOrder (M : ZFSet.{u}) (r : M → M → Prop) [IsWellOrder M r] :
    IsWellOrder (Def M) (defOrder M r) := by
  let := codeLt_wellOrder M r
  exact Function.Injective.isWellOrder (codeLt M r) (leastCode_injective M r)

def graphRelation (M R : ZFSet.{u}) (x y : M) : Prop := ZFSet.pair x.val y.val ∈ R
def successorComparison (M R : ZFSet.{u}) (hR : IsSetWellOrder M R) (x y : Def M) : Prop :=
  let _ : IsWellOrder M (graphRelation M R) := hR.2
  (x.val ∈ M ∧ y.val ∈ M ∧ ZFSet.pair x.val y.val ∈ R) ∨
  (x.val ∈ M ∧ y.val ∉ M) ∨
  (x.val ∉ M ∧ y.val ∉ M ∧ defOrder M (graphRelation M R) x y)
def successorGraph (M R : ZFSet.{u}) (hR : IsSetWellOrder M R) : ZFSet.{u} :=
  ZFSet.sep (fun p => ∃ x y : Def M, p = ZFSet.pair x.val y.val ∧ successorComparison M R hR x y)
    (ZFSet.prod (Def M) (Def M))
theorem successorGraph_members (M R : ZFSet.{u}) (hR : IsSetWellOrder M R)
    (x y : Def M) :
    ZFSet.pair x.val y.val ∈ successorGraph M R hR ↔ successorComparison M R hR x y := by
  rw [successorGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,u,v,heq,hcmp⟩
    obtain ⟨hu,hv⟩ := ZFSet.pair_inj.mp heq
    have hxu : x = u := Subtype.ext hu
    have hyv : y = v := Subtype.ext hv
    simpa only [hxu,hyv] using hcmp
  · intro hcmp
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨x.property,y.property⟩,x,y,rfl,hcmp⟩

def InitialSegmentSets (A B R S : ZFSet.{u}) : Prop :=
  A ⊆ B ∧ (∀ x ∈ A, ∀ y ∈ A, ZFSet.pair x y ∈ R ↔ ZFSet.pair x y ∈ S) ∧
    ∀ x ∈ A, ∀ y ∈ B, ZFSet.pair y x ∈ S → y ∈ A
theorem successorGraph_spec (M R : ZFSet.{u}) (hM : M.IsTransitive)
    (hR : IsSetWellOrder M R) : IsSetWellOrder (Def M) (successorGraph M R hR) ∧
      InitialSegmentSets M (Def M) R (successorGraph M R hR) := by
  classical
  have hi : M ⊆ Def M := (transitive_Def M hM).1
  let r := graphRelation M R
  let : IsWellOrder M r := hR.2
  let : IsWellOrder (Def M) (defOrder M r) := defOrder_wellOrder M r
  let e : Def M → M ⊕ Def M := fun x =>
    if hx : x.val ∈ M then Sum.inl ⟨x.val,hx⟩ else Sum.inr x
  have he : Function.Injective e := by
    intro x y h
    by_cases hx : x.val ∈ M <;> by_cases hy : y.val ∈ M
    · simp only [e,dite_eq_left hx,dite_eq_left hy,Sum.inl.injEq] at h
      exact Subtype.ext (congrArg (fun z : M => z.val) h)
    · simp only [e,dite_eq_left hx,dite_eq_right hy,Sum.inl_ne_inr] at h
    · simp only [e,dite_eq_right hx,dite_eq_left hy,Sum.inr_ne_inl] at h
    · simpa only [e,dite_eq_right hx,dite_eq_right hy,Sum.inr.injEq] using h
  have hr : successorComparison M R hR = (Sum.Lex r (defOrder M r)).onFun e := by
    funext x y
    apply propext
    by_cases hx : x.val ∈ M <;> by_cases hy : y.val ∈ M <;>
      simp [successorComparison,e,hx,hy,Function.onFun,r,graphRelation]
  have hw : IsWellOrder (Def M) (successorComparison M R hR) := by
    rw [hr]
    exact he.isWellOrder (Sum.Lex r (defOrder M r))
  have hg : graphRelation (Def M) (successorGraph M R hR) = successorComparison M R hR := by
    funext x y
    exact propext (successorGraph_members M R hR x y)
  refine ⟨⟨?_,?_⟩,hi,?_,?_⟩
  · intro p hp
    exact (ZFSet.mem_sep.mp hp).1
  · change IsWellOrder (Def M) (graphRelation (Def M) (successorGraph M R hR))
    rw [hg]
    exact hw
  · intro x hx y hy
    have h := successorGraph_members M R hR ⟨x,hi hx⟩ ⟨y,hi hy⟩
    simpa only [successorComparison,hx,hy,true_and,not_true_eq_false,and_false,
      false_and,or_false] using h.symm
  · intro x hx y hy hyx
    have h := (successorGraph_members M R hR ⟨y,hy⟩ ⟨x,hi hx⟩).mp hyx
    exact (by simpa only [successorComparison,hx,true_and,not_true_eq_false,and_false,
      false_and,or_false] using h : y ∈ M ∧ ZFSet.pair y x ∈ R).1


/-- The fallback makes the set-valued rule total even on an invalid history.
The well-order theorem proves it is never used in the actual recursion. -/
def orderGraph (a : Ordinal.{u}) : ZFSet.{u} := by
  classical
  exact Ordinal.limitRecOn a ∅
    (fun b R => if hR : IsSetWellOrder (level b) R then successorGraph (level b) R hR else ∅)
    (fun l _ prev => ZFSet.iUnion (fun b : Set.Iio l => prev b.val b.property))
theorem orderGraph_zero : orderGraph (0 : Ordinal.{u}) = ∅ := by
  simp only [orderGraph,Ordinal.limitRecOn_zero]
theorem orderGraph_limit (l : Ordinal.{u}) (hl : Order.IsSuccLimit l) :
    orderGraph l = ZFSet.iUnion (fun b : Set.Iio l => orderGraph b.val) := by
  simp only [orderGraph,Ordinal.limitRecOn_limit l _ _ _ hl]
private theorem initialSegment_refl (A R : ZFSet.{u}) : InitialSegmentSets A A R R := by
  exact ⟨fun _ h => h,fun _ _ _ _ => Iff.rfl,fun _ _ _ h _ => h⟩

private theorem initialSegment_trans {A B C R S T : ZFSet.{u}}
    (h : InitialSegmentSets A B R S) (k : InitialSegmentSets B C S T) :
    InitialSegmentSets A C R T := by
  refine ⟨fun _ hx => k.1 (h.1 hx),?_,?_⟩
  · intro x hx y hy
    exact (h.2.1 x hx y hy).trans (k.2.1 x (h.1 hx) y (h.1 hy))
  · intro x hx y hy hyx
    have hyB := k.2.2 x (h.1 hx) y hy hyx
    exact h.2.2 x hx y hyB ((k.2.1 y hyB x (h.1 hx)).mpr hyx)

private theorem initialSegment_limit (l : Ordinal.{u}) (hl : Order.IsSuccLimit l)
    (ih : ∀ b < l, IsSetWellOrder (level b) (orderGraph b) ∧
      ∀ c ≤ b, InitialSegmentSets (level c) (level b) (orderGraph c) (orderGraph b))
    (b : Ordinal.{u}) (hb : b < l) :
    InitialSegmentSets (level b) (level l) (orderGraph b) (orderGraph l) := by
  have hin (c : Ordinal.{u}) (hc : c < l) {p : ZFSet.{u}} (hp : p ∈ orderGraph c) :
      p ∈ orderGraph l := by
    rw [orderGraph_limit l hl,ZFSet.mem_iUnion]
    exact ⟨⟨c,hc⟩,hp⟩
  refine ⟨level_monotone hb.le,?_,?_⟩
  · intro x hx y hy
    refine ⟨hin b hb,?_⟩
    intro hxy
    rw [orderGraph_limit l hl,ZFSet.mem_iUnion] at hxy
    obtain ⟨⟨c,hc⟩,hxy⟩ := hxy
    have hm : max b c < l := max_lt hb hc
    have hcb := (ih (max b c) hm).2 c (le_max_right _ _)
    have hbb := (ih (max b c) hm).2 b (le_max_left _ _)
    have hmem := ZFSet.pair_mem_prod.mp ((ih c hc).1.1 hxy)
    exact (hbb.2.1 x hx y hy).mpr ((hcb.2.1 x hmem.1 y hmem.2).mp hxy)
  · intro x hx y hy hyx
    rw [orderGraph_limit l hl,ZFSet.mem_iUnion] at hyx
    obtain ⟨⟨c,hc⟩,hyx⟩ := hyx
    have hm : max b c < l := max_lt hb hc
    have hcb := (ih (max b c) hm).2 c (le_max_right _ _)
    have hbb := (ih (max b c) hm).2 b (le_max_left _ _)
    have hmem := ZFSet.pair_mem_prod.mp ((ih c hc).1.1 hyx)
    exact hbb.2.2 x hx y (hcb.1 hmem.1) ((hcb.2.1 y hmem.1 x hmem.2).mp hyx)

private theorem orderGraph_limit_wellOrder (l : Ordinal.{u}) (hl : Order.IsSuccLimit l)
    (ih : ∀ b < l, IsSetWellOrder (level b) (orderGraph b) ∧
      ∀ c ≤ b, InitialSegmentSets (level c) (level b) (orderGraph c) (orderGraph b)) :
    IsSetWellOrder (level l) (orderGraph l) := by
  classical
  have hseg := initialSegment_limit l hl ih
  have hinc (b : Ordinal.{u}) (hb : b < l) := level_monotone hb.le
  refine ⟨?_,?_⟩
  · intro p hp
    rw [orderGraph_limit l hl,ZFSet.mem_iUnion] at hp
    obtain ⟨⟨b,hb⟩,hp⟩ := hp
    obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp ((ih b hb).1.1 hp)
    exact ZFSet.pair_mem_prod.mpr ⟨hinc b hb hx,hinc b hb hy⟩
  · refine { trichotomous := ?_, wf := ?_ }
    · intro x y hxy hyx
      obtain ⟨b,hb,hx⟩ := (level_limit_members l hl x.val).mp x.property
      obtain ⟨c,hc,hy⟩ := (level_limit_members l hl y.val).mp y.property
      let d := max b c
      have hd : d < l := max_lt hb hc
      have hxd : x.val ∈ level d := level_monotone (le_max_left b c) hx
      have hyd : y.val ∈ level d := level_monotone (le_max_right b c) hy
      let : IsWellOrder (level d) (graphRelation (level d) (orderGraph d)) := (ih d hd).1.2
      have he : (⟨x.val,hxd⟩ : level d) = ⟨y.val,hyd⟩ :=
        Std.Trichotomous.trichotomous (r := graphRelation (level d) (orderGraph d))
          _ _ (fun h => hxy ((hseg d hd).2.1 _ hxd _ hyd |>.mp h))
          (fun h => hyx ((hseg d hd).2.1 _ hyd _ hxd |>.mp h))
      exact Subtype.ext (congrArg (fun z : level d => z.val) he)
    · rw [WellFounded.wellFounded_iff_has_min]
      intro S hS
      obtain ⟨x,hxS⟩ := hS
      obtain ⟨b,hb,hxb⟩ := (level_limit_members l hl x.val).mp x.property
      let e : level b → level l := fun z => ⟨z.val,hinc b hb z.property⟩
      let T : Set (level b) := {z | e z ∈ S}
      have hT : T.Nonempty := ⟨⟨x.val,hxb⟩,by change (⟨x.val,_⟩ : level l) ∈ S; exact hxS⟩
      obtain ⟨m,hm,hmin⟩ := (ih b hb).1.2.wf.has_min T hT
      refine ⟨e m,hm,?_⟩
      intro y hyS hym
      have hyb : y.val ∈ level b := (hseg b hb).2.2 m.val m.property y.val y.property hym
      let yb : level b := ⟨y.val,hyb⟩
      have hyT : yb ∈ T := by change (⟨y.val,_⟩ : level l) ∈ S; exact hyS
      exact hmin yb hyT ((hseg b hb).2.1 y.val hyb m.val m.property |>.mpr hym)

theorem coherent_orderGraphs (a : Ordinal.{u}) :
    IsSetWellOrder (level a) (orderGraph a) ∧
      ∀ b ≤ a, InitialSegmentSets (level b) (level a) (orderGraph b) (orderGraph a) := by
  classical
  induction a using Ordinal.limitRecOn with
  | zero =>
    have he : IsSetWellOrder (∅ : ZFSet.{u}) ∅ := by
      refine ⟨fun _ h => (ZFSet.notMem_empty _ h).elim,?_⟩
      let : IsEmpty (∅ : ZFSet.{u}) := ⟨fun x => ZFSet.notMem_empty _ x.property⟩
      exact { trichotomous := fun x => isEmptyElim x, wf := ⟨fun x => isEmptyElim x⟩ }
    refine ⟨by simpa only [level_zero,orderGraph_zero] using he,?_⟩
    intro b hb
    have h : b = 0 := le_antisymm hb bot_le
    subst b
    exact initialSegment_refl _ _
  | add_one a ih =>
    have he : orderGraph (a+1) = successorGraph (level a) (orderGraph a) ih.1 := by
      unfold orderGraph
      rw [Ordinal.limitRecOn_add_one]
      exact dite_eq_left ih.1
    have hs := successorGraph_spec (level a) (orderGraph a) (level_transitive a) ih.1
    have hstep : InitialSegmentSets (level a) (level (a+1)) (orderGraph a) (orderGraph (a+1)) := by
      simpa only [level_successor,he] using hs.2
    refine ⟨by simpa only [level_successor,he] using hs.1,?_⟩
    intro b hb
    rcases lt_or_eq_of_le hb with hb | rfl
    · have hba : b ≤ a := by simpa only [← Order.succ_eq_add_one,Order.lt_succ_iff] using hb
      exact initialSegment_trans (ih.2 b hba) hstep
    · exact initialSegment_refl _ _
  | limit l hl ih =>
    refine ⟨orderGraph_limit_wellOrder l hl ih,?_⟩
    intro b hb
    rcases lt_or_eq_of_le hb with hb | rfl
    · exact initialSegment_limit l hl ih b hb
    · exact initialSegment_refl _ _
theorem orderGraph_successor (a : Ordinal.{u}) :
    orderGraph (a+1) = successorGraph (level a) (orderGraph a) (coherent_orderGraphs a).1  := by
  classical
  have he : orderGraph (a+1) =
      (if hR : IsSetWellOrder (level a) (orderGraph a) then
        successorGraph (level a) (orderGraph a) hR else ∅) := by
    unfold orderGraph
    rw [Ordinal.limitRecOn_add_one]
  exact he.trans (dite_eq_left (coherent_orderGraphs a).1)
theorem orderGraph_unique (R : Ordinal.{u} → ZFSet.{u}) (h0 : R 0 = ∅)
    (hw : ∀ a, IsSetWellOrder (level a) (R a))
    (hs : ∀ a, R (a+1) = successorGraph (level a) (R a) (hw a))
    (hl : ∀ l, Order.IsSuccLimit l → R l = ZFSet.iUnion (fun b : Set.Iio l => R b.val)) :
    R = orderGraph := by
  funext a
  induction a using Ordinal.limitRecOn with
  | zero => exact h0.trans orderGraph_zero.symm
  | add_one a ih =>
    rw [hs,orderGraph_successor]
    have he (A B : ZFSet.{u}) (h : A = B) (ha : IsSetWellOrder (level a) A)
        (hb : IsSetWellOrder (level a) B) :
        successorGraph (level a) A ha = successorGraph (level a) B hb := by
      cases h
      rfl
    exact he _ _ ih _ _
  | limit l hlim ih =>
    rw [hl l hlim,orderGraph_limit l hlim]
    congr 1
    funext b
    exact ih b.val b.property

def parentStage (x : ZFSet.{u}) (_hx : IsConstructible x) : Ordinal.{u} :=
  sInf {a | x ∈ Def (level a)}
theorem parentStage_spec (x : ZFSet.{u}) (hx : IsConstructible x) :
    IsLeast {a | x ∈ Def (level a)} (parentStage x hx) := by
  have hex (a : Ordinal.{u}) (ha : x ∈ level a) : ∃ b, x ∈ Def (level b) := by
    induction a using Ordinal.limitRecOn with
    | zero => rw [level_zero] at ha; exact (ZFSet.notMem_empty _ ha).elim
    | add_one a ih => exact ⟨a,by simpa only [level_successor] using ha⟩
    | limit l hl ih =>
      obtain ⟨b,hb,hx⟩ := (level_limit_members l hl x).mp ha
      exact ih b hb hx
  obtain ⟨a,ha⟩ := hx
  have hn : ({a | x ∈ Def (level a)} : Set Ordinal.{u}).Nonempty := hex a ha
  exact ⟨csInf_mem hn,fun a ha => csInf_le ⟨0,fun _ _ => bot_le⟩ ha⟩
def firstCode (x : ZFSet.{u}) (hx : IsConstructible x) :
    DefinitionCode (level (parentStage x hx)) := by
  let : IsWellOrder (level (parentStage x hx))
      (graphRelation _ (orderGraph (parentStage x hx))) :=
    (coherent_orderGraphs (parentStage x hx)).1.2
  exact leastCode _ (graphRelation _ (orderGraph (parentStage x hx)))
    ⟨x,(parentStage_spec x hx).1⟩
theorem firstCode_spec (x : ZFSet.{u}) (hx : IsConstructible x) :
    definedSubset (level (parentStage x hx)) (firstCode x hx) = x ∧
      ∀ c, definedSubset (level (parentStage x hx)) c = x →
        ¬codeLt _ (graphRelation _ (orderGraph (parentStage x hx))) c (firstCode x hx) := by
  let : IsWellOrder (level (parentStage x hx))
      (graphRelation _ (orderGraph (parentStage x hx))) :=
    (coherent_orderGraphs (parentStage x hx)).1.2
  exact leastCode_spec _ _ _
theorem first_membership_parent (x : ZFSet.{u}) (hx : IsConstructible x) (d : Ordinal.{u})
    (hfirst : leastStage x hx = d+1) : parentStage x hx = d := by
  apply le_antisymm
  · apply (parentStage_spec x hx).2
    have hm := (leastStage_spec x hx).1
    change x ∈ level (leastStage x hx) at hm
    rw [hfirst,level_successor] at hm
    exact hm
  · have hm : x ∈ level (parentStage x hx+1) := by
      rw [level_successor]
      exact (parentStage_spec x hx).1
    have hb := (leastStage_spec x hx).2 hm
    rw [hfirst] at hb
    simpa only [← Order.succ_eq_add_one,Order.succ_le_succ_iff] using hb

def restrictedOrder (x : LDomain.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => p ∈ orderGraph (leastStage x.val x.property)) (ZFSet.prod x.val x.val)
theorem restrictedOrder_spec (x : LDomain.{u}) :
    IsSetWellOrder x.val (restrictedOrder x) ∧
      ∀ y z : x.val, ZFSet.pair y.val z.val ∈ restrictedOrder x ↔
        ZFSet.pair y.val z.val ∈ orderGraph (leastStage x.val x.property) := by
  let b := leastStage x.val x.property
  have hx : x.val ∈ level b := (leastStage_spec x.val x.property).1
  let e : x.val → level b := fun y => ⟨y.val,level_transitive b x.val hx y.property⟩
  have he : Function.Injective e := fun y z h => Subtype.ext (show y.val = z.val from congrArg (fun v : level b => v.val) h)
  have hp (y z : x.val) : ZFSet.pair y.val z.val ∈ restrictedOrder x ↔
      ZFSet.pair y.val z.val ∈ orderGraph b := by
    simp only [restrictedOrder,ZFSet.mem_sep,ZFSet.pair_mem_prod,y.property,z.property,
      and_self,true_and]
    rfl
  refine ⟨⟨?_,?_⟩,hp⟩
  · exact fun _ h => (ZFSet.mem_sep.mp h).1
  · let : IsWellOrder (level b) (graphRelation (level b) (orderGraph b)) :=
      (coherent_orderGraphs b).1.2
    have hi := Function.Injective.isWellOrder (graphRelation (level b) (orderGraph b)) he
    have hrel : (fun y z : x.val => ZFSet.pair y.val z.val ∈ restrictedOrder x) =
        (graphRelation (level b) (orderGraph b)).onFun e := by
      funext y z
      exact propext (hp y z)
    rw [hrel]
    exact hi

end
end Lemmatheca.SetTheory.ConstructibleInnerModel
