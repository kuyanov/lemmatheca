import Lemmatheca.InaccessibleCardinals.CardinalBounds
import Lemmatheca.Absoluteness.BoundedRelations

namespace Lemmatheca.SetTheory.InaccessibleCardinals
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
universe u
noncomputable section

def relationDomainTest {n} (R x : Fin n) : DeltaZero n :=
  .ball R (.bex x.castSucc (.bex x.castSucc.castSucc
    (orderedPairTest (Fin.last n).castSucc.castSucc
      (Fin.last (n+1)).castSucc (Fin.last (n+2)))))

def irreflexiveTest {n} (R x : Fin n) : DeltaZero n :=
  .ball x (.neg (relationTest (Fin.last n) (Fin.last n) R.castSucc))

def transitiveRelationTest {n} (R x : Fin n) : DeltaZero n :=
  .ball x (.ball x.castSucc (.ball x.castSucc.castSucc
    (.imp (.conj
      (relationTest (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc
        R.castSucc.castSucc.castSucc)
      (relationTest (Fin.last (n+1)).castSucc (Fin.last (n+2))
        R.castSucc.castSucc.castSucc))
      (relationTest (Fin.last n).castSucc.castSucc (Fin.last (n+2))
        R.castSucc.castSucc.castSucc))))

def comparableTest {n} (R x : Fin n) : DeltaZero n :=
  .ball x (.ball x.castSucc
    (.disj (.equal (Fin.last n).castSucc (Fin.last (n+1)))
      (.disj (relationTest (Fin.last n).castSucc (Fin.last (n+1)) R.castSucc.castSucc)
        (relationTest (Fin.last (n+1)) (Fin.last n).castSucc R.castSucc.castSucc))))

def nonemptyTest {n} (A : Fin n) : DeltaZero n :=
  .bex A (.equal (Fin.last n) (Fin.last n))

def minimumTest {n} (R A : Fin n) : DeltaZero n :=
  .bex A (.ball A.castSucc
    (.disj (.equal (Fin.last n).castSucc (Fin.last (n+1)))
      (relationTest (Fin.last n).castSucc (Fin.last (n+1)) R.castSucc.castSucc)))

/-- Only the subset variable is unrestricted. Each individual relation test is
 bounded by the supplied relation and its Kuratowski-pair candidates. -/
def wellOrderFormula {n} (R x : Fin n) : membershipLanguage.BoundedFormula Empty n :=
  (DeltaZero.conj (relationDomainTest R x)
    (.conj (irreflexiveTest R x) (.conj (transitiveRelationTest R x) (comparableTest R x)))).toShared ⊓
  (((subsetTest (Fin.last n) x.castSucc).conj (nonemptyTest (Fin.last n))).toShared.imp
    (minimumTest R.castSucc (Fin.last n)).toShared).all

def IsSetWellOrder (x R : ZFSet.{u}) : Prop :=
  R ⊆ ZFSet.prod x x ∧ IsWellOrder x (fun a b : x => ZFSet.pair a.val b.val ∈ R)

private theorem dzConj {n} (p q : DeltaZero n) (a : Fin n → ZFSet.{u}) :
    (p.conj q).Holds (fun x y => x ∈ y) a ↔
      p.Holds (fun x y => x ∈ y) a ∧ q.Holds (fun x y => x ∈ y) a := by
  classical
  simp [DeltaZero.conj,DeltaZero.neg,DeltaZero.Holds]
private theorem dzDisj {n} (p q : DeltaZero n) (a : Fin n → ZFSet.{u}) :
    (p.disj q).Holds (fun x y => x ∈ y) a ↔
      p.Holds (fun x y => x ∈ y) a ∨ q.Holds (fun x y => x ∈ y) a := by
  classical
  simp only [DeltaZero.disj,DeltaZero.neg,DeltaZero.Holds,imp_false]
  tauto
private theorem dzPair {n} (z x y : Fin n) (a : Fin n → ZFSet.{u}) :
    (orderedPairTest z x y).Holds (fun x y => x ∈ y) a ↔ a z = ZFSet.pair (a x) (a y) :=
  (DeltaZero.toShared_realize _ _ _).symm.trans (orderedPairTest_correct _ _ _ _)
private theorem dzRel {n} (x y R : Fin n) (a : Fin n → ZFSet.{u}) :
    (relationTest x y R).Holds (fun x y => x ∈ y) a ↔ ZFSet.pair (a x) (a y) ∈ a R :=
  (DeltaZero.toShared_realize _ _ _).symm.trans (relationTest_correct _ _ _ _)
private theorem dzSubset {n} (x y : Fin n) (a : Fin n → ZFSet.{u}) :
    (subsetTest x y).Holds (fun x y => x ∈ y) a ↔ a x ⊆ a y :=
  (DeltaZero.toShared_realize _ _ _).symm.trans (subsetTest_correct _ _ _)
private theorem woSem {n} (R x : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (wellOrderFormula R x) a ↔
      ((∀ z ∈ a R, ∃ y ∈ a x, ∃ w ∈ a x, z = ZFSet.pair y w) ∧
      ((∀ y ∈ a x, ZFSet.pair y y ∉ a R) ∧
      ((∀ y ∈ a x, ∀ z ∈ a x, ∀ w ∈ a x,
        ZFSet.pair y z ∈ a R ∧ ZFSet.pair z w ∈ a R → ZFSet.pair y w ∈ a R) ∧
      (∀ y ∈ a x, ∀ z ∈ a x, y = z ∨ ZFSet.pair y z ∈ a R ∨ ZFSet.pair z y ∈ a R)))) ∧
      (∀ A : ZFSet.{u}, A ⊆ a x ∧ A.Nonempty →
        ∃ m ∈ A, ∀ z ∈ A, m = z ∨ ZFSet.pair m z ∈ a R) := by
  let := universeMembershipStructure.{u}
  change (wellOrderFormula R x).Realize Empty.elim a ↔ _
  simp only [wellOrderFormula,BoundedFormula.realize_inf,BoundedFormula.realize_all,
    BoundedFormula.realize_imp,DeltaZero.toShared_realize,dzConj]
  simp only [relationDomainTest,irreflexiveTest,transitiveRelationTest,comparableTest,
    nonemptyTest,minimumTest,DeltaZero.bex_realize,dzConj,dzDisj,dzPair,dzRel,dzSubset,
    DeltaZero.neg,DeltaZero.Holds,Fin.snoc_last,Fin.snoc_castSucc]
  simp only [and_true]
  rfl

theorem wellOrderFormula_correct {n} (R x : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (wellOrderFormula R x) a ↔ IsSetWellOrder (a x) (a R) := by
  classical
  rw [woSem]
  constructor
  · rintro ⟨⟨hd,hi,ht,hc⟩,hm⟩
    refine ⟨?_,?_⟩
    · intro z hz
      obtain ⟨y,hy,w,hw,rfl⟩ := hd z hz
      exact ZFSet.pair_mem_prod.mpr ⟨hy,hw⟩
    · let r : a x → a x → Prop := fun y z => ZFSet.pair y.val z.val ∈ a R
      apply (WellFounded.isWellOrder_iff_exists_not_lt_and_eq_or_gt).mpr
      intro S hS
      let A := (a x).sep (fun y => ∃ hy : y ∈ a x, (⟨y,hy⟩ : a x) ∈ S)
      have hA : A ⊆ a x := fun _ hy => (ZFSet.mem_sep.mp hy).1
      have hAe : A.Nonempty := by
        obtain ⟨y,hy⟩ := hS
        exact ⟨y.val,ZFSet.mem_sep.mpr ⟨y.property,y.property,hy⟩⟩
      obtain ⟨m,hmA,hmin⟩ := hm A ⟨hA,hAe⟩
      have hmS : (⟨m,hA hmA⟩ : a x) ∈ S := by
        obtain ⟨_,hm'⟩ := (ZFSet.mem_sep.mp hmA).2
        exact hm'
      refine ⟨⟨m,hA hmA⟩,hmS,fun z hz => ?_⟩
      have hzA : z.val ∈ A := ZFSet.mem_sep.mpr ⟨z.property,z.property,hz⟩
      have hcomp := hmin z.val hzA
      constructor
      · intro hzm
        rcases hcomp with he | hmz
        · exact hi m (hA hmA) (by simpa only [he] using hzm)
        · exact hi m (hA hmA) (ht m (hA hmA) z.val z.property m (hA hmA) ⟨hmz,hzm⟩)
      · exact hcomp.imp Subtype.ext id
  · rintro ⟨hd,hr⟩
    let := hr
    refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
    · intro z hz
      obtain ⟨y,hy,w,hw,he,_⟩ := ZFSet.mem_pairSep.mp (hd hz)
      exact ⟨y,hy,w,hw,he⟩
    · intro y hy
      exact irrefl_of (fun y z : a x => ZFSet.pair y.val z.val ∈ a R) ⟨y,hy⟩
    · intro y hy z hz w hw h
      exact trans_of (fun y z : a x => ZFSet.pair y.val z.val ∈ a R)
        (a := ⟨y,hy⟩) (b := ⟨z,hz⟩) (c := ⟨w,hw⟩) h.1 h.2
    · intro y hy z hz
      exact (trichotomous_of (fun y z : a x => ZFSet.pair y.val z.val ∈ a R)
        ⟨y,hy⟩ ⟨z,hz⟩).elim (fun h => Or.inr (Or.inl h))
        (fun h => h.elim (fun he => Or.inl (congrArg Subtype.val he)) (fun h => Or.inr (Or.inr h)))
    · intro A hA
      let S : Set (a x) := {y | y.val ∈ A}
      have hS : S.Nonempty := by
        obtain ⟨y,hy⟩ := hA.2
        exact ⟨⟨y,hA.1 hy⟩,hy⟩
      obtain ⟨m,hm,hmin⟩ := (IsWellOrder.wf (r := fun y z : a x => ZFSet.pair y.val z.val ∈ a R)).has_min S hS
      refine ⟨m.val,hm,fun z hz => ?_⟩
      have hs := hmin ⟨z,hA.1 hz⟩ hz
      rcases trichotomous_of (fun y z : a x => ZFSet.pair y.val z.val ∈ a R)
        m ⟨z,hA.1 hz⟩ with h | he | h
      · exact Or.inr h
      · exact Or.inl (congrArg Subtype.val he)
      · exact (hs h).elim

theorem wellOrder_native_transfer (D : ZFSet.{u}) (hD : D.IsTransitive)
    (R x : D) (hr : IsSetWellOrder x.val R.val) :
    setSatisfies D (wellOrderFormula (0 : Fin 2) 1) ![R,x] := by
  let := actualMembershipStructure D
  let := universeMembershipStructure.{u}
  let q : DeltaZero 2 := DeltaZero.conj (relationDomainTest 0 1)
    (.conj (irreflexiveTest 0 1) (.conj (transitiveRelationTest 0 1) (comparableTest 0 1)))
  let s : DeltaZero 3 := (subsetTest (Fin.last 2) (1 : Fin 2).castSucc).conj
    (nonemptyTest (Fin.last 2))
  let t : DeltaZero 3 := minimumTest (0 : Fin 2).castSucc (Fin.last 2)
  let a : Fin 2 → D := ![R,x]
  have hu := (wellOrderFormula_correct (0 : Fin 2) 1 (fun i => (a i).val)).mpr hr
  have hsem : universeSatisfies (q.toShared ⊓ (s.toShared.imp t.toShared).all)
      (fun i => (a i).val) := hu
  have hq := (BoundedFormula.realize_inf.mp hsem).1
  have ht := (BoundedFormula.realize_inf.mp hsem).2
  change setSatisfies D (q.toShared ⊓ (s.toShared.imp t.toShared).all) a
  refine BoundedFormula.realize_inf.mpr ⟨(bounded_to_universe D hD q a).mpr hq,?_⟩
  apply BoundedFormula.realize_all.mpr
  intro A
  apply BoundedFormula.realize_imp.mpr
  intro hA
  have hs := (bounded_to_universe D hD s (Fin.snoc a A)).mp hA
  have hv : (fun i : Fin 3 => ((Fin.snoc (α := fun _ => D) a A) i).val) =
      Fin.snoc (fun i => (a i).val) A.val := (Fin.comp_snoc Subtype.val a A)
  rw [hv] at hs
  have ht' := (BoundedFormula.realize_imp.mp (BoundedFormula.realize_all.mp ht A.val)) hs
  apply (bounded_to_universe D hD t (Fin.snoc a A)).mpr
  rw [hv]
  exact ht'


/-- The exact graph of a supplied relation on the actual members of x. -/
def wellOrderGraph (x : ZFSet.{u}) (r : x → x → Prop) : ZFSet.{u} :=
  ZFSet.pairSep (fun a b => ∃ (ha : a ∈ x) (hb : b ∈ x), r ⟨a,ha⟩ ⟨b,hb⟩) x x

theorem wellOrderGraph_spec (x : ZFSet.{u}) (r : x → x → Prop) (hr : IsWellOrder x r) :
    wellOrderGraph x r ⊆ ZFSet.prod x x ∧
    (∀ a b : x, ZFSet.pair a.val b.val ∈ wellOrderGraph x r ↔ r a b) ∧
    IsSetWellOrder x (wellOrderGraph x r) := by
  classical
  have hd : wellOrderGraph x r ⊆ ZFSet.prod x x := by
    intro z hz
    obtain ⟨a,ha,b,hb,rfl,_⟩ := ZFSet.mem_pairSep.mp hz
    exact ZFSet.pair_mem_prod.mpr ⟨ha,hb⟩
  have he (a b : x) : ZFSet.pair a.val b.val ∈ wellOrderGraph x r ↔ r a b := by
    simp only [wellOrderGraph,ZFSet.mem_pairSep,ZFSet.pair_inj]
    constructor
    · rintro ⟨a',ha,b',hb,⟨hea,heb⟩,ha',hb',hr'⟩
      subst a'; subst b'; exact hr'
    · intro h; exact ⟨a.val,a.property,b.val,b.property,⟨rfl,rfl⟩,a.property,b.property,h⟩
  refine ⟨hd,he,hd,?_⟩
  have hr' : (fun a b : x => ZFSet.pair a.val b.val ∈ wellOrderGraph x r) = r := by
    funext a b
    exact propext (he a b)
  rw [hr']
  exact hr

theorem wellOrderGraph_in_stage (l : Ordinal.{u}) (hl : Order.IsSuccLimit l)
    (x : ZFSet.vonNeumann l) (r : x.val → x.val → Prop) (hr : IsWellOrder x.val r) :
    ∃ hR : wellOrderGraph x.val r ∈ ZFSet.vonNeumann l,
      setSatisfies (ZFSet.vonNeumann l) (wellOrderFormula (0 : Fin 2) 1)
        ![⟨wellOrderGraph x.val r,hR⟩,x] := by
  have hs := wellOrderGraph_spec x.val r hr
  have hR := (relation_rank_overhead l hl x.val (wellOrderGraph x.val r) x.property hs.1).2
  exact ⟨hR,wellOrder_native_transfer _ (ZFSet.isTransitive_vonNeumann l) ⟨_,hR⟩ x hs.2.2⟩

theorem inaccessible_internal_wellOrder (k : Cardinal.{u}) (hk : k.IsInaccessible)
    (x : ZFSet.vonNeumann k.ord) :
    ∃ r : x.val → x.val → Prop, IsWellOrder x.val r ∧
      ∃ hR : wellOrderGraph x.val r ∈ ZFSet.vonNeumann k.ord,
        setSatisfies (ZFSet.vonNeumann k.ord) (wellOrderFormula (0 : Fin 2) 1)
          ![⟨wellOrderGraph x.val r,hR⟩,x] := by
  classical
  let r : x.val → x.val → Prop := WellOrderingRel
  have hr : IsWellOrder x.val r := inferInstance
  obtain ⟨hR,hR'⟩ := wellOrderGraph_in_stage k.ord (inaccessible_ordinal k hk).1 x r hr
  exact ⟨r,hr,hR,hR'⟩

end
end Lemmatheca.SetTheory.InaccessibleCardinals
