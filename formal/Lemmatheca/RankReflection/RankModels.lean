import Lemmatheca.RankReflection.Reflection
import Lemmatheca.CumulativeHierarchy.CumulativeHierarchy
import Lemmatheca.MembershipModels.Compactness
import Lemmatheca.ElementarySubmodels.ElementarySubmodels

namespace Lemmatheca.SetTheory.RankReflection
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
universe u
noncomputable section

def rankHierarchy : Hierarchy.{u} where
  level := ZFSet.vonNeumann
  transitive := ZFSet.isTransitive_vonNeumann
  monotone := fun h => ZFSet.vonNeumann_strictMono.monotone h
  continuous := by
    intro l hl x
    rw [ZFSet.vonNeumann_of_isSuccPrelimit hl.isSuccPrelimit]
    simp only [ZFSet.mem_iUnion]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a.val,a.property,ha⟩
    · rintro ⟨a,ha,hx⟩
      exact ⟨⟨a,ha⟩,hx⟩

theorem rankHierarchy_nonempty : NonemptyUnion rankHierarchy.{u} := by
  refine ⟨1,∅,?_⟩
  change (∅ : ZFSet.{u}) ∈ ZFSet.vonNeumann 1
  simp [ZFSet.mem_vonNeumann]

theorem rank_union_truth {n} (p : membershipLanguage.BoundedFormula Empty n)
    (a : Fin n → UnionDomain rankHierarchy.{u}) :
    unionSatisfies rankHierarchy p a ↔ universeSatisfies p (fun i => (a i).val) := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure
    (UnionDomain rankHierarchy.{u}) (fun x y => x.val ∈ y.val)
  let := universeMembershipStructure.{u}
  let e : UnionDomain rankHierarchy.{u} ≃[membershipLanguage] ZFSet.{u} :=
    { toEquiv :=
        { toFun := Subtype.val
          invFun := fun x => ⟨x,ZFSet.exists_mem_vonNeumann x⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun _ => rfl }
      map_fun' := by intro n f; exact Empty.elim f
      map_rel' := by intro n r xs; cases r; rfl }
  have he := (StrongHomClass.realize_boundedFormula e p (v := Empty.elim) (xs := a)).symm
  have hEmpty : e ∘ (Empty.elim : Empty → UnionDomain rankHierarchy.{u}) =
      (Empty.elim : Empty → ZFSet.{u}) := Subsingleton.elim _ _
  rw [hEmpty] at he
  exact he

theorem rank_reflectingHeight_spec (F : Finset NativePackedFormula) (theta : Ordinal.{u}) :
    let l := reflectingHeight rankHierarchy (expandFamily F) theta
    theta < l ∧ Order.IsSuccLimit l ∧ (ZFSet.vonNeumann l).Nonempty ∧
      ∀ p ∈ F, ∀ a : Fin p.1 → ZFSet.vonNeumann l,
        setSatisfies (ZFSet.vonNeumann l) p.2 a ↔
          universeSatisfies p.2 (fun i => (a i).val) := by
  obtain ⟨ht,hl,hn,hr⟩ := native_reflectingHeight_spec rankHierarchy
    rankHierarchy_nonempty F theta
  refine ⟨ht,hl,hn,?_⟩
  intro p hp a
  exact (hr p hp a).trans (rank_union_truth p.2 (fun i => intoUnion rankHierarchy _ (a i)))

private theorem scope_equal {M : Type*} (E : M → M → Prop) {n}
    (i j : Fin n) (a : Fin n → M) :
    nativeSatisfies E (Formula.equal i j).toShared a ↔ a i = a j := Iff.rfl
private theorem scope_mem {M : Type*} (E : M → M → Prop) {n}
    (i j : Fin n) (a : Fin n → M) :
    nativeSatisfies E (Formula.mem i j).toShared a ↔ E (a i) (a j) := Iff.rfl
private theorem scope_neg {M : Type*} (E : M → M → Prop) {n}
    (p : Formula n) (a : Fin n → M) :
    nativeSatisfies E (Formula.neg p).toShared a ↔ ¬nativeSatisfies E p.toShared a := Iff.rfl
private theorem scope_conj {M : Type*} (E : M → M → Prop) {n}
    (p q : Formula n) (a : Fin n → M) :
    nativeSatisfies E (Formula.conj p q).toShared a ↔
      nativeSatisfies E p.toShared a ∧ nativeSatisfies E q.toShared a := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  exact BoundedFormula.realize_inf
private theorem scope_ex {M : Type*} (E : M → M → Prop) {n}
    (p : Formula (n+1)) (a : Fin n → M) :
    nativeSatisfies E (Formula.ex p).toShared a ↔
      ∃ x, nativeSatisfies E p.toShared (Fin.snoc a x) := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  exact BoundedFormula.realize_ex
private theorem scope_all {M : Type*} (E : M → M → Prop) {n}
    (p : Formula (n+1)) (a : Fin n → M) :
    nativeSatisfies E (Formula.all p).toShared a ↔
      ∀ x, nativeSatisfies E p.toShared (Fin.snoc a x) := by
  classical
  simp only [Formula.all, scope_neg, scope_ex, not_exists, not_not]
private theorem scope_imp {M : Type*} (E : M → M → Prop) {n}
    (p q : Formula n) (a : Fin n → M) :
    nativeSatisfies E (Formula.imp p q).toShared a ↔
      (nativeSatisfies E p.toShared a → nativeSatisfies E q.toShared a) := by
  classical
  simp only [Formula.imp, scope_neg, scope_conj, not_and, not_not]
private theorem scope_disj {M : Type*} (E : M → M → Prop) {n}
    (p q : Formula n) (a : Fin n → M) :
    nativeSatisfies E (Formula.disj p q).toShared a ↔
      nativeSatisfies E p.toShared a ∨ nativeSatisfies E q.toShared a := by
  classical
  simp only [Formula.disj, scope_neg, scope_conj, not_and_or, not_not]
private theorem scope_iff {M : Type*} (E : M → M → Prop) {n}
    (p q : Formula n) (a : Fin n → M) :
    nativeSatisfies E (Formula.iff p q).toShared a ↔
      (nativeSatisfies E p.toShared a ↔ nativeSatisfies E q.toShared a) := by
  classical
  simp only [Formula.iff, scope_neg, scope_conj, not_and, not_not, iff_def]

def emptyAxiom : membershipLanguage.Sentence :=
  (Formula.ex (Formula.all (Formula.neg (Formula.mem 1 0)))).toShared
def pairingAxiom : membershipLanguage.Sentence :=
  (Formula.all (Formula.all (Formula.ex (Formula.all
    (Formula.iff (Formula.mem 3 2)
      (Formula.disj (Formula.equal 3 0) (Formula.equal 3 1))))))).toShared
def unionAxiom : membershipLanguage.Sentence :=
  (Formula.all (Formula.ex (Formula.all
    (Formula.iff (Formula.mem 2 1)
      (Formula.ex (Formula.conj (Formula.mem 3 0) (Formula.mem 2 3))))))).toShared

def emptyScoped {n} (x : Fin n) : Formula n :=
  .all (.neg (.mem (Fin.last n) x.castSucc))
def successorScoped {n} (s x : Fin n) : Formula n :=
  .all (.iff (.mem (Fin.last n) s.castSucc)
    (.disj (.mem (Fin.last n) x.castSucc) (.equal (Fin.last n) x.castSucc)))
def inductiveScoped {n} (i : Fin n) : Formula n :=
  .conj (.ex (.conj (emptyScoped (Fin.last n)) (.mem (Fin.last n) i.castSucc)))
    (.all (.imp (.mem (Fin.last n) i.castSucc)
      (.ex (.conj (.mem (Fin.last (n+1)) i.castSucc.castSucc)
        (successorScoped (Fin.last (n+1)) (Fin.last n).castSucc)))))
def infinityAxiom : membershipLanguage.Sentence :=
  (Formula.ex (inductiveScoped 0)).toShared

theorem emptyAxiom_realize (D : ZFSet.{u}) :
    setSatisfies D emptyAxiom Fin.elim0 ↔
      ∃ a : D, ∀ x : D, x.val ∉ a.val := by
  classical
  simp only [emptyAxiom, scope_ex, scope_all, scope_neg, scope_mem]
  rfl
theorem pairingAxiom_realize (D : ZFSet.{u}) :
    setSatisfies D pairingAxiom Fin.elim0 ↔
      ∀ x y : D, ∃ p : D, ∀ z : D, z.val ∈ p.val ↔ z = x ∨ z = y := by
  classical
  simp only [pairingAxiom, scope_all, scope_ex, scope_iff, scope_disj,
    scope_equal, scope_mem]
  rfl
theorem unionAxiom_realize (D : ZFSet.{u}) :
    setSatisfies D unionAxiom Fin.elim0 ↔
      ∀ a : D, ∃ b : D, ∀ z : D, z.val ∈ b.val ↔
        ∃ y : D, y.val ∈ a.val ∧ z.val ∈ y.val := by
  classical
  simp only [unionAxiom, scope_all, scope_ex, scope_iff, scope_conj, scope_mem]
  rfl
private theorem emptyScoped_universe {n} (i : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (emptyScoped i).toShared a ↔ a i = ∅ := by
  classical
  simp only [emptyScoped, scope_all, scope_neg, scope_mem, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h
    ext z
    simp only [ZFSet.notMem_empty, iff_false]
    exact h z
  · rintro h z
    rw [h]
    exact ZFSet.notMem_empty z
private theorem successorScoped_universe {n} (s x : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (successorScoped s x).toShared a ↔ a s = insert (a x) (a x) := by
  simp only [successorScoped, scope_all, scope_iff, scope_disj, scope_equal, scope_mem,
    Fin.snoc_last, Fin.snoc_castSucc]
  rw [ZFSet.ext_iff]
  simp only [ZFSet.mem_insert_iff, or_comm]

theorem inductiveScoped_correct {n} (i : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (inductiveScoped i).toShared a ↔
      (∅ : ZFSet.{u}) ∈ a i ∧ ∀ x ∈ a i, insert x x ∈ a i := by
  simp only [inductiveScoped, scope_conj, scope_ex, scope_all, scope_imp,
    emptyScoped_universe, successorScoped_universe, scope_mem,
    Fin.snoc_last, Fin.snoc_castSucc, exists_eq_left, exists_eq_right]

theorem limit_basic_axioms (l : Ordinal.{u}) (hl : Order.IsSuccLimit l) :
    (ZFSet.vonNeumann l).Nonempty ∧
    setSatisfies (ZFSet.vonNeumann l) extensionalitySentence Fin.elim0 ∧
    setSatisfies (ZFSet.vonNeumann l) foundationSentence Fin.elim0 ∧
    setSatisfies (ZFSet.vonNeumann l) emptyAxiom Fin.elim0 ∧
    setSatisfies (ZFSet.vonNeumann l) pairingAxiom Fin.elim0 ∧
    setSatisfies (ZFSet.vonNeumann l) unionAxiom Fin.elim0 := by
  let D := ZFSet.vonNeumann l
  have hD := ZFSet.isTransitive_vonNeumann l
  have h0 : (∅ : ZFSet.{u}) ∈ D := by
    apply ZFSet.mem_vonNeumann.mpr
    simpa only [ZFSet.rank_empty] using hl.pos
  let := actualMembershipStructure D
  have hh := Lemmatheca.SetTheory.MostowskiCollapse.transitive_membership_hypotheses D hD
  refine ⟨⟨∅,h0⟩,?_,?_,?_,?_,?_⟩
  · change D ⊨ extensionalitySentence
    exact (extensionality_realize (fun x y : D => x.val ∈ y.val)).mpr hh.2
  · change D ⊨ foundationSentence
    exact (foundation_realize (fun x y : D => x.val ∈ y.val)).mpr
      (wellFounded_internalFoundation hh.1)
  · apply (emptyAxiom_realize D).mpr
    exact ⟨⟨∅,h0⟩,fun x => ZFSet.notMem_empty x.val⟩
  · apply (pairingAxiom_realize D).mpr
    intro x y
    have hp := ((Lemmatheca.SetTheory.CumulativeHierarchy.stage_closure l x.val y.val
      x.property y.property).2.2.2 hl).1
    refine ⟨⟨{x.val,y.val},hp⟩,?_⟩
    intro z
    simp only [ZFSet.mem_pair, Subtype.ext_iff]
  · apply (unionAxiom_realize D).mpr
    intro a
    have hu := (Lemmatheca.SetTheory.CumulativeHierarchy.stage_closure l a.val a.val
      a.property a.property).1
    refine ⟨⟨ZFSet.sUnion a.val,hu⟩,?_⟩
    intro z
    rw [ZFSet.mem_sUnion]
    constructor
    · rintro ⟨y,hy,hz⟩
      exact ⟨⟨y,hD.mem_trans hy a.property⟩,hy,hz⟩
    · rintro ⟨y,hy,hz⟩
      exact ⟨y.val,hy,hz⟩

def separationSubset (D : ZFSet.{u}) {n}
    (p : membershipLanguage.BoundedFormula Empty (n+1)) (a : Fin n → D)
    (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ hz : z ∈ D, setSatisfies D p (Fin.snoc a ⟨z,hz⟩)) x

theorem limit_separation (l : Ordinal.{u}) (hl : Order.IsSuccLimit l) {n}
    (p : membershipLanguage.BoundedFormula Empty (n+1))
    (a : Fin n → ZFSet.vonNeumann l) (x : ZFSet.vonNeumann l) :
    separationSubset (ZFSet.vonNeumann l) p a x.val ∈ ZFSet.vonNeumann l ∧
    ∀ z : ZFSet.vonNeumann l,
      z.val ∈ separationSubset (ZFSet.vonNeumann l) p a x.val ↔
        z.val ∈ x.val ∧ setSatisfies (ZFSet.vonNeumann l) p (Fin.snoc a z) := by
  have _ := hl.ne_bot
  have hs : separationSubset (ZFSet.vonNeumann l) p a x.val ⊆ x.val :=
    fun _ hz => (ZFSet.mem_sep.mp hz).1
  refine ⟨ZFSet.mem_vonNeumann_of_subset hs x.property,?_⟩
  intro z
  simp only [separationSubset, ZFSet.mem_sep]
  constructor
  · rintro ⟨hz,_,hp⟩
    exact ⟨hz,hp⟩
  · rintro ⟨hz,hp⟩
    exact ⟨hz,z.property,hp⟩

theorem limit_full_power_set (l : Ordinal.{u}) (hl : Order.IsSuccLimit l)
    (a : ZFSet.vonNeumann l) :
    (∀ z : ZFSet.{u}, z ⊆ a.val → z ∈ ZFSet.vonNeumann l) ∧
    ∃ hp : ZFSet.powerset a.val ∈ ZFSet.vonNeumann l,
      setSatisfies (ZFSet.vonNeumann l) (powerSetFormula (0 : Fin 2) 1)
        ![⟨ZFSet.powerset a.val,hp⟩,a] := by
  have hc := Lemmatheca.SetTheory.CumulativeHierarchy.stage_closure l a.val a.val
    a.property a.property
  have hp := (hc.2.2.2 hl).2
  refine ⟨fun z hz => ZFSet.mem_vonNeumann_of_subset hz a.property,hp,?_⟩
  let := actualMembershipStructure (ZFSet.vonNeumann l)
  change ((memScoped (Fin.last 2) (0 : Fin 2).castSucc).iff
    (subsetTest (Fin.last 2) (1 : Fin 2).castSucc).toShared).all.Realize Empty.elim _
  rw [BoundedFormula.realize_all]
  intro z
  rw [BoundedFormula.realize_iff]
  change z.val ∈ ZFSet.powerset a.val ↔
    setSatisfies (ZFSet.vonNeumann l)
      (subsetTest (Fin.last 2) (1 : Fin 2).castSucc).toShared
        (Fin.snoc ![⟨ZFSet.powerset a.val,hp⟩,a] z)
  rw [bounded_to_universe _ (ZFSet.isTransitive_vonNeumann l), subsetTest_correct]
  exact ZFSet.mem_powerset

private theorem emptyScoped_set (D : ZFSet.{u}) (hD : D.IsTransitive) {n}
    (i : Fin n) (a : Fin n → D) :
    setSatisfies D (emptyScoped i).toShared a ↔ (a i).val = ∅ := by
  classical
  simp only [emptyScoped, scope_all, scope_neg, scope_mem, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h
    ext z
    simp only [ZFSet.notMem_empty, iff_false]
    intro hz
    exact h ⟨z,hD.mem_trans hz (a i).property⟩ hz
  · intro h z
    rw [h]
    exact ZFSet.notMem_empty z.val
private theorem successorScoped_set (D : ZFSet.{u}) (hD : D.IsTransitive) {n}
    (s x : Fin n) (a : Fin n → D) :
    setSatisfies D (successorScoped s x).toShared a ↔
      (a s).val = insert (a x).val (a x).val := by
  simp only [successorScoped, scope_all, scope_iff, scope_disj, scope_equal, scope_mem,
    Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h
    ext z
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hz
      let b : D := ⟨z,hD.mem_trans hz (a s).property⟩
      rcases (h b).mp hz with hx | hx
      · exact Or.inr hx
      · exact Or.inl (congrArg Subtype.val hx)
    · rintro (rfl | hz)
      · exact (h (a x)).mpr (Or.inr rfl)
      · exact (h ⟨z,hD.mem_trans hz (a x).property⟩).mpr (Or.inl hz)
  · intro h z
    rw [h,ZFSet.mem_insert_iff]
    simp only [Subtype.ext_iff, or_comm]
private theorem inductiveScoped_set (D : ZFSet.{u}) (hD : D.IsTransitive) {n}
    (i : Fin n) (a : Fin n → D) :
    setSatisfies D (inductiveScoped i).toShared a ↔
      (∅ : ZFSet.{u}) ∈ (a i).val ∧
        ∀ x ∈ (a i).val, insert x x ∈ (a i).val := by
  simp only [inductiveScoped, scope_conj, scope_ex, scope_all, scope_imp,
    emptyScoped_set D hD, successorScoped_set D hD, scope_mem,
    Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨⟨z,hz,hm⟩,hs⟩
    refine ⟨hz ▸ hm,?_⟩
    intro x hx
    obtain ⟨s,hm,he⟩ := hs ⟨x,hD.mem_trans hx (a i).property⟩ hx
    exact he ▸ hm
  · rintro ⟨hz,hs⟩
    refine ⟨⟨⟨∅,hD.mem_trans hz (a i).property⟩,rfl,hz⟩,?_⟩
    intro x hx
    have hm := hs x.val hx
    exact ⟨⟨insert x.val x.val,hD.mem_trans hm (a i).property⟩,hm,rfl⟩

theorem infinity_above_omega (l : Ordinal.{u}) (hl : Order.IsSuccLimit l)
    (hw : Ordinal.omega0.{u} < l) :
    Ordinal.omega0.{u}.toZFSet ∈ ZFSet.vonNeumann l ∧
    setSatisfies (ZFSet.vonNeumann l) infinityAxiom Fin.elim0 := by
  have _ := hl.ne_bot
  have hwMem := (Lemmatheca.SetTheory.CumulativeHierarchy.ordinal_part l
    Ordinal.omega0.{u}).mpr hw
  refine ⟨hwMem,?_⟩
  apply (scope_ex _ (inductiveScoped 0) Fin.elim0).mpr
  refine ⟨⟨Ordinal.omega0.toZFSet,hwMem⟩,?_⟩
  apply (inductiveScoped_set _ (ZFSet.isTransitive_vonNeumann l) _ _).mpr
  change (∅ : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet ∧
    ∀ x ∈ Ordinal.omega0.toZFSet, insert x x ∈ Ordinal.omega0.toZFSet
  constructor
  · rw [←Ordinal.toZFSet_zero,Ordinal.toZFSet_mem_toZFSet_iff]
    exact Ordinal.omega0_pos
  · intro x hx
    obtain ⟨b,hb,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    rw [←Ordinal.toZFSet_add_one,Ordinal.toZFSet_mem_toZFSet_iff]
    exact Ordinal.isSuccLimit_omega0.succ_lt hb

theorem no_infinity_at_omega :
    ¬setSatisfies (ZFSet.vonNeumann Ordinal.omega0.{u}) infinityAxiom Fin.elim0 := by
  intro h
  obtain ⟨a,ha⟩ := (scope_ex _ (inductiveScoped 0) Fin.elim0).mp h
  obtain ⟨hz,hs⟩ := (inductiveScoped_set _
    (ZFSet.isTransitive_vonNeumann Ordinal.omega0) _ _).mp ha
  change (∅ : ZFSet.{u}) ∈ a.val at hz
  change ∀ x ∈ a.val, insert x x ∈ a.val at hs
  have hn (n : ℕ) : (n : Ordinal.{u}).toZFSet ∈ a.val := by
    induction n with
    | zero => simpa only [Nat.cast_zero,Ordinal.toZFSet_zero] using hz
    | succ n ih =>
      simpa only [Nat.cast_add_one,Ordinal.toZFSet_add_one] using hs _ ih
  obtain ⟨n,hr⟩ := Ordinal.lt_omega0.mp (ZFSet.mem_vonNeumann.mp a.property)
  have hc := ZFSet.rank_lt_of_mem (hn n)
  rw [Ordinal.rank_toZFSet,hr] at hc
  exact lt_irrefl _ hc

theorem replacement_range_rank_criterion (l : Ordinal.{u}) (hl : Order.IsSuccLimit l)
    (a : ZFSet.{u}) (f : a → ZFSet.{u}) :
    ZFSet.range f ∈ ZFSet.vonNeumann l ↔
      ∃ b < l, ∀ i, (f i).rank < b := by
  have _ := hl.ne_bot
  rw [ZFSet.mem_vonNeumann]
  constructor
  · intro h
    refine ⟨(ZFSet.range f).rank,h,?_⟩
    intro i
    exact ZFSet.rank_lt_of_mem (ZFSet.mem_range_self i)
  · rintro ⟨b,hb,hf⟩
    apply lt_of_le_of_lt _ hb
    apply ZFSet.rank_le_iff.mpr
    intro y hy
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hy
    exact hf i

private theorem countable_membership_submodel (D : ZFSet.{u}) (hD : D.Nonempty) :
    letI := actualMembershipStructure D
    ∃ S : membershipLanguage.ElementarySubstructure D, Countable S := by
  classical
  let := actualMembershipStructure D
  let : Nonempty D := ⟨⟨hD.choose,hD.choose_spec⟩⟩
  let : Countable membershipLanguage.Symbols := countable_membership_symbols
  by_cases h : Cardinal.mk D ≤ Cardinal.aleph0
  · let : Countable D := Cardinal.mk_le_aleph0_iff.mp h
    exact ⟨⊤,(Subtype.val_injective : Function.Injective
      (Subtype.val : (⊤ : membershipLanguage.ElementarySubstructure D) → D)).countable⟩
  · have hL : membershipLanguage.card ≤ Cardinal.aleph0 :=
      Cardinal.mk_le_aleph0_iff.mpr inferInstance
    obtain ⟨S,_,hS⟩ := membershipLanguage.exists_elementarySubstructure_card_eq
      (∅ : Set D) Cardinal.aleph0.{u+1} le_rfl (by simp)
      (by simpa using Cardinal.lift_le.{u+1,0}.mpr hL)
      (by simpa using le_of_not_ge h)
    refine ⟨S,Cardinal.mk_le_aleph0_iff.mp ?_⟩
    simpa only [Cardinal.lift_id,Cardinal.lift_aleph0] using hS.le

/-- A finite native sentence fragment true in this ZFSet universe has the actual
countable transitive membership model, independently of any coding of ZFC. -/
theorem finite_native_fragment (G : Finset membershipLanguage.Sentence)
    (hG : ∀ p ∈ G, universeSatisfies.{u} p Fin.elim0) :
    (∃ l : Ordinal.{u}, Order.IsSuccLimit l ∧
      ∀ p ∈ G, setSatisfies (ZFSet.vonNeumann l) p Fin.elim0) ∧
    ∃ T : ZFSet.{u}, Countable T ∧ TransitiveSetModel T (G : Set membershipLanguage.Sentence) :=
  by
  classical
  have hExt : universeSatisfies.{u} extensionalitySentence Fin.elim0 := by
    let := universeMembershipStructure.{u}
    change ZFSet.{u} ⊨ extensionalitySentence
    apply (extensionality_realize (fun x y : ZFSet.{u} => x ∈ y)).mpr
    intro a b hab
    exact ZFSet.ext hab
  let G' := insert extensionalitySentence G
  let F : Finset NativePackedFormula := G'.image (fun p => ⟨0,p⟩)
  let l := reflectingHeight rankHierarchy (expandFamily F) 0
  obtain ⟨_,hl,hne,hr⟩ := rank_reflectingHeight_spec F 0
  have hall (p : membershipLanguage.Sentence) (hp : p ∈ G') :
      setSatisfies (ZFSet.vonNeumann l) p Fin.elim0 := by
    have hf : (⟨0,p⟩ : NativePackedFormula) ∈ F := Finset.mem_image.mpr ⟨p,hp,rfl⟩
    apply (hr ⟨0,p⟩ hf Fin.elim0).mpr
    have he : (fun i => ((Fin.elim0 : Fin 0 → ZFSet.vonNeumann l) i).val) =
        (Fin.elim0 : Fin 0 → ZFSet.{u}) := Subsingleton.elim _ _
    rw [he]
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hExt
    · exact hG p hp
  refine ⟨⟨l,hl,fun p hp => hall p (Finset.mem_insert_of_mem hp)⟩,?_⟩
  let D := ZFSet.vonNeumann l
  let := actualMembershipStructure D
  let : Nonempty D := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  obtain ⟨S,hS⟩ := countable_membership_submodel D hne
  let : Countable S := hS
  let : Small.{u} S := Countable.toSmall S
  have hSTheory : S ⊨ (G' : Set membershipLanguage.Sentence) := by
    apply (S.theory_model_iff _).mpr
    constructor
    intro p hp
    simpa only [Sentence.Realize, FirstOrder.Language.Formula.Realize, nativeSatisfies,
      Unique.eq_default (Fin.elim0 : Fin 0 → D),
      Unique.eq_default (Empty.elim : Empty → D)] using hall p hp
  have hextS : S ⊨ extensionalitySentence :=
    hSTheory.realize_of_mem extensionalitySentence (Finset.mem_insert_self _ _)
  let E : S → S → Prop := fun x y => x.val.val ∈ y.val.val
  have hw : WellFounded E := InvImage.wf (fun x : S => x.val.val) ZFSet.mem_wf
  have hStr : S.inducedStructure =
      Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure S E := by
    apply Structure.ext
    · funext n f
      exact Empty.elim f
    · funext n r xs
      cases r
      rfl
  have hextE : letI := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure S E
      S ⊨ extensionalitySentence := by
    rw [←hStr]
    exact hextS
  have hTheoryE : letI := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure S E
      S ⊨ (G' : Set membershipLanguage.Sentence) := by
    rw [←hStr]
    exact hSTheory
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure S E
  have he : Lemmatheca.SetTheory.MostowskiCollapse.Extensional E :=
    (extensionality_realize E).mp hextE
  let T := collapsedSet.{u} hw
  let := actualMembershipStructure T
  have hc : Countable T := ((collapseIso.{u} hw he).symm.injective).countable
  have ht : T.IsTransitive :=
    (Lemmatheca.SetTheory.MostowskiCollapse.collapse_image hw).1
  have hnT : T ≠ ∅ := by
    intro h
    have hm : Lemmatheca.SetTheory.MostowskiCollapse.collapse.{u} hw (Classical.choice (inferInstance : Nonempty S)) ∈ T :=
      ZFSet.mem_range_self _
    rw [h] at hm
    exact ZFSet.notMem_empty _ hm
  refine ⟨T,hc,hnT,ht,?_⟩
  apply (collapse_theory.{u} hw he _).mpr
  exact (Theory.model_iff _).mpr (fun p hp =>
    hTheoryE.realize_of_mem p (Finset.mem_insert_of_mem hp))

end
end Lemmatheca.SetTheory.RankReflection
