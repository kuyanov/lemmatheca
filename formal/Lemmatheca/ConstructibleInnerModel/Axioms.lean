import Lemmatheca.ConstructibleHierarchy.Absoluteness
import Lemmatheca.RankReflection.RankModels
import Lemmatheca.NaturalNumbersAsSets.NaturalNumbersAsSets

namespace Lemmatheca.SetTheory.ConstructibleInnerModel
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
open Lemmatheca.SetTheory.ConstructibleHierarchy
open Lemmatheca.SetTheory.RankReflection
open scoped Ordinal ZFSet
universe u
noncomputable section

abbrev LDomain := UnionDomain constructibleHierarchy.{u}
abbrev lTruth {n} (p : membershipLanguage.BoundedFormula Empty n) (a : Fin n → LDomain.{u}) :=
  unionSatisfies constructibleHierarchy p a
def lElement (x : ZFSet.{u}) (hx : IsConstructible x) : LDomain.{u} := ⟨x,hx⟩
def lMember (x : LDomain.{u}) (y : x.val) : LDomain.{u} :=
  ⟨y.val,constructible_transitive y.property x.property⟩

def leastStage (x : ZFSet.{u}) (_hx : IsConstructible x) : Ordinal.{u} :=
  sInf {a | x ∈ level a}
theorem leastStage_spec (x : ZFSet.{u}) (hx : IsConstructible x) :
    IsLeast {a | x ∈ level a} (leastStage x hx) := by
  exact ⟨csInf_mem hx,fun a ha => csInf_le ⟨0,fun _ _ => bot_le⟩ ha⟩
def stageBound (A : ZFSet.{u}) (hA : ∀ a ∈ A, IsConstructible a) : Ordinal.{u} :=
  (⨆ a : A, leastStage a.val (hA a.val a.property)) + 1
theorem stageBound_spec (A : ZFSet.{u}) (hA : ∀ a ∈ A, IsConstructible a) :
    ∀ a : A, leastStage a.val (hA a.val a.property) < stageBound A hA ∧
      a.val ∈ level (stageBound A hA) := by
  intro a
  have h : leastStage a.val (hA a.val a.property) < stageBound A hA :=
    (Ordinal.le_iSup (fun a : A => leastStage a.val (hA a.val a.property)) a).trans_lt (lt_add_one _)
  exact ⟨h,level_monotone h.le (leastStage_spec a.val _).1⟩
theorem stageBound_empty (h : ∀ a ∈ (∅ : ZFSet.{u}), IsConstructible a) :
    stageBound ∅ h = 1 := by
  have he : (⨆ a : (∅ : ZFSet.{u}), leastStage a.val (h a.val a.property)) = 0 := by
    apply le_antisymm
    · apply Ordinal.iSup_le
      intro a
      exact (ZFSet.notMem_empty a.val a.property).elim
    · exact bot_le
  simp only [stageBound,he,zero_add]
theorem finite_tuple_stage {n} (a : Fin n → LDomain.{u}) :
    ∃ b : Ordinal.{u}, ∀ i, (a i).val ∈ level b := by
  let b := (⨆ i, leastStage (a i).val (a i).property)+1
  refine ⟨b,fun i => ?_⟩
  have hi : leastStage (a i).val (a i).property < b :=
    (Ordinal.le_iSup (fun i => leastStage (a i).val (a i).property) i).trans_lt (lt_add_one _)
  exact level_monotone hi.le (leastStage_spec _ _).1

theorem reflection_in_L (F : Finset NativePackedFormula) (theta : Ordinal.{u}) :
    let b := reflectingHeight constructibleHierarchy (expandFamily F) theta
    theta < b ∧ Order.IsSuccLimit b ∧ (level b).Nonempty ∧
      ∀ p ∈ F, ∀ a : Fin p.1 → level b,
        setSatisfies (level b) p.2 a ↔ lTruth p.2 (fun i => intoUnion constructibleHierarchy b (a i)) := by
  exact native_reflectingHeight_spec constructibleHierarchy constructibleHierarchy_nonempty F theta

def pairCode (M : ZFSet.{u}) (x y : M) : DefinitionCode M :=
  ⟨2,(.equal (.var (.inr 2)) (.var (.inr 0))) ⊔
    (.equal (.var (.inr 2)) (.var (.inr 1))),![x,y]⟩
def unionCode (M : ZFSet.{u}) (x : M) : DefinitionCode M :=
  ⟨1,(DeltaZero.bex (0 : Fin 2) (.mem (1 : Fin 3) 2)).toShared,![x]⟩
theorem pairCode_spec (M : ZFSet.{u}) (x y : M) :
    definedSubset M (pairCode M x y) = {x.val,y.val} := by
  let := actualMembershipStructure M
  ext z
  rw [definedSubset,ZFSet.mem_sep,ZFSet.mem_pair]
  change (z ∈ M ∧ ∃ hz : z ∈ M,
    setSatisfies M (pairCode M x y).2.1 (Fin.snoc (pairCode M x y).2.2 ⟨z,hz⟩)) ↔ _
  have sem (hz : z ∈ M) :
      setSatisfies M (pairCode M x y).2.1 (Fin.snoc (pairCode M x y).2.2 ⟨z,hz⟩) ↔
        z = x.val ∨ z = y.val := by
    simp only [setSatisfies,nativeSatisfies,pairCode,BoundedFormula.realize_sup]
    change ((⟨z,hz⟩ : M) = x ∨ (⟨z,hz⟩ : M) = y) ↔ _
    simp only [Subtype.ext_iff]
  simp only [sem]
  exact ⟨fun h => h.2.choose_spec,fun h =>
    ⟨h.elim (fun e => e ▸ x.property) (fun e => e ▸ y.property),
      h.elim (fun e => e ▸ x.property) (fun e => e ▸ y.property),h⟩⟩
theorem unionCode_spec (M : ZFSet.{u}) (hM : M.IsTransitive) (x : M) :
    definedSubset M (unionCode M x) = ⋃₀ x.val := by
  have sem (z : M) :
      setSatisfies M (unionCode M x).2.1 (Fin.snoc (unionCode M x).2.2 z) ↔ z.val ∈ ⋃₀x.val := by
    change setSatisfies M (DeltaZero.bex (0 : Fin 2) (.mem (1 : Fin 3) 2)).toShared
      (Fin.snoc ![x] z) ↔ _
    rw [bounded_to_universe M hM]
    apply (DeltaZero.toShared_realize _ _ _).trans
    simp only [DeltaZero.bex_realize,DeltaZero.Holds]
    change (∃ y, y ∈ x.val ∧ z.val ∈ y) ↔ _
    exact ZFSet.mem_sUnion.symm
  ext z
  rw [definedSubset,ZFSet.mem_sep]
  change (z ∈ M ∧ ∃ hz : z ∈ M,
    setSatisfies M (unionCode M x).2.1 (Fin.snoc (unionCode M x).2.2 ⟨z,hz⟩)) ↔ z ∈ ⋃₀x.val
  simp only [sem]
  constructor
  · exact fun h => h.2.choose_spec
  · intro hz
    obtain ⟨y,hy,hzy⟩ := ZFSet.mem_sUnion.mp hz
    have hM' := hM.mem_trans hzy (hM.mem_trans hy x.property)
    exact ⟨hM',hM',hz⟩
theorem basic_L_witnesses : IsConstructible (∅ : ZFSet.{u}) ∧
    (∀ x y : LDomain.{u}, IsConstructible ({x.val,y.val} : ZFSet.{u})) ∧
    (∀ x : LDomain.{u}, IsConstructible (⋃₀ x.val)) ∧
    IsConstructible (Ordinal.omega0 : Ordinal.{u}).toZFSet := by
  refine ⟨⟨1,?_⟩,?_,?_,constructible_ordinals _⟩
  · rw [first_levels.2.1]
    exact ZFSet.mem_singleton.mpr rfl
  · intro x y
    obtain ⟨b,hb⟩ := finite_tuple_stage ![x,y]
    refine ⟨b+1,?_⟩
    rw [level_successor]
    exact (Def_members _ _).mpr ⟨pairCode _ ⟨x.val,hb 0⟩ ⟨y.val,hb 1⟩,pairCode_spec _ _ _⟩
  · intro x
    obtain ⟨b,hb⟩ := x.property
    refine ⟨b+1,?_⟩
    rw [level_successor]
    exact (Def_members _ _).mpr ⟨unionCode _ ⟨x.val,hb⟩,unionCode_spec _ (level_transitive b) _⟩
private theorem scope_equal {M : Type*} (E : M → M → Prop) {n}
    (i j : Fin n) (a : Fin n → M) :
    nativeSatisfies E (RankReflection.Formula.equal i j).toShared a ↔ a i = a j := Iff.rfl
private theorem scope_mem {M : Type*} (E : M → M → Prop) {n}
    (i j : Fin n) (a : Fin n → M) :
    nativeSatisfies E (RankReflection.Formula.mem i j).toShared a ↔ E (a i) (a j) := Iff.rfl
private theorem scope_neg {M : Type*} (E : M → M → Prop) {n}
    (p : Formula n) (a : Fin n → M) :
    nativeSatisfies E (RankReflection.Formula.neg p).toShared a ↔ ¬nativeSatisfies E p.toShared a := Iff.rfl
private theorem scope_conj {M : Type*} (E : M → M → Prop) {n}
    (p q : Formula n) (a : Fin n → M) :
    nativeSatisfies E (RankReflection.Formula.conj p q).toShared a ↔
      nativeSatisfies E p.toShared a ∧ nativeSatisfies E q.toShared a := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  exact BoundedFormula.realize_inf
private theorem scope_ex {M : Type*} (E : M → M → Prop) {n}
    (p : Formula (n+1)) (a : Fin n → M) :
    nativeSatisfies E (RankReflection.Formula.ex p).toShared a ↔
      ∃ x, nativeSatisfies E p.toShared (Fin.snoc a x) := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  exact BoundedFormula.realize_ex
private theorem scope_all {M : Type*} (E : M → M → Prop) {n}
    (p : Formula (n+1)) (a : Fin n → M) :
    nativeSatisfies E (RankReflection.Formula.all p).toShared a ↔
      ∀ x, nativeSatisfies E p.toShared (Fin.snoc a x) := by
  classical
  simp only [RankReflection.Formula.all, scope_neg, scope_ex, not_exists, not_not]
private theorem scope_imp {M : Type*} (E : M → M → Prop) {n}
    (p q : Formula n) (a : Fin n → M) :
    nativeSatisfies E (RankReflection.Formula.imp p q).toShared a ↔
      (nativeSatisfies E p.toShared a → nativeSatisfies E q.toShared a) := by
  classical
  simp only [RankReflection.Formula.imp, scope_neg, scope_conj, not_and, not_not]
private theorem scope_disj {M : Type*} (E : M → M → Prop) {n}
    (p q : Formula n) (a : Fin n → M) :
    nativeSatisfies E (RankReflection.Formula.disj p q).toShared a ↔
      nativeSatisfies E p.toShared a ∨ nativeSatisfies E q.toShared a := by
  classical
  simp only [RankReflection.Formula.disj, scope_neg, scope_conj, not_and_or, not_not]
private theorem scope_iff {M : Type*} (E : M → M → Prop) {n}
    (p q : Formula n) (a : Fin n → M) :
    nativeSatisfies E (RankReflection.Formula.iff p q).toShared a ↔
      (nativeSatisfies E p.toShared a ↔ nativeSatisfies E q.toShared a) := by
  classical
  simp only [RankReflection.Formula.iff, scope_neg, scope_conj, not_and, not_not, iff_def]

theorem basic_L_axioms :
    lTruth extensionalitySentence (Fin.elim0 : Fin 0 → LDomain.{u}) ∧
    lTruth foundationSentence (Fin.elim0 : Fin 0 → LDomain.{u}) ∧
    lTruth emptyAxiom (Fin.elim0 : Fin 0 → LDomain.{u}) ∧
    lTruth pairingAxiom (Fin.elim0 : Fin 0 → LDomain.{u}) ∧
    lTruth unionAxiom (Fin.elim0 : Fin 0 → LDomain.{u}) ∧
    lTruth infinityAxiom (Fin.elim0 : Fin 0 → LDomain.{u}) := by
  classical
  let E : LDomain.{u} → LDomain.{u} → Prop := fun x y => x.val ∈ y.val
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure LDomain.{u} E
  have ht (p : membershipLanguage.Sentence) :
      lTruth p (Fin.elim0 : Fin 0 → LDomain.{u}) ↔ LDomain.{u} ⊨ p := by
    change BoundedFormula.Realize p Empty.elim Fin.elim0 ↔ BoundedFormula.Realize p default default
    rw [show (Empty.elim : Empty → LDomain.{u}) = default from Subsingleton.elim _ _,
      show (Fin.elim0 : Fin 0 → LDomain.{u}) = default from Subsingleton.elim _ _]
  have he : Lemmatheca.SetTheory.MostowskiCollapse.Extensional E := by
    intro a b hab
    apply Subtype.ext
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact (hab ⟨z,constructible_transitive hz a.property⟩).mp hz
    · intro hz
      exact (hab ⟨z,constructible_transitive hz b.property⟩).mpr hz
  refine ⟨(ht _).mpr ((extensionality_realize E).mpr he),
    (ht _).mpr ((foundation_realize E).mpr
      (wellFounded_internalFoundation (InvImage.wf Subtype.val ZFSet.mem_wf))),?_,?_,?_,?_⟩
  · have sem : lTruth emptyAxiom (Fin.elim0 : Fin 0 → LDomain.{u}) ↔
        ∃ a : LDomain.{u}, ∀ x : LDomain.{u}, x.val ∉ a.val := by
      change nativeSatisfies E emptyAxiom Fin.elim0 ↔ _
      simp only [emptyAxiom,scope_ex,scope_all,scope_neg,scope_mem]
      rfl
    exact sem.mpr ⟨⟨∅,basic_L_witnesses.1⟩,fun x => ZFSet.notMem_empty x.val⟩
  · have sem : lTruth pairingAxiom (Fin.elim0 : Fin 0 → LDomain.{u}) ↔
        ∀ x y : LDomain.{u}, ∃ p : LDomain.{u}, ∀ z : LDomain.{u},
          z.val ∈ p.val ↔ z = x ∨ z = y := by
      change nativeSatisfies E pairingAxiom Fin.elim0 ↔ _
      simp only [pairingAxiom,scope_all,scope_ex,scope_iff,scope_disj,scope_equal,scope_mem]
      rfl
    apply sem.mpr
    intro x y
    refine ⟨⟨{x.val,y.val},basic_L_witnesses.2.1 x y⟩,fun z => ?_⟩
    simp only [ZFSet.mem_pair,Subtype.ext_iff]
  · have sem : lTruth unionAxiom (Fin.elim0 : Fin 0 → LDomain.{u}) ↔
        ∀ x : LDomain.{u}, ∃ b : LDomain.{u}, ∀ z : LDomain.{u}, z.val ∈ b.val ↔
          ∃ y : LDomain.{u}, y.val ∈ x.val ∧ z.val ∈ y.val := by
      change nativeSatisfies E unionAxiom Fin.elim0 ↔ _
      simp only [unionAxiom,scope_all,scope_ex,scope_iff,scope_conj,scope_mem]
      rfl
    apply sem.mpr
    intro x
    refine ⟨⟨⋃₀x.val,basic_L_witnesses.2.2.1 x⟩,fun z => ?_⟩
    rw [ZFSet.mem_sUnion]
    constructor
    · rintro ⟨y,hy,hz⟩
      exact ⟨⟨y,constructible_transitive hy x.property⟩,hy,hz⟩
    · rintro ⟨y,hy,hz⟩
      exact ⟨y.val,hy,hz⟩
  · have hω : IsConstructible ZFSet.omega.{u} := by
      rw [Lemmatheca.SetTheory.NaturalNumbersAsSets.omega_eq_ordinal]
      exact basic_L_witnesses.2.2.2
    let ωL : LDomain.{u} := ⟨ZFSet.omega,hω⟩
    change nativeSatisfies E (Formula.ex (inductiveScoped 0)).toShared Fin.elim0
    apply (scope_ex E _ Fin.elim0).mpr
    refine ⟨ωL,?_⟩
    simp only [inductiveScoped,scope_conj,scope_ex,scope_all,scope_imp,scope_mem,
      Fin.snoc_last,Fin.snoc_castSucc]
    constructor
    · refine ⟨⟨∅,basic_L_witnesses.1⟩,?_,ZFSet.omega_zero⟩
      simp only [emptyScoped,scope_all,scope_neg,scope_mem,Fin.snoc_last,Fin.snoc_castSucc]
      exact fun x => ZFSet.notMem_empty x.val
    · intro x hx
      refine ⟨⟨insert x.val x.val,constructible_transitive (ZFSet.omega_succ hx) hω⟩,
        ZFSet.omega_succ hx,?_⟩
      simp only [successorScoped,scope_all,scope_iff,scope_disj,scope_equal,scope_mem,
        Fin.snoc_last,Fin.snoc_castSucc]
      intro z
      change z.val ∈ insert x.val x.val ↔ z.val ∈ x.val ∨ z = x
      simp only [ZFSet.mem_insert_iff,Subtype.ext_iff,or_comm]


/-- Reindex the scoped slots through the actual shared free-variable translation;
the library's relabel operation preserves all inner binders. -/
def reindex {n m} (p : membershipLanguage.BoundedFormula Empty n) (f : Fin n → Fin m) :
    membershipLanguage.BoundedFormula Empty m :=
  BoundedFormula.relabel (β := Empty) (n := m)
    (fun v => Sum.elim Empty.elim (fun i => Sum.inr (f i)) v) p.toFormula
theorem reindex_truth {M : Type u} (E : M → M → Prop) {n m}
    (p : membershipLanguage.BoundedFormula Empty n) (f : Fin n → Fin m) (a : Fin m → M) :
    nativeSatisfies E (reindex p f) a ↔ nativeSatisfies E p (fun i => a (f i)) := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  simp only [reindex,nativeSatisfies,BoundedFormula.realize_relabel]
  have he : (Sum.elim Empty.elim a ∘
      (fun v : Empty ⊕ Fin n => Sum.elim Empty.elim (fun i => Sum.inr (f i)) v)) =
      Sum.elim Empty.elim (fun i => a (f i)) := by
    funext v
    cases v with
    | inl v => exact Empty.elim v
    | inr i => rfl
  have hc : a ∘ Fin.castAdd 0 = a := by
    funext i
    rfl
  have hz : a ∘ Fin.natAdd m = (default : Fin 0 → M) := Subsingleton.elim _ _
  rw [hc,he,hz]
  change p.toFormula.Realize (Sum.elim Empty.elim (fun i => a (f i))) ↔ _
  simpa only [Function.comp_def,Sum.elim_inl,Sum.elim_inr] using
    BoundedFormula.realize_toFormula p (Sum.elim Empty.elim (fun i => a (f i)))

def separationIndex {n} : Fin (n+1) → Fin (n+2) :=
  Fin.lastCases (Fin.last (n+1)) (fun i => i.castSucc.castSucc)
def separationCode (M : ZFSet.{u}) {n} (p : membershipLanguage.BoundedFormula Empty (n+1))
    (a : Fin n → M) (x : M) : DefinitionCode M :=
  ⟨n+1,memScoped (Fin.last (n+1)) (Fin.last n).castSucc ⊓ reindex p separationIndex,
    Fin.snoc a x⟩
def classSeparation {n} (p : membershipLanguage.BoundedFormula Empty (n+1))
    (a : Fin n → LDomain.{u}) (x : LDomain.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ hz : IsConstructible z, lTruth p (Fin.snoc a ⟨z,hz⟩)) x.val
private theorem scopedMemTruth (M : ZFSet.{u}) {n} (i j : Fin n) (a : Fin n → M) :
    let := actualMembershipStructure M
    (memScoped (α := Empty) i j).Realize Empty.elim a ↔ (a i).val ∈ (a j).val := by rfl

private theorem separationCode_member (M : ZFSet.{u}) {n}
    (p : membershipLanguage.BoundedFormula Empty (n+1)) (a : Fin n → M) (x z : M) :
    z.val ∈ definedSubset M (separationCode M p a x) ↔
      z.val ∈ x.val ∧ setSatisfies M p (Fin.snoc a z) := by
  let := actualMembershipStructure M
  rw [definedSubset_members]
  change (memScoped (Fin.last (n+1)) (Fin.last n).castSucc ⊓ reindex p separationIndex).Realize
    Empty.elim (Fin.snoc (Fin.snoc a x) z) ↔ _
  rw [BoundedFormula.realize_inf]
  have hv : (fun i => (Fin.snoc (α := fun _ => M) (Fin.snoc (α := fun _ => M) a x) z) (separationIndex i)) = Fin.snoc a z := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [separationIndex]
  have hr := reindex_truth (fun x y : M => x.val ∈ y.val) p separationIndex
    (Fin.snoc (Fin.snoc a x) z)
  rw [hv] at hr
  apply and_congr ?_ hr
  simpa only [Fin.snoc_last,Fin.snoc_castSucc] using
    scopedMemTruth M (Fin.last (n+1)) (Fin.last n).castSucc (Fin.snoc (Fin.snoc a x) z)

private theorem reflect_snoc {n} (p : membershipLanguage.BoundedFormula Empty (n+1))
    (b : Ordinal.{u}) (hr : ReflectsNative constructibleHierarchy {⟨n+1,p⟩} b)
    (a : Fin n → level b) (z : level b) :
    setSatisfies (level b) p (Fin.snoc a z) ↔
      lTruth p (Fin.snoc (fun i => intoUnion constructibleHierarchy b (a i))
        (intoUnion constructibleHierarchy b z)) := by
  have h := hr.2 ⟨n+1,p⟩ (Finset.mem_singleton_self _) (Fin.snoc a z)
  change setSatisfies (level b) p (Fin.snoc a z) ↔
    lTruth p ((intoUnion constructibleHierarchy b) ∘ Fin.snoc a z) at h
  let inc : level b → LDomain.{u} := fun x => intoUnion constructibleHierarchy b x
  have hv : inc ∘ Fin.snoc a z = Fin.snoc (inc ∘ a) (inc z) := Fin.comp_snoc inc a z
  exact h.trans (Iff.of_eq (congrArg (lTruth p) hv))

theorem separation_at_reflecting_level {n}
    (p : membershipLanguage.BoundedFormula Empty (n+1)) (b : Ordinal.{u})
    (hr : ReflectsNative constructibleHierarchy {⟨n+1,p⟩} b)
    (a : Fin n → level b) (x : level b) :
    definedSubset (level b) (separationCode (level b) p a x) =
      classSeparation p (fun i => intoUnion constructibleHierarchy b (a i))
        (intoUnion constructibleHierarchy b x) := by
  ext z
  constructor
  · intro hz
    have hzM := (ZFSet.mem_sep.mp hz).1
    have hs := (separationCode_member _ p a x ⟨z,hzM⟩).mp hz
    rw [classSeparation,ZFSet.mem_sep]
    exact ⟨hs.1,⟨b,hzM⟩,(reflect_snoc p b hr a ⟨z,hzM⟩).mp hs.2⟩
  · intro hz
    obtain ⟨hzx,hzL,hφ⟩ := ZFSet.mem_sep.mp hz
    have hzM := (level_transitive b).mem_trans hzx x.property
    apply (separationCode_member _ p a x ⟨z,hzM⟩).mpr
    refine ⟨hzx,(reflect_snoc p b hr a ⟨z,hzM⟩).mpr ?_⟩
    exact hφ
theorem classSeparation_spec {n} (p : membershipLanguage.BoundedFormula Empty (n+1))
    (a : Fin n → LDomain.{u}) (x : LDomain.{u}) :
    IsConstructible (classSeparation p a x) ∧
      ∀ z : LDomain.{u}, z.val ∈ classSeparation p a x ↔
        z.val ∈ x.val ∧ lTruth p (Fin.snoc a z) := by
  have hspec (z : LDomain.{u}) :
      z.val ∈ classSeparation p a x ↔ z.val ∈ x.val ∧ lTruth p (Fin.snoc a z) := by
    rw [classSeparation,ZFSet.mem_sep]
    exact ⟨fun ⟨h,_,hp⟩ => ⟨h,hp⟩,fun ⟨h,hp⟩ => ⟨h,z.property,hp⟩⟩
  refine ⟨?_,hspec⟩
  obtain ⟨theta,hθ⟩ := finite_tuple_stage (Fin.snoc a x)
  let b := reflectingHeight constructibleHierarchy (expandFamily {⟨n+1,p⟩}) theta
  have hb := reflection_in_L {⟨n+1,p⟩} theta
  have hr : ReflectsNative constructibleHierarchy {⟨n+1,p⟩} b := ⟨hb.2.2.1,hb.2.2.2⟩
  let a' : Fin n → level b := fun i => ⟨(a i).val,
    level_monotone hb.1.le (by simpa only [Fin.snoc_castSucc] using hθ i.castSucc)⟩
  let x' : level b := ⟨x.val,level_monotone hb.1.le
    (by simpa only [Fin.snoc_last] using hθ (Fin.last n))⟩
  have ha : (fun i => intoUnion constructibleHierarchy b (a' i)) = a := by
    funext i; exact Subtype.ext rfl
  have hx : intoUnion constructibleHierarchy b x' = x := Subtype.ext rfl
  have he := separation_at_reflecting_level p b hr a' x'
  rw [ha,hx] at he
  refine ⟨b+1,?_⟩
  rw [level_successor]
  exact (Def_members _ _).mpr ⟨separationCode _ p a' x',he⟩

def ClassFunctional {n} (p : membershipLanguage.BoundedFormula Empty (n+2))
    (a : Fin n → LDomain.{u}) (x : LDomain.{u}) : Prop :=
  ∀ i : x.val, ∃! y : LDomain.{u}, lTruth p (Fin.snoc (Fin.snoc a (lMember x i)) y)
def replacementOutput {n} (p : membershipLanguage.BoundedFormula Empty (n+2))
    (a : Fin n → LDomain.{u}) (x : LDomain.{u}) (hf : ClassFunctional p a x)
    (i : x.val) : LDomain.{u} := Classical.choose (hf i)
def replacementRange {n} (p : membershipLanguage.BoundedFormula Empty (n+2))
    (a : Fin n → LDomain.{u}) (x : LDomain.{u}) (hf : ClassFunctional p a x) : ZFSet.{u} :=
  ZFSet.range (fun i => (replacementOutput p a x hf i).val)
theorem replacementOutput_spec {n} (p : membershipLanguage.BoundedFormula Empty (n+2))
    (a : Fin n → LDomain.{u}) (x : LDomain.{u}) (hf : ClassFunctional p a x) (i : x.val) :
    lTruth p (Fin.snoc (Fin.snoc a (lMember x i)) (replacementOutput p a x hf i)) ∧
      ∀ y, lTruth p (Fin.snoc (Fin.snoc a (lMember x i)) y) → y = replacementOutput p a x hf i := by
  exact (hf i).choose_spec
def replacementIndex {n} : Fin (n+2) → Fin (n+3) :=
  Fin.lastCases (Fin.last (n+1)).castSucc
    (Fin.lastCases (Fin.last (n+2)) (fun i => i.castSucc.castSucc.castSucc))
def replacementCode (M : ZFSet.{u}) {n} (p : membershipLanguage.BoundedFormula Empty (n+2))
    (a : Fin n → M) (x : M) : DefinitionCode M :=
  ⟨n+1,(memScoped (Fin.last (n+2)) (Fin.last n).castSucc.castSucc ⊓
    reindex p replacementIndex).ex,Fin.snoc a x⟩
theorem replacementCode_spec (M : ZFSet.{u}) (hM : M.IsTransitive) {n}
    (p : membershipLanguage.BoundedFormula Empty (n+2)) (a : Fin n → M) (x : M) (y : M) :
    y.val ∈ definedSubset M (replacementCode M p a x) ↔
      ∃ i : x.val, setSatisfies M p
        (Fin.snoc (Fin.snoc a ⟨i.val,hM x.val x.property i.property⟩) y) := by
  let := actualMembershipStructure M
  rw [definedSubset_members]
  change (memScoped (Fin.last (n+2)) (Fin.last n).castSucc.castSucc ⊓
    reindex p replacementIndex).ex.Realize Empty.elim (Fin.snoc (Fin.snoc a x) y) ↔ _
  rw [BoundedFormula.realize_ex]
  have sem (z : M) :
      (memScoped (Fin.last (n+2)) (Fin.last n).castSucc.castSucc ⊓ reindex p replacementIndex).Realize
        Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc a x) y) z) ↔
      z.val ∈ x.val ∧ setSatisfies M p (Fin.snoc (Fin.snoc a z) y) := by
    rw [BoundedFormula.realize_inf]
    have hv : (fun i => (Fin.snoc (α := fun _ => M) (Fin.snoc (α := fun _ => M) (Fin.snoc (α := fun _ => M) a x) y) z) (replacementIndex i)) =
        Fin.snoc (Fin.snoc a z) y := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [replacementIndex]
      · refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [replacementIndex]
    have hr := reindex_truth (fun x y : M => x.val ∈ y.val) p replacementIndex
      (Fin.snoc (Fin.snoc (Fin.snoc a x) y) z)
    rw [hv] at hr
    apply and_congr ?_ hr
    simpa only [Fin.snoc_last,Fin.snoc_castSucc] using
      scopedMemTruth M (Fin.last (n+2)) (Fin.last n).castSucc.castSucc
        (Fin.snoc (Fin.snoc (Fin.snoc a x) y) z)
  simp only [sem]
  constructor
  · rintro ⟨z,hzx,hp⟩
    exact ⟨⟨z.val,hzx⟩,hp⟩
  · rintro ⟨z,hp⟩
    exact ⟨⟨z.val,hM.mem_trans z.property x.property⟩,z.property,hp⟩
private theorem reflect_two {n} (p : membershipLanguage.BoundedFormula Empty (n+2))
    (b : Ordinal.{u}) (hr : ReflectsNative constructibleHierarchy {⟨n+2,p⟩} b)
    (a : Fin n → level b) (x y : level b) :
    setSatisfies (level b) p (Fin.snoc (Fin.snoc a x) y) ↔
      lTruth p (Fin.snoc (Fin.snoc (fun i => intoUnion constructibleHierarchy b (a i))
        (intoUnion constructibleHierarchy b x)) (intoUnion constructibleHierarchy b y)) := by
  have h := hr.2 ⟨n+2,p⟩ (Finset.mem_singleton_self _) (Fin.snoc (Fin.snoc a x) y)
  change setSatisfies (level b) p (Fin.snoc (Fin.snoc a x) y) ↔
    lTruth p ((intoUnion constructibleHierarchy b) ∘ Fin.snoc (Fin.snoc a x) y) at h
  let inc : level b → LDomain.{u} := fun x => intoUnion constructibleHierarchy b x
  have hv : inc ∘ Fin.snoc (Fin.snoc a x) y =
      Fin.snoc (Fin.snoc (inc ∘ a) (inc x)) (inc y) :=
    (Fin.comp_snoc inc (Fin.snoc a x) y).trans
      (congrArg (fun v : Fin (n+1) → LDomain.{u} =>
        Fin.snoc (α := fun _ => LDomain.{u}) v (inc y)) (Fin.comp_snoc inc a x))
  exact h.trans (Iff.of_eq (congrArg (lTruth p) hv))

theorem replacement_at_reflecting_level {n}
    (p : membershipLanguage.BoundedFormula Empty (n+2)) (b : Ordinal.{u})
    (hr : ReflectsNative constructibleHierarchy {⟨n+2,p⟩} b)
    (a : Fin n → level b) (x : level b)
    (hf : ClassFunctional p (fun i => intoUnion constructibleHierarchy b (a i))
      (intoUnion constructibleHierarchy b x))
    (hbound : ∀ y ∈ replacementRange p (fun i => intoUnion constructibleHierarchy b (a i))
      (intoUnion constructibleHierarchy b x) hf, y ∈ level b) :
    definedSubset (level b) (replacementCode (level b) p a x) =
      replacementRange p (fun i => intoUnion constructibleHierarchy b (a i))
        (intoUnion constructibleHierarchy b x) hf := by
  ext z
  constructor
  · intro hz
    have hzM := (ZFSet.mem_sep.mp hz).1
    obtain ⟨i,hi⟩ := (replacementCode_spec _ (level_transitive b) p a x ⟨z,hzM⟩).mp hz
    have ht := (reflect_two p b hr a
      ⟨i.val,(level_transitive b).mem_trans i.property x.property⟩ ⟨z,hzM⟩).mp hi
    have he := (replacementOutput_spec p _ _ hf i).2 (intoUnion constructibleHierarchy b ⟨z,hzM⟩) ht
    apply ZFSet.mem_range.mpr
    exact ⟨i,(congrArg Subtype.val he).symm⟩
  · intro hz
    have hzM := hbound z hz
    obtain ⟨i,hi⟩ := ZFSet.mem_range.mp hz
    apply (replacementCode_spec _ (level_transitive b) p a x ⟨z,hzM⟩).mpr
    refine ⟨i,(reflect_two p b hr a
      ⟨i.val,(level_transitive b).mem_trans i.property x.property⟩ ⟨z,hzM⟩).mpr ?_⟩
    have he : replacementOutput p _ _ hf i = intoUnion constructibleHierarchy b ⟨z,hzM⟩ :=
      Subtype.ext hi
    exact he ▸ (replacementOutput_spec p _ _ hf i).1
theorem classReplacement_spec {n} (p : membershipLanguage.BoundedFormula Empty (n+2))
    (a : Fin n → LDomain.{u}) (x : LDomain.{u}) (hf : ClassFunctional p a x) :
    IsConstructible (replacementRange p a x hf) ∧
      ∀ y : LDomain.{u}, y.val ∈ replacementRange p a x hf ↔
        ∃ i : x.val, lTruth p (Fin.snoc (Fin.snoc a (lMember x i)) y) := by
  have hspec (y : LDomain.{u}) : y.val ∈ replacementRange p a x hf ↔
      ∃ i : x.val, lTruth p (Fin.snoc (Fin.snoc a (lMember x i)) y) := by
    rw [replacementRange,ZFSet.mem_range]
    constructor
    · rintro ⟨i,hi⟩
      have he : replacementOutput p a x hf i = y := Subtype.ext hi
      exact ⟨i,he ▸ (replacementOutput_spec p a x hf i).1⟩
    · rintro ⟨i,hi⟩
      exact ⟨i,congrArg Subtype.val ((replacementOutput_spec p a x hf i).2 y hi).symm⟩
  refine ⟨?_,hspec⟩
  let R := replacementRange p a x hf
  have hR : ∀ y ∈ R, IsConstructible y := by
    intro y hy
    obtain ⟨i,hi⟩ := ZFSet.mem_range.mp hy
    exact hi ▸ (replacementOutput p a x hf i).property
  obtain ⟨theta,hθ⟩ := finite_tuple_stage (Fin.snoc a x)
  let rho := stageBound R hR
  let b := reflectingHeight constructibleHierarchy (expandFamily {⟨n+2,p⟩}) (max theta rho)
  have hb := reflection_in_L {⟨n+2,p⟩} (max theta rho)
  have hθb : theta ≤ b := (le_max_left _ _).trans hb.1.le
  have hρb : rho ≤ b := (le_max_right _ _).trans hb.1.le
  have hr : ReflectsNative constructibleHierarchy {⟨n+2,p⟩} b := ⟨hb.2.2.1,hb.2.2.2⟩
  let a' : Fin n → level b := fun i => ⟨(a i).val,
    level_monotone hθb (by simpa only [Fin.snoc_castSucc] using hθ i.castSucc)⟩
  let x' : level b := ⟨x.val,level_monotone hθb
    (by simpa only [Fin.snoc_last] using hθ (Fin.last n))⟩
  have ha : (fun i => intoUnion constructibleHierarchy b (a' i)) = a := by
    funext i; exact Subtype.ext rfl
  have hx : intoUnion constructibleHierarchy b x' = x := Subtype.ext rfl
  have hf' : ClassFunctional p (fun i => intoUnion constructibleHierarchy b (a' i))
      (intoUnion constructibleHierarchy b x') := by rw [ha,hx]; exact hf
  have hbound : ∀ y ∈ replacementRange p
      (fun i => intoUnion constructibleHierarchy b (a' i)) (intoUnion constructibleHierarchy b x') hf',
      y ∈ level b := by
    have hbase : ∀ y ∈ replacementRange p a x hf, y ∈ level b := by
      intro y hy
      exact level_monotone hρb ((stageBound_spec R hR ⟨y,hy⟩).2)
    simpa only [ha,hx] using hbase
  have he := replacement_at_reflecting_level p b hr a' x' hf' hbound
  have he' : definedSubset (level b) (replacementCode (level b) p a' x') = replacementRange p a x hf := by
    simpa only [ha,hx] using he
  refine ⟨b+1,?_⟩
  rw [level_successor]
  exact (Def_members _ _).mpr ⟨replacementCode _ p a' x',he'⟩

def internalPowerSet (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep IsConstructible (ZFSet.powerset x)
def powerSubsetCode (M : ZFSet.{u}) (x : M) : DefinitionCode M :=
  ⟨1,(subsetTest (1 : Fin 2) 0).toShared,![x]⟩
theorem powerSubsetCode_spec (b : Ordinal.{u}) (x : level b)
    (hbound : ∀ z ∈ internalPowerSet x.val, z ∈ level b) :
    definedSubset (level b) (powerSubsetCode (level b) x) = internalPowerSet x.val := by
  have sem (z : level b) :
      z.val ∈ definedSubset (level b) (powerSubsetCode (level b) x) ↔ z.val ⊆ x.val := by
    rw [definedSubset_members]
    change setSatisfies (level b) (subsetTest (1 : Fin 2) 0).toShared
      (Fin.snoc ![x] z) ↔ _
    rw [bounded_to_universe _ (level_transitive b),subsetTest_correct]
    rfl
  ext z
  constructor
  · intro hz
    have hzM := (ZFSet.mem_sep.mp hz).1
    have hs := (sem ⟨z,hzM⟩).mp hz
    exact ZFSet.mem_sep.mpr ⟨ZFSet.mem_powerset.mpr hs,⟨b,hzM⟩⟩
  · intro hz
    exact (sem ⟨z,hbound z hz⟩).mpr (ZFSet.mem_powerset.mp (ZFSet.mem_sep.mp hz).1)
theorem internalPowerSet_spec (x : LDomain.{u}) :
    IsConstructible (internalPowerSet x.val) ∧
      ∀ z : LDomain.{u}, z.val ∈ internalPowerSet x.val ↔ z.val ⊆ x.val := by
  have hspec (z : LDomain.{u}) : z.val ∈ internalPowerSet x.val ↔ z.val ⊆ x.val := by
    simp only [internalPowerSet,ZFSet.mem_sep,ZFSet.mem_powerset]
    exact ⟨And.left,fun h => ⟨h,z.property⟩⟩
  refine ⟨?_,hspec⟩
  let P := internalPowerSet x.val
  have hP : ∀ z ∈ P, IsConstructible z := fun _ hz => (ZFSet.mem_sep.mp hz).2
  let rho := stageBound P hP
  obtain ⟨a,hx⟩ := x.property
  let b := max a rho
  let x' : level b := ⟨x.val,level_monotone (le_max_left _ _) hx⟩
  have hbound : ∀ z ∈ internalPowerSet x'.val, z ∈ level b := by
    intro z hz
    exact level_monotone (le_max_right _ _) ((stageBound_spec P hP ⟨z,hz⟩).2)
  refine ⟨b+1,?_⟩
  rw [level_successor]
  exact (Def_members _ _).mpr ⟨powerSubsetCode _ x',powerSubsetCode_spec b x' hbound⟩

end
end Lemmatheca.SetTheory.ConstructibleInnerModel
