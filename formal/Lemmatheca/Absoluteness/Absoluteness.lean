import Lemmatheca.Absoluteness.Syntax

namespace Lemmatheca.SetTheory.Absoluteness
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u

abbrev setSatisfies (D : ZFSet.{u}) {n}
    (p : membershipLanguage.BoundedFormula Empty n) (a : Fin n → D) : Prop :=
  nativeSatisfies (fun x y : D => x.val ∈ y.val) p a
abbrev universeSatisfies {n} (p : membershipLanguage.BoundedFormula Empty n)
    (a : Fin n → ZFSet.{u}) : Prop := nativeSatisfies (fun x y => x ∈ y) p a

def inclusion (M N : ZFSet.{u}) (h : M ⊆ N) : M → N := fun x => ⟨x.val,h x.property⟩

def Absolute (M N : ZFSet.{u}) (h : M ⊆ N) {n}
    (p : membershipLanguage.BoundedFormula Empty n) : Prop :=
  ∀ a : Fin n → M, setSatisfies M p a ↔ setSatisfies N p (fun i => inclusion M N h (a i))
def Upward (M N : ZFSet.{u}) (h : M ⊆ N) {n}
    (p : membershipLanguage.BoundedFormula Empty n) : Prop :=
  ∀ a : Fin n → M, setSatisfies M p a → setSatisfies N p (fun i => inclusion M N h (a i))
def Downward (M N : ZFSet.{u}) (h : M ⊆ N) {n}
    (p : membershipLanguage.BoundedFormula Empty n) : Prop :=
  ∀ a : Fin n → M, setSatisfies N p (fun i => inclusion M N h (a i)) → setSatisfies M p a

private theorem holds_transitive (D : ZFSet.{u}) (hD : D.IsTransitive) {n}
    (p : DeltaZero n) (a : Fin n → D) :
    p.Holds (fun x y : D => x.val ∈ y.val) a ↔
      p.Holds (fun x y : ZFSet.{u} => x ∈ y) (fun i => (a i).val) := by
  induction p with
  | falsum => rfl
  | equal i j => exact Subtype.ext_iff
  | mem i j => rfl
  | imp p q ihp ihq =>
    simp only [DeltaZero.Holds, ihp, ihq]
  | @ball n j p ih =>
    change (∀ x : D, x.val ∈ (a j).val → p.Holds _ (Fin.snoc a x)) ↔
      ∀ x : ZFSet.{u}, x ∈ (a j).val → p.Holds _ (Fin.snoc (fun i => (a i).val) x)
    have hv (x : D) : (fun i => ((Fin.snoc (α := fun _ : Fin (n+1) => D) a x) i).val) =
        Fin.snoc (fun i => (a i).val) x.val := Fin.comp_snoc Subtype.val a x
    constructor
    · intro h x hx
      let b : D := ⟨x,hD (a j).val (a j).property hx⟩
      have h' := (ih (Fin.snoc a b)).mp (h b hx)
      simpa only [hv] using h'
    · intro h x hx
      apply (ih (Fin.snoc a x)).mpr
      simpa only [hv] using h x.val hx

theorem bounded_to_universe (D : ZFSet.{u}) (hD : D.IsTransitive) {n}
    (p : DeltaZero n) (a : Fin n → D) :
    setSatisfies D p.toShared a ↔ universeSatisfies p.toShared (fun i => (a i).val) := by
  exact (DeltaZero.toShared_realize (fun x y : D => x.val ∈ y.val) p a).trans
    ((holds_transitive D hD p a).trans
      (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) p (fun i => (a i).val)).symm)

theorem bounded_absolute (M N : ZFSet.{u}) (hM : M.IsTransitive) (hN : N.IsTransitive)
    (h : M ⊆ N) {n} (p : DeltaZero n) : Absolute M N h p.toShared := by
  intro a
  exact (bounded_to_universe M hM p a).trans
    (bounded_to_universe N hN p (fun i => inclusion M N h (a i))).symm

def emptyTest {n} (i : Fin n) : DeltaZero n :=
  .ball i (.neg (.equal (Fin.last n) (Fin.last n)))
def subsetTest {n} (i j : Fin n) : DeltaZero n :=
  .ball i (.mem (Fin.last n) j.castSucc)
def pairTest {n} (x y z : Fin n) : DeltaZero n :=
  .conj (.mem y x) (.conj (.mem z x)
    (.ball x (.disj (.equal (Fin.last n) y.castSucc) (.equal (Fin.last n) z.castSucc))))
def transitiveTest {n} (i : Fin n) : DeltaZero n :=
  .ball i (.ball (Fin.last n) (.mem (Fin.last (n+1)) i.castSucc.castSucc))
def ordinalTest {n} (i : Fin n) : DeltaZero n :=
  .conj (transitiveTest i) (.conj (.ball i (transitiveTest (Fin.last n)))
    (.ball i (.ball i.castSucc
      (.disj (.mem (Fin.last n).castSucc (Fin.last (n+1)))
        (.disj (.equal (Fin.last n).castSucc (Fin.last (n+1)))
          (.mem (Fin.last (n+1)) (Fin.last n).castSucc))))))

private theorem zero_truth {n} (p : DeltaZero n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies p.toShared a ↔ p.Holds (fun x y : ZFSet.{u} => x ∈ y) a :=
  DeltaZero.toShared_realize _ _ _

theorem emptyTest_correct {n} (i : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (emptyTest i).toShared a ↔ a i = ∅ := by
  rw [zero_truth]
  simp only [emptyTest, DeltaZero.Holds, DeltaZero.neg, Fin.snoc_last]
  simp only [true_implies]
  exact (ZFSet.eq_empty (a i)).symm
theorem subsetTest_correct {n} (i j : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (subsetTest i j).toShared a ↔ a i ⊆ a j := by
  rw [zero_truth]
  simp only [subsetTest, DeltaZero.Holds, Fin.snoc_last, Fin.snoc_castSucc]
  rfl
theorem pairTest_correct {n} (x y z : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (pairTest x y z).toShared a ↔ a x = {a y,a z} := by
  classical
  rw [zero_truth]
  simp only [pairTest, DeltaZero.conj, DeltaZero.disj, DeltaZero.neg, DeltaZero.Holds,
    Fin.snoc_last, Fin.snoc_castSucc, imp_false, not_not, not_imp]
  constructor
  · rintro ⟨hy,hz,hall⟩
    apply ZFSet.ext
    intro u
    simp only [ZFSet.mem_pair]
    constructor
    · intro hu
      by_cases h : u = a y
      · exact Or.inl h
      · exact Or.inr (hall u hu h)
    · intro h
      exact h.elim (fun h => h ▸ hy) (fun h => h ▸ hz)
  · rintro h
    simp only [h, ZFSet.mem_pair, true_or, or_true]
    exact ⟨trivial,trivial,fun _ h hne => h.resolve_left hne⟩
theorem transitiveTest_correct {n} (i : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (transitiveTest i).toShared a ↔ (a i).IsTransitive := by
  rw [zero_truth]
  simp only [transitiveTest, DeltaZero.Holds, Fin.snoc_last, Fin.snoc_castSucc]
  rfl
theorem ordinalTest_correct {n} (i : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (ordinalTest i).toShared a ↔ (a i).IsOrdinal := by
  classical
  rw [show universeSatisfies (ordinalTest i).toShared a ↔
    (ordinalTest i).Holds (fun x y : ZFSet.{u} => x ∈ y) a from
      DeltaZero.toShared_realize _ _ _]
  simp only [ordinalTest,transitiveTest,DeltaZero.conj,DeltaZero.disj,DeltaZero.neg,
    DeltaZero.Holds,Fin.snoc_last,Fin.snoc_castSucc,imp_false,not_not,not_imp]
  constructor
  · rintro ⟨htrans,hmem,hcomp⟩
    exact (ZFSet.isOrdinal_iff_forall_mem_isTransitive).mpr ⟨htrans,hmem⟩
  · intro h
    obtain ⟨ht,hm⟩ := (ZFSet.isOrdinal_iff_forall_mem_isTransitive).mp h
    refine ⟨ht,hm,?_⟩
    intro x hx y hy hxy hne
    exact ((h.mem hx).mem_trichotomous (h.mem hy)).resolve_left hxy |>.resolve_left hne


private theorem set_ex {n} (D : ZFSet.{u})
    (p : membershipLanguage.BoundedFormula Empty (n+1)) (a : Fin n → D) :
    setSatisfies D p.ex a ↔ ∃ x : D, setSatisfies D p (Fin.snoc a x) := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure D
    (fun x y : D => x.val ∈ y.val)
  exact BoundedFormula.realize_ex
private theorem set_all {n} (D : ZFSet.{u})
    (p : membershipLanguage.BoundedFormula Empty (n+1)) (a : Fin n → D) :
    setSatisfies D p.all a ↔ ∀ x : D, setSatisfies D p (Fin.snoc a x) := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure D
    (fun x y : D => x.val ∈ y.val)
  exact BoundedFormula.realize_all

theorem sigma_upward (M N : ZFSet.{u}) (hM : M.IsTransitive) (hN : N.IsTransitive)
    (h : M ⊆ N) {n} (p : SigmaOne n) : Upward M N h p.toShared := by
  induction p with
  | matrix p => exact fun a ha => (bounded_absolute M N hM hN h p a).mp ha
  | @ex n p ih =>
    intro a ha
    obtain ⟨x,hx⟩ := (set_ex M p.toShared a).mp ha
    apply (set_ex N p.toShared (fun i => inclusion M N h (a i))).mpr
    refine ⟨inclusion M N h x,?_⟩
    have hm : (fun i => inclusion M N h ((Fin.snoc (α := fun _ : Fin (n+1) => M) a x) i)) =
        Fin.snoc (fun i => inclusion M N h (a i)) (inclusion M N h x) :=
      Fin.comp_snoc (inclusion M N h) a x
    simpa only [hm] using ih (Fin.snoc a x) hx


theorem pi_downward (M N : ZFSet.{u}) (hM : M.IsTransitive) (hN : N.IsTransitive)
    (h : M ⊆ N) {n} (p : PiOne n) : Downward M N h p.toShared := by
  induction p with
  | matrix p => exact fun a ha => (bounded_absolute M N hM hN h p a).mpr ha
  | @all n p ih =>
    intro a ha
    apply (set_all M p.toShared a).mpr
    intro x
    apply ih (Fin.snoc a x)
    have hm : (fun i => inclusion M N h ((Fin.snoc (α := fun _ : Fin (n+1) => M) a x) i)) =
        Fin.snoc (fun i => inclusion M N h (a i)) (inclusion M N h x) :=
      Fin.comp_snoc (inclusion M N h) a x
    simpa only [hm] using (set_all N p.toShared (fun i => inclusion M N h (a i))).mp ha
      (inclusion M N h x)


def RelativeDeltaOne (T : membershipLanguage.Theory) {n}
    (theta : membershipLanguage.BoundedFormula Empty n) : Prop :=
  ∃ sig : SigmaOne n, ∃ pi : PiOne n,
    Derives T (theta.iff sig.toShared).alls ∧ Derives T (theta.iff pi.toShared).alls

private theorem model_derived_iff (T : membershipLanguage.Theory) (D : ZFSet.{u})
    (hD : TransitiveSetModel D T) {n}
    (p q : membershipLanguage.BoundedFormula Empty n)
    (hpq : Derives T (p.iff q).alls) (a : Fin n → D) :
    setSatisfies D p a ↔ setSatisfies D q a := by
  obtain ⟨x,hx⟩ := (ZFSet.eq_empty_or_nonempty D).resolve_left hD.1
  let : Nonempty D := ⟨⟨x,hx⟩⟩
  let := actualMembershipStructure D
  let : D ⊨ T := hD.2.2
  have hc := derives_sound hpq (Empty.elim : Empty → D)
    (fun B hB => by
      have hb : D ⊨ B := T.realize_sentence_of_mem hB
      have he : (default : Empty → D) = Empty.elim := Subsingleton.elim _ _
      simpa only [Sentence.Realize,he] using hb)
  exact BoundedFormula.realize_iff.mp ((BoundedFormula.realize_alls.mp hc) a)

/-- Both domains genuinely model the specified theory, and both equivalences are
actual shared proof-calculus derivations of their universal closures. -/
theorem relative_deltaOne_absolute (T : membershipLanguage.Theory)
    (M N : ZFSet.{u}) (hM : TransitiveSetModel M T) (hN : TransitiveSetModel N T)
    (h : M ⊆ N) {n} (theta : membershipLanguage.BoundedFormula Empty n)
    (sig : SigmaOne n) (pi : PiOne n)
    (hsig : Derives T (theta.iff sig.toShared).alls)
    (hpi : Derives T (theta.iff pi.toShared).alls) :
    Absolute M N h theta := by
  intro a
  have hmSig := model_derived_iff T M hM theta sig.toShared hsig a
  have hnSig := model_derived_iff T N hN theta sig.toShared hsig
    (fun i => inclusion M N h (a i))
  have hmPi := model_derived_iff T M hM theta pi.toShared hpi a
  have hnPi := model_derived_iff T N hN theta pi.toShared hpi
    (fun i => inclusion M N h (a i))
  constructor
  · intro ha
    exact hnSig.mpr (sigma_upward M N hM.2.1 hN.2.1 h sig a (hmSig.mp ha))
  · intro ha
    exact hmPi.mpr (pi_downward M N hM.2.1 hN.2.1 h pi a (hnPi.mp ha))


/-- The outer quantifier is unrestricted; this is not a DeltaZero constructor. -/
def powerSetFormula {n} (p a : Fin n) : membershipLanguage.BoundedFormula Empty n :=
  ((memScoped (Fin.last n) p.castSucc).iff
    (subsetTest (Fin.last n) a.castSucc).toShared).all

end Lemmatheca.SetTheory.Absoluteness
