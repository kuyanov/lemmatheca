import Lemmatheca.IsolatedTypes.IsolatedTypes
import Lemmatheca.QuantifierElimination.QuantifierEliminationShared
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Preorder.Finite

/-! Equality partitions and ordered equality partitions classify actual shared-syntax types. -/
namespace Lemmatheca.ModelTheory.IsolatedTypes

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Types
open Lemmatheca.ModelTheory.QuantifierElimination
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics

variable {n : ℕ}

private theorem same_type_of_similar {o : Bool} {T : (Shared.Lang o).Theory}
    (hqe : HasQuantifierElimination T) {M N : Type*}
    [(Shared.Lang o).Structure M] [(Shared.Lang o).Structure N]
    [Nonempty M] [Nonempty N] [M ⊨ T] [N ⊨ T]
    (a : Fin n → M) (b : Fin n → N)
    (hs : Similar (o := o) (Shared.relation (o := o)) (Shared.relation (o := o)) a b) :
    T.typeOf a = T.typeOf b := by
  apply SetLike.ext
  intro γ
  rw [Theory.CompleteType.mem_typeOf, Theory.CompleteType.mem_typeOf]
  obtain ⟨ψ, hψ, he⟩ := hqe n (Shared.pack (Formula.equivSentence.symm γ))
  have h := (he.realize_bd_iff (M := M)).trans
    ((Shared.qf_transport hψ hs).trans (he.realize_bd_iff (M := N)).symm)
  simpa only [Shared.pack_realize] using h

private theorem isolates_of_agreement {L : Language.{0, 0}} {T : L.Theory}
    {M : Type} [L.Structure M] [Nonempty M] [M ⊨ T]
    (a : Fin n → M) (θ : L.Formula (Fin n)) (hθ : θ.Realize a)
    (hagree : ∀ N : Theory.ModelType.{0, 0, 0} T, ∀ b : Fin n → N, θ.Realize b → T.typeOf b = T.typeOf a) :
    Isolates T (T.typeOf a) θ := by
  apply (isolates_iff_unique _ _).mpr
  refine ⟨Theory.CompleteType.formula_mem_typeOf.mpr hθ, fun q hq => ?_⟩
  obtain ⟨N, b, hb⟩ := T.exists_modelType_is_realized_in q
  have hθb : θ.Realize b := Theory.CompleteType.formula_mem_typeOf.mp (hb.symm ▸ hq)
  exact hb.symm.trans (hagree N b hθb)

private theorem unique_isolated {L : Language} {T : L.Theory}
    (p : T.CompleteType (Fin n)) (θ : L.Formula (Fin n)) (h : Isolates T p θ) :
    ∃! q : T.CompleteType (Fin n), Isolates T q θ := by
  refine ⟨p, h, fun q hq => ?_⟩
  exact ((isolates_iff_unique p θ).mp h).2 q hq.1

private theorem relationFormula_realize {M : Type*} [binaryRelLanguage.Structure M]
    (a : Fin n → M) (i j : Fin n) :
    (Relations.formula₂ (L := binaryRelLanguage) .rel (.var i) (.var j)).Realize a ↔
      Shared.relation (o := true) (a i) (a j) := by
  change Structure.RelMap (L := binaryRelLanguage) .rel
    (fun k => ((![(Term.var i : binaryRelLanguage.Term (Fin n)), Term.var j] k).relabel Sum.inl).realize (Sum.elim a (default : Fin 0 → M))) ↔ _
  have hv : (fun k : Fin 2 =>
      ((![(Term.var i : binaryRelLanguage.Term (Fin n)), Term.var j] k).relabel Sum.inl).realize (Sum.elim a (default : Fin 0 → M))) =
      ![a i, a j] := by
    funext k
    fin_cases k <;> rfl
  rw [hv]
  rfl

/-- Equalities and their negations specify precisely the displayed equivalence relation. -/
noncomputable def equalityPatternFormula (E : Setoid (Fin n)) :
    Language.empty.Formula (Fin n) := by
  classical
  exact Formula.iInf fun ij : Fin n × Fin n =>
    if E.r ij.1 ij.2 then (Term.var ij.1).equal (.var ij.2)
    else ((Term.var ij.1).equal (.var ij.2)).not

/-- The pattern formula gives exactly the equal-coordinate relation. -/
theorem equalityPattern_realize {M : Type*} [Language.empty.Structure M]
    (E : Setoid (Fin n)) (a : Fin n → M) :
    (equalityPatternFormula E).Realize a ↔ ∀ i j, E.r i j ↔ a i = a j := by
  classical
  rw [equalityPatternFormula, Formula.realize_iInf]
  constructor
  · intro h i j
    by_cases he : E.r i j
    · exact iff_of_true he (by simpa [he] using h (i, j))
    · exact iff_of_false he (by simpa [he] using h (i, j))
  · intro h ij
    by_cases he : E.r ij.1 ij.2
    · simpa [he] using (h ij.1 ij.2).mp he
    · simpa [he] using (mt (h ij.1 ij.2).mpr he)

/-- Every equivalence relation on finitely many positions is the equality pattern of a tuple. -/
theorem equalityPattern_exists (E : Setoid (Fin n)) :
    ∃ a : Fin n → ℕ, ∀ i j, E.r i j ↔ a i = a j := by
  classical
  let := Fintype.ofFinite (Quotient E)
  let e := Fintype.equivFin (Quotient E)
  refine ⟨fun i => (e (Quotient.mk E i)).val, fun i j => ?_⟩
  constructor
  · intro h
    exact congrArg (fun q : Quotient E => (e q).val) (Quotient.sound h)
  · intro h
    exact Quotient.exact (e.injective (Fin.ext h))

private theorem equality_isolates_tuple {M : Type} [Language.empty.Structure M]
    [Nonempty M] [M ⊨ Language.empty.infiniteTheory]
    (E : Setoid (Fin n)) (a : Fin n → M) (ha : (equalityPatternFormula E).Realize a) :
    Isolates Language.empty.infiniteTheory (Language.empty.infiniteTheory.typeOf a)
      (equalityPatternFormula E) := by
  apply isolates_of_agreement a _ ha
  intro N b hb
  apply same_type_of_similar (o := false) (T := Language.empty.infiniteTheory)
    Shared.equality_hasQuantifierElimination b a
  rintro (⟨i,j⟩ | ⟨r,_,_⟩)
  · exact ((equalityPattern_realize E b).mp hb i j).symm.trans
      ((equalityPattern_realize E a).mp ha i j)
  · exact isEmptyElim r

/-- Each equality pattern isolates exactly one complete type of the theory of infinite sets. -/
theorem equalityPattern_isolates (E : Setoid (Fin n)) :
    ∃! p : Language.empty.infiniteTheory.CompleteType (Fin n),
      Isolates Language.empty.infiniteTheory p (equalityPatternFormula E) := by
  let : Language.empty.Structure ℕ := Inhabited.trivialStructure Language.empty
  let : ℕ ⊨ Language.empty.infiniteTheory := Language.empty.model_infiniteTheory_iff.mpr inferInstance
  obtain ⟨a, ha⟩ := equalityPattern_exists E
  exact unique_isolated _ _ (equality_isolates_tuple E a ((equalityPattern_realize E a).mpr ha))

/-- Every complete type of infinite equality has exactly one equality pattern. -/
theorem equalityType_pattern (p : Language.empty.infiniteTheory.CompleteType (Fin n)) :
    ∃! E : Setoid (Fin n),
      Isolates Language.empty.infiniteTheory p (equalityPatternFormula E) := by
  obtain ⟨M, a, ha⟩ := Language.empty.infiniteTheory.exists_modelType_is_realized_in p
  let E := Setoid.ker a
  have hEa : (equalityPatternFormula E).Realize a := (equalityPattern_realize E a).mpr
    (fun _ _ => by rfl)
  refine ⟨E, ha ▸ equality_isolates_tuple E a hEa, fun F hF => ?_⟩
  have hFa : (equalityPatternFormula F).Realize a :=
    (isolator_realizes p _ hF a).mpr ((realizes_complete_iff p a).mpr ha.symm)
  apply Setoid.ext
  intro i j
  exact (equalityPattern_realize F a).mp hFa i j

/-- A finite coordinate set has only finitely many equivalence relations. -/
theorem finite_equalityPatterns (n : ℕ) : Finite (Setoid (Fin n)) := by
  apply Finite.of_injective (fun E : Setoid (Fin n) => {ij : Fin n × Fin n | E.r ij.1 ij.2})
  intro E F h
  exact Setoid.ext (fun i j => Set.ext_iff.mp h (i,j))

/-- Every finite-tuple complete-type space of infinite equality is finite. -/
theorem finite_equalityTypes (n : ℕ) :
    Finite (Language.empty.infiniteTheory.CompleteType (Fin n)) := by
  apply finite_iff_all_isolated.mpr
  intro p
  obtain ⟨E, hE, _⟩ := equalityType_pattern p
  exact ⟨_, hE⟩

/-- An ordered partition is its number of blocks and the surjective block-index map.
Using `Fin (n+1)` includes the empty pattern and bounds the number of nonempty blocks. -/
def OrderedPattern (n : ℕ) :=
  Σ k : Fin (n + 1), {r : Fin n → Fin k.val // Function.Surjective r}

/-- Within-block equalities and comparisons from earlier to later blocks. -/
noncomputable def orderPatternFormula (P : OrderedPattern n) :
    binaryRelLanguage.Formula (Fin n) :=
  Formula.iInf fun ij : Fin n × Fin n =>
    (if P.2.val ij.1 = P.2.val ij.2 then (Term.var ij.1).equal (.var ij.2) else ⊤) ⊓
    (if P.2.val ij.1 < P.2.val ij.2 then
      (Relations.formula₂ (L := binaryRelLanguage) .rel (.var ij.1) (.var ij.2)) else ⊤)

private theorem orderPattern_realize_of_atoms {M : Type*} [LinearOrder M]
    [binaryRelLanguage.Structure M] (P : OrderedPattern n) (a : Fin n → M)
    (hrel : ∀ i j, (Relations.formula₂ (L := binaryRelLanguage) .rel (.var i) (.var j)).Realize a ↔
      a i < a j) :
    (orderPatternFormula P).Realize a ↔
      ∀ i j, (P.2.val i = P.2.val j ↔ a i = a j) ∧
        (P.2.val i < P.2.val j ↔ a i < a j) := by
  rw [orderPatternFormula, Formula.realize_iInf]
  have heq (i j : Fin n) : ((Term.var i).equal (.var j) : binaryRelLanguage.Formula _).Realize a ↔
      a i = a j := Iff.rfl
  constructor
  · intro h
    have hE (i j) (hi : P.2.val i = P.2.val j) : a i = a j := by
      have hh := (Formula.realize_inf.mp (h (i,j))).1
      simpa only [hi, ↓reduceIte, heq] using hh
    have hR (i j) (hi : P.2.val i < P.2.val j) : a i < a j := by
      have hh := (Formula.realize_inf.mp (h (i,j))).2
      simpa only [hi, ↓reduceIte, hrel] using hh
    intro i j
    rcases lt_trichotomy (P.2.val i) (P.2.val j) with hr | he | hr
    · have ha := hR i j hr
      exact ⟨iff_of_false (ne_of_lt hr) (ne_of_lt ha), iff_of_true hr ha⟩
    · have ha := hE i j he
      exact ⟨iff_of_true he ha, iff_of_false (not_lt_of_ge he.ge) (not_lt_of_ge ha.ge)⟩
    · have ha := hR j i hr
      exact ⟨iff_of_false (ne_of_gt hr) (ne_of_gt ha),
        iff_of_false (not_lt_of_gt hr) (not_lt_of_gt ha)⟩
  · intro h ij
    apply Formula.realize_inf.mpr
    constructor
    · by_cases he : P.2.val ij.1 = P.2.val ij.2
      · simpa only [he, ↓reduceIte, heq] using (h ij.1 ij.2).1.mp he
      · simp only [he, ↓reduceIte, FirstOrder.Language.Formula.realize_top]
    · by_cases hr : P.2.val ij.1 < P.2.val ij.2
      · simpa only [hr, ↓reduceIte, hrel] using (h ij.1 ij.2).2.mp hr
      · simp only [hr, ↓reduceIte, FirstOrder.Language.Formula.realize_top]

/-- The ordered pattern gives both equality and strict comparison exactly. -/
theorem orderPattern_realize {M : Type*} [LinearOrder M]
    (P : OrderedPattern n) (a : Fin n → M) :
    let : binaryRelLanguage.Structure M := binaryRelStructure M (· < ·)
    (orderPatternFormula P).Realize a ↔
      ∀ i j, (P.2.val i = P.2.val j ↔ a i = a j) ∧
        (P.2.val i < P.2.val j ↔ a i < a j) := by
  let : binaryRelLanguage.Structure M := binaryRelStructure M (· < ·)
  exact orderPattern_realize_of_atoms P a (fun i j => (relationFormula_realize a i j).trans Iff.rfl)

/-- Rational values realize each specified ordered pattern. -/
theorem orderPattern_exists (P : OrderedPattern n) :
    let : binaryRelLanguage.Structure ℚ := binaryRelStructure ℚ (· < ·)
    ∃ a : Fin n → ℚ, (orderPatternFormula P).Realize a := by
  let : binaryRelLanguage.Structure ℚ := binaryRelStructure ℚ (· < ·)
  let a : Fin n → ℚ := fun i => (P.2.val i).val
  refine ⟨a, (orderPattern_realize P a).mpr (fun i j => ?_)⟩
  constructor
  · constructor
    · intro h
      exact congrArg (fun x : Fin P.1.val => (x.val : ℚ)) h
    · intro h
      apply Fin.ext
      change (((P.2.val i).val : ℚ) = ((P.2.val j).val : ℚ)) at h
      exact_mod_cast h
  · change ((P.2.val i).val < (P.2.val j).val) ↔
      (((P.2.val i).val : ℚ) < ((P.2.val j).val : ℚ))
    exact_mod_cast (Iff.rfl : (P.2.val i).val < (P.2.val j).val ↔
      (P.2.val i).val < (P.2.val j).val)

private theorem orderedPattern_ext (P Q : OrderedPattern n)
    (he : ∀ i j, P.2.val i = P.2.val j ↔ Q.2.val i = Q.2.val j)
    (hl : ∀ i j, P.2.val i < P.2.val j ↔ Q.2.val i < Q.2.val j) : P = Q := by
  classical
  obtain ⟨k, r, hr⟩ := P
  obtain ⟨l, t, ht⟩ := Q
  let pick (x : Fin k.val) : Fin n := Classical.choose (hr x)
  have hpick (x : Fin k.val) : r (pick x) = x := Classical.choose_spec (hr x)
  let f : Fin k.val → Fin l.val := t ∘ pick
  have hfi (i : Fin n) : f (r i) = t i := by
    exact (he (pick (r i)) i).mp (hpick (r i))
  have hf : StrictMono f := by
    intro x y hxy
    exact (hl (pick x) (pick y)).mp (by simpa only [hpick] using hxy)
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨i, hi⟩ := ht y
    exact ⟨r i, (hfi i).trans hi⟩
  have hcard : k.val = l.val := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (Equiv.ofBijective f ⟨hf.injective, hfs⟩)
  have hkl : k = l := Fin.ext hcard
  subst l
  have hrt : r = t := by
    funext i
    have hid := congrFun hf.eq_id (r i)
    exact hid.symm.trans (hfi i)
  subst t
  rfl

/-- Sorting the finitely many distinct tuple values produces one and only one ordered partition. -/
theorem tuple_orderedPattern {M : Type*} [LinearOrder M] (a : Fin n → M) :
    ∃! P : OrderedPattern n,
      ∀ i j, (P.2.val i = P.2.val j ↔ a i = a j) ∧
        (P.2.val i < P.2.val j ↔ a i < a j) := by
  classical
  let s := Finset.univ.image a
  have hcard : s.card ≤ n := (Finset.card_image_le).trans (by simp)
  let k : Fin (n + 1) := ⟨s.card, Nat.lt_succ_of_le hcard⟩
  let e := s.orderIsoOfFin (k := s.card) rfl
  let av (i : Fin n) : s := ⟨a i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let r : Fin n → Fin k.val := fun i => e.symm (av i)
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (e x).prop
    have hav : av i = e x := Subtype.ext hi
    exact ⟨i, by change e.symm (av i) = x; rw [hav, e.symm_apply_apply]⟩
  let P : OrderedPattern n := ⟨k, r, hr⟩
  have hP : ∀ i j, (P.2.val i = P.2.val j ↔ a i = a j) ∧
      (P.2.val i < P.2.val j ↔ a i < a j) := by
    intro i j
    exact ⟨e.symm.injective.eq_iff.trans Subtype.ext_iff, e.symm.lt_iff_lt⟩
  refine ⟨P, hP, fun Q hQ => ?_⟩
  exact orderedPattern_ext Q P
    (fun i j => (hQ i j).1.trans (hP i j).1.symm)
    (fun i j => (hQ i j).2.trans (hP i j).2.symm)

/-- The block count and finite block-index map give finitely many ordered patterns. -/
theorem finite_orderedPatterns (n : ℕ) : Finite (OrderedPattern n) := by
  unfold OrderedPattern
  infer_instance

private theorem order_isolates_tuple {M : Type} [binaryRelLanguage.Structure M]
    [Nonempty M] [M ⊨ Shared.strictDloTheory]
    (P : OrderedPattern n) (a : Fin n → M) (ha : (orderPatternFormula P).Realize a) :
    Isolates Shared.strictDloTheory (Shared.strictDloTheory.typeOf a) (orderPatternFormula P) := by
  let hM := Shared.model_strictDloTheory_iff.mp (inferInstance : M ⊨ Shared.strictDloTheory)
  let : LinearOrder M := Shared.orderOfAxioms (Shared.relation (o := true)) hM
  have hpa := (orderPattern_realize_of_atoms P a (fun i j => (relationFormula_realize a i j).trans Iff.rfl)).mp ha
  apply isolates_of_agreement a _ ha
  intro N b hb
  let hN := Shared.model_strictDloTheory_iff.mp (inferInstance : N ⊨ Shared.strictDloTheory)
  let : LinearOrder N := Shared.orderOfAxioms (Shared.relation (o := true)) hN
  have hpb := (orderPattern_realize_of_atoms P b (fun i j => (relationFormula_realize b i j).trans Iff.rfl)).mp hb
  apply same_type_of_similar (o := true) (T := Shared.strictDloTheory)
    Shared.strictDlo_hasQuantifierElimination b a
  rintro (⟨i,j⟩ | ⟨_,i,j⟩)
  · exact (hpb i j).1.symm.trans (hpa i j).1
  · change b i < b j ↔ a i < a j
    exact (hpb i j).2.symm.trans (hpa i j).2

/-- Each ordered partition isolates exactly one actual shared-language dense-order type. -/
theorem orderPattern_isolates (P : OrderedPattern n) :
    ∃! p : Shared.strictDloTheory.CompleteType (Fin n),
      Isolates Shared.strictDloTheory p (orderPatternFormula P) := by
  let : binaryRelLanguage.Structure ℚ := binaryRelStructure ℚ (· < ·)
  let : ℚ ⊨ Shared.strictDloTheory := Shared.model_strictDloTheory
  obtain ⟨a, ha⟩ := orderPattern_exists P
  exact unique_isolated _ _ (order_isolates_tuple P a ha)

/-- Every dense-order type has a unique ordered partition, retaining equal coordinates. -/
theorem dloType_pattern (p : Shared.strictDloTheory.CompleteType (Fin n)) :
    ∃! P : OrderedPattern n,
      Isolates Shared.strictDloTheory p (orderPatternFormula P) := by
  obtain ⟨M, a, ha⟩ := Shared.strictDloTheory.exists_modelType_is_realized_in p
  let hM := Shared.model_strictDloTheory_iff.mp (inferInstance : M ⊨ Shared.strictDloTheory)
  let : LinearOrder M := Shared.orderOfAxioms (Shared.relation (o := true)) hM
  obtain ⟨P, hP, _⟩ := tuple_orderedPattern a
  have hPa : (orderPatternFormula P).Realize a :=
    (orderPattern_realize_of_atoms P a (fun i j => (relationFormula_realize a i j).trans Iff.rfl)).mpr hP
  refine ⟨P, ha ▸ order_isolates_tuple P a hPa, fun Q hQ => ?_⟩
  have hQa : (orderPatternFormula Q).Realize a :=
    (isolator_realizes p _ hQ a).mpr ((realizes_complete_iff p a).mpr ha.symm)
  have hQp := (orderPattern_realize_of_atoms Q a (fun i j => (relationFormula_realize a i j).trans Iff.rfl)).mp hQa
  exact orderedPattern_ext Q P
    (fun i j => (hQp i j).1.trans (hP i j).1.symm)
    (fun i j => (hQp i j).2.trans (hP i j).2.symm)

/-- Dense linear orders have finitely many complete types at every finite tuple length. -/
theorem finite_dloTypes (n : ℕ) : Finite (Shared.strictDloTheory.CompleteType (Fin n)) := by
  apply finite_iff_all_isolated.mpr
  intro p
  obtain ⟨P, hP, _⟩ := dloType_pattern p
  exact ⟨_, hP⟩

/-- Equality of two coordinates. -/
def pairEqual : binaryRelLanguage.Formula (Fin 2) := (Term.var 0).equal (.var 1)
/-- The first coordinate is strictly below the second. -/
def pairLess : binaryRelLanguage.Formula (Fin 2) := Relations.formula₂ (L := binaryRelLanguage) .rel (.var 0) (.var 1)
/-- The second coordinate is strictly below the first. -/
def pairGreater : binaryRelLanguage.Formula (Fin 2) := Relations.formula₂ (L := binaryRelLanguage) .rel (.var 1) (.var 0)

/-- All three distinct two-coordinate types, with the stated isolators and exhaustive classification. -/
theorem dlo_two_types :
    ∃ pEq pLt pGt : Shared.strictDloTheory.CompleteType (Fin 2),
      pEq ≠ pLt ∧ pEq ≠ pGt ∧ pLt ≠ pGt ∧
      Isolates Shared.strictDloTheory pEq pairEqual ∧
      Isolates Shared.strictDloTheory pLt pairLess ∧
      Isolates Shared.strictDloTheory pGt pairGreater ∧
      ∀ p, p = pEq ∨ p = pLt ∨ p = pGt := by
  let : binaryRelLanguage.Structure ℚ := binaryRelStructure ℚ (· < ·)
  let : ℚ ⊨ Shared.strictDloTheory := Shared.model_strictDloTheory
  let aEq : Fin 2 → ℚ := ![0, 0]
  let aLt : Fin 2 → ℚ := ![0, 1]
  let aGt : Fin 2 → ℚ := ![1, 0]
  let pEq := Shared.strictDloTheory.typeOf aEq
  let pLt := Shared.strictDloTheory.typeOf aLt
  let pGt := Shared.strictDloTheory.typeOf aGt
  have hEq : Isolates Shared.strictDloTheory pEq pairEqual := by
    apply isolates_of_agreement aEq pairEqual (by rfl)
    intro N b hb
    change b 0 = b 1 at hb
    let hN := Shared.model_strictDloTheory_iff.mp (inferInstance : N ⊨ Shared.strictDloTheory)
    let : LinearOrder N := Shared.orderOfAxioms (Shared.relation (o := true)) hN
    apply same_type_of_similar (o := true) (T := Shared.strictDloTheory)
      Shared.strictDlo_hasQuantifierElimination b aEq
    rintro (⟨i,j⟩ | ⟨_,i,j⟩)
    · change b i = b j ↔ aEq i = aEq j
      fin_cases i <;> fin_cases j <;> simp [aEq, hb]
    · change b i < b j ↔ aEq i < aEq j
      fin_cases i <;> fin_cases j <;> simp [aEq, hb]
  have hLt : Isolates Shared.strictDloTheory pLt pairLess := by
    apply isolates_of_agreement aLt pairLess (by change (0 : ℚ) < 1; norm_num)
    intro N b hb
    let hN := Shared.model_strictDloTheory_iff.mp (inferInstance : N ⊨ Shared.strictDloTheory)
    let : LinearOrder N := Shared.orderOfAxioms (Shared.relation (o := true)) hN
    have hbl : b 0 < b 1 := (relationFormula_realize b 0 1).mp hb
    apply same_type_of_similar (o := true) (T := Shared.strictDloTheory)
      Shared.strictDlo_hasQuantifierElimination b aLt
    rintro (⟨i,j⟩ | ⟨_,i,j⟩)
    · change b i = b j ↔ aLt i = aLt j
      fin_cases i <;> fin_cases j <;> simp [aLt, ne_of_lt hbl, ne_of_gt hbl]
    · change b i < b j ↔ aLt i < aLt j
      fin_cases i <;> fin_cases j <;> simp [aLt, hbl, not_lt_of_gt hbl]
  have hGt : Isolates Shared.strictDloTheory pGt pairGreater := by
    apply isolates_of_agreement aGt pairGreater (by change (0 : ℚ) < 1; norm_num)
    intro N b hb
    let hN := Shared.model_strictDloTheory_iff.mp (inferInstance : N ⊨ Shared.strictDloTheory)
    let : LinearOrder N := Shared.orderOfAxioms (Shared.relation (o := true)) hN
    have hbl : b 1 < b 0 := (relationFormula_realize b 1 0).mp hb
    apply same_type_of_similar (o := true) (T := Shared.strictDloTheory)
      Shared.strictDlo_hasQuantifierElimination b aGt
    rintro (⟨i,j⟩ | ⟨_,i,j⟩)
    · change b i = b j ↔ aGt i = aGt j
      fin_cases i <;> fin_cases j <;> simp [aGt, ne_of_lt hbl, ne_of_gt hbl]
    · change b i < b j ↔ aGt i < aGt j
      fin_cases i <;> fin_cases j <;> simp [aGt, hbl, not_lt_of_gt hbl]
  refine ⟨pEq, pLt, pGt, ?_, ?_, ?_, hEq, hLt, hGt, ?_⟩
  · intro h
    have hm : pairLess ∈ formulas pEq := h.symm ▸ hLt.1
    have hv := Theory.CompleteType.formula_mem_typeOf.mp hm
    change (0 : ℚ) < 0 at hv
    exact (lt_irrefl _) hv
  · intro h
    have hm : pairGreater ∈ formulas pEq := h.symm ▸ hGt.1
    have hv := Theory.CompleteType.formula_mem_typeOf.mp hm
    change (0 : ℚ) < 0 at hv
    exact (lt_irrefl _) hv
  · intro h
    have hm : pairGreater ∈ formulas pLt := h.symm ▸ hGt.1
    have hv := Theory.CompleteType.formula_mem_typeOf.mp hm
    change (1 : ℚ) < 0 at hv
    norm_num at hv
  · intro p
    obtain ⟨M, a, ha⟩ := Shared.strictDloTheory.exists_modelType_is_realized_in p
    let hM := Shared.model_strictDloTheory_iff.mp (inferInstance : M ⊨ Shared.strictDloTheory)
    let : LinearOrder M := Shared.orderOfAxioms (Shared.relation (o := true)) hM
    rcases lt_trichotomy (a 0) (a 1) with hl | he | hg
    · right; left
      apply ((isolates_iff_unique pLt pairLess).mp hLt).2 p
      have ht : pairLess.Realize a := (relationFormula_realize a 0 1).mpr hl
      exact ha ▸ Theory.CompleteType.formula_mem_typeOf.mpr ht
    · left
      apply ((isolates_iff_unique pEq pairEqual).mp hEq).2 p
      have ht : pairEqual.Realize a := he
      exact ha ▸ Theory.CompleteType.formula_mem_typeOf.mpr ht
    · right; right
      apply ((isolates_iff_unique pGt pairGreater).mp hGt).2 p
      have ht : pairGreater.Realize a := (relationFormula_realize a 1 0).mpr hg
      exact ha ▸ Theory.CompleteType.formula_mem_typeOf.mpr ht

end Lemmatheca.ModelTheory.IsolatedTypes
