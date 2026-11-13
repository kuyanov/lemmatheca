import Lemmatheca.InfinitaryLogic.Syntax
import Lemmatheca.BackAndForth.BackAndForth
import Mathlib.ModelTheory.Encoding
import Mathlib.SetTheory.Cardinal.Aleph

/-! Scott analysis with native finite-context infinitary formulas. -/
namespace Lemmatheca.ModelTheory.ScottSentences

open FirstOrder FirstOrder.Language
open scoped Ordinal

universe u v w w' z

namespace IL
export Lemmatheca.MathematicalLogic.InfinitaryLogic
  (Formula Sentence Realize)
end IL

abbrev ScopedFormula (L : Language.{u,v}) (n : ℕ) := IL.Formula L Empty n

/-- A countable indexed conjunction, using actual syntax and truth padding. -/
noncomputable def indexedConj {L : Language.{u,v}} {n : ℕ} {ι : Type z}
    [Countable ι] (f : ι → ScopedFormula L n) : ScopedFormula L n := by
  letI := Encodable.ofCountable ι
  exact .conj fun k => match Encodable.decode (α := ι) k with
    | some i => f i
    | none => .top

noncomputable def indexedDisj {L : Language.{u,v}} {n : ℕ} {ι : Type z}
    [Countable ι] (f : ι → ScopedFormula L n) : ScopedFormula L n :=
  (indexedConj fun i => (f i).neg).neg

variable {L : Language.{u,v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

theorem realize_indexedConj {n : ℕ} {ι : Type z} [Countable ι]
    (f : ι → ScopedFormula L n) (b : Fin n → N) :
    IL.Realize (indexedConj f) Empty.elim b ↔
      ∀ i, IL.Realize (f i) Empty.elim b := by
  classical
  let := Encodable.ofCountable ι
  change (∀ k, IL.Realize (match Encodable.decode (α := ι) k with
    | some i => f i | none => .top) Empty.elim b) ↔ _
  constructor
  · intro h i
    simpa only [Encodable.encodek] using h (Encodable.encode i)
  · intro h k
    cases Encodable.decode (α := ι) k with
    | none =>
      exact (Lemmatheca.MathematicalLogic.InfinitaryLogic.realize_abbreviations
        (.falsum : ScopedFormula L n) .falsum Empty.elim b).1
    | some i => exact h i

theorem realize_indexedDisj {n : ℕ} {ι : Type z} [Countable ι]
    (f : ι → ScopedFormula L n) (b : Fin n → N) :
    IL.Realize (indexedDisj f) Empty.elim b ↔
      ∃ i, IL.Realize (f i) Empty.elim b := by
  classical
  simp only [indexedDisj,
    Lemmatheca.MathematicalLogic.InfinitaryLogic.realize_neg, realize_indexedConj]
  simp

abbrev AtomicFormula (L : Language.{u,v}) (n : ℕ) :=
  {φ : L.Formula (Fin n) // φ.IsAtomic}

/-- Agreement on all actual atomic formulas, including arbitrary terms. -/
def AtomicAgreement {n : ℕ} (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∀ φ : AtomicFormula L n, φ.val.Realize a ↔ φ.val.Realize b

abbrev TupleRelation (M : Type w) (N : Type w') :=
  ∀ n : ℕ, (Fin n → M) → (Fin n → N) → Prop

/-- The same monotone extension operation at every successor stage. -/
def extensionStep (R : TupleRelation M N) : TupleRelation M N := fun n a b =>
  R n a b ∧ (∀ c : M, ∃ d : N, R (n+1) (Fin.snoc a c) (Fin.snoc b d)) ∧
    (∀ d : N, ∃ c : M, R (n+1) (Fin.snoc a c) (Fin.snoc b d))

/-- Ordinal comparisons exist independently of any countability hypothesis. -/
noncomputable def comparison (α : Ordinal.{0}) : TupleRelation M N :=
  Ordinal.limitRecOn α (fun _ a b => AtomicAgreement (L := L) a b)
    (fun _ R => extensionStep R) (fun β _ R n a b => ∀ γ, ∀ h : γ < β, R γ h n a b)

theorem comparison_zero {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    comparison (L := L) 0 n a b ↔ AtomicAgreement (L := L) a b := by
  simp only [comparison, Ordinal.limitRecOn_zero]

theorem comparison_successor (α : Ordinal.{0}) {n : ℕ}
    (a : Fin n → M) (b : Fin n → N) :
    comparison (L := L) (α+1) n a b ↔
      extensionStep (comparison (L := L) α) n a b := by
  simp only [comparison, Ordinal.limitRecOn_add_one]

theorem comparison_limit (α : Ordinal.{0}) (hα : Order.IsSuccLimit α)
    {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    comparison (L := L) α n a b ↔ ∀ β < α, comparison (L := L) β n a b := by
  simp only [comparison, Ordinal.limitRecOn_limit _ _ _ _ hα]

theorem comparison_decreasing {α β : Ordinal.{0}} (h : β ≤ α) {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} :
    comparison (L := L) α n a b → comparison (L := L) β n a b := by
  induction α using Ordinal.limitRecOn generalizing β with
  | zero =>
    have hb : β = 0 := le_antisymm h bot_le
    subst β
    exact id
  | add_one α ih =>
    intro hR
    rcases lt_or_eq_of_le h with hlt | rfl
    · exact ih (Order.lt_add_one_iff.mp hlt) ((comparison_successor α a b).mp hR).1
    · exact hR
  | limit α hα ih =>
    intro hR
    rcases lt_or_eq_of_le h with hlt | rfl
    · exact (comparison_limit α hα a b).mp hR β hlt
    · exact hR

theorem comparison_reflexive (α : Ordinal.{0}) {n : ℕ} (a : Fin n → M) :
    comparison (L := L) α n a a := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero => exact (comparison_zero a a).mpr (fun _ => Iff.rfl)
  | add_one α ih =>
    apply (comparison_successor α a a).mpr
    exact ⟨ih a, (fun c => ⟨c, ih (Fin.snoc a c)⟩), fun c => ⟨c, ih (Fin.snoc a c)⟩⟩
  | limit α hα ih =>
    exact (comparison_limit α hα a a).mpr (fun β hβ => ih β hβ a)

private theorem realize_and {n : ℕ} (φ ψ : ScopedFormula L n) (b : Fin n → N) :
    IL.Realize (φ.and ψ) Empty.elim b ↔
      IL.Realize φ Empty.elim b ∧ IL.Realize ψ Empty.elim b :=
  (Lemmatheca.MathematicalLogic.InfinitaryLogic.realize_abbreviations φ ψ Empty.elim b).2.1

section Syntax
variable [Countable L.Symbols] [Countable M]

/-- The native signed atomic conjunction in a protected bound context. -/
noncomputable def atomicDescription {n : ℕ} (a : Fin n → M) : ScopedFormula L n := by
  classical
  exact indexedConj fun φ : AtomicFormula L n =>
    let ψ : ScopedFormula L n := .ofFirstOrder (BoundedFormula.relabel (Sum.inr : Fin n → Empty ⊕ Fin n) φ.val)
    if φ.val.Realize a then ψ else ψ.neg

omit [Countable M] in
theorem atomicDescription_realize {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    IL.Realize (atomicDescription (L := L) a) Empty.elim b ↔
      AtomicAgreement (L := L) a b := by
  classical
  unfold atomicDescription
  rw [realize_indexedConj]
  unfold AtomicAgreement
  apply forall_congr'
  intro φ
  have hr : IL.Realize (Lemmatheca.MathematicalLogic.InfinitaryLogic.Formula.ofFirstOrder
      (BoundedFormula.relabel (Sum.inr : Fin n → Empty ⊕ Fin n) φ.val)) Empty.elim b ↔
      φ.val.Realize b :=
    (Lemmatheca.MathematicalLogic.InfinitaryLogic.realize_ofFirstOrder _ Empty.elim b).trans
      (FirstOrder.Language.Formula.realize_relabel_sumInr φ.val)
  by_cases h : φ.val.Realize a <;>
    simp only [h, ite_true, ite_false,
      Lemmatheca.MathematicalLogic.InfinitaryLogic.realize_neg, hr, true_iff, false_iff]

/-- Successor syntax binds the newly appended coordinate before combining components. -/
noncomputable def formulaStep
    (F : ∀ n : ℕ, (Fin n → M) → ScopedFormula L n) :
    ∀ n : ℕ, (Fin n → M) → ScopedFormula L n := fun n a =>
  (F n a).and ((indexedConj fun c : M => (F (n+1) (Fin.snoc a c)).ex).and
    (.all (indexedDisj fun c : M => F (n+1) (Fin.snoc a c))))

/-- Formula recursion is restricted to countable ordinals by an explicit argument. -/
noncomputable def comparisonFormula (α : Ordinal.{0}) :
    α < ω₁ → ∀ n : ℕ, (Fin n → M) → ScopedFormula L n :=
  Ordinal.limitRecOn α (fun _ _ a => atomicDescription a)
    (fun β F h => formulaStep (F (lt_trans (lt_add_one β) h)))
    (fun β _ F h n a => by
      letI : Countable (Set.Iio β) :=
        (Cardinal.countable_Iio_of_lt_omega_one h).to_subtype
      exact indexedConj fun γ : Set.Iio β => F γ.val γ.property (lt_trans γ.property h) n a)

omit [L.Structure M] [Countable L.Symbols] in
private theorem realize_formulaStep
    (F : ∀ n : ℕ, (Fin n → M) → ScopedFormula L n) {n : ℕ}
    (a : Fin n → M) (b : Fin n → N) :
    IL.Realize (formulaStep F n a) Empty.elim b ↔
      extensionStep (fun n a b => IL.Realize (F n a) Empty.elim b) n a b := by
  simp only [formulaStep, realize_and, realize_indexedConj,
    Lemmatheca.MathematicalLogic.InfinitaryLogic.realize_ex,
    Lemmatheca.MathematicalLogic.InfinitaryLogic.Realize,
    realize_indexedDisj, extensionStep]

theorem comparisonFormula_realize (α : Ordinal.{0}) (hα : α < ω₁)
    {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    IL.Realize (comparisonFormula (L := L) α hα n a) Empty.elim b ↔
      comparison (L := L) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero =>
    have hw : comparisonFormula (L := L) (M := M) 0 hα n a = atomicDescription a := by
      simp only [comparisonFormula, Ordinal.limitRecOn_zero]
    rw [hw, atomicDescription_realize, comparison_zero]
  | add_one α ih =>
    let hprev : α < ω₁ := lt_trans (lt_add_one α) hα
    have hw : comparisonFormula (L := L) (M := M) (α+1) hα n a =
        formulaStep (comparisonFormula (L := L) (M := M) α hprev) n a := by
      simp only [comparisonFormula, Ordinal.limitRecOn_add_one]
    rw [hw, realize_formulaStep, comparison_successor]
    simp only [extensionStep, ih hprev]
  | limit α hlim ih =>
    let : Countable (Set.Iio α) := (Cardinal.countable_Iio_of_lt_omega_one hα).to_subtype
    have hw : comparisonFormula (L := L) (M := M) α hα n a =
        indexedConj (fun β : Set.Iio α =>
          comparisonFormula (L := L) (M := M) β.val (lt_trans β.property hα) n a) := by
      simp only [comparisonFormula, Ordinal.limitRecOn_limit _ _ _ _ hlim]
    rw [hw, realize_indexedConj, comparison_limit α hlim]
    constructor
    · intro h β hβ
      exact (ih β hβ (lt_trans hβ hα) a b).mp (h ⟨β,hβ⟩)
    · intro h β
      exact (ih β.val β.property (lt_trans β.property hα) a b).mpr (h β.val β.property)

end Syntax

/-- All tuple lengths at once are part of the stabilization assertion. -/
def Stabilizes (M : Type w) [L.Structure M] (α : Ordinal.{0}) : Prop :=
  ∀ n (a b : Fin n → M),
    comparison (L := L) α n a b ↔ comparison (L := L) (α+1) n a b

theorem countable_stabilization [Countable M] :
    ∃ α : Ordinal.{0}, α < ω₁ ∧ Stabilizes (L := L) M α := by
  classical
  by_contra h
  push Not at h
  let Pair := Σ n : ℕ, (Fin n → M) × (Fin n → M)
  have drops (α : Set.Iio (ω₁ : Ordinal.{0})) : ∃ p : Pair,
      comparison (L := L) α.val p.fst p.snd.1 p.snd.2 ∧
        ¬ comparison (L := L) (α.val+1) p.fst p.snd.1 p.snd.2 := by
    have hn := h α.val α.property
    unfold Stabilizes at hn
    push Not at hn
    obtain ⟨n, a, b, hn⟩ := hn
    have hm : comparison (L := L) (α.val+1) n a b → comparison (L := L) α.val n a b :=
      comparison_decreasing (le_of_lt (lt_add_one α.val))
    exact ⟨⟨n, a, b⟩, by tauto⟩
  choose pair hp using drops
  have separated (α β : Set.Iio (ω₁ : Ordinal.{0})) (hlt : α.val < β.val) :
      pair α ≠ pair β := by
    intro heq
    have hR := comparison_decreasing (L := L) (Order.add_one_le_iff.mpr hlt) (hp β).1
    apply (hp α).2
    exact Eq.mpr (congrArg (fun p : Pair =>
      comparison (L := L) (α.val+1) p.fst p.snd.1 p.snd.2) heq) hR
  have hinj : Function.Injective pair := by
    intro α β heq
    apply Subtype.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact separated α β hlt heq
    · exact separated β α hgt heq.symm
  have hc : Countable (Set.Iio (ω₁ : Ordinal.{0})) := hinj.countable
  have hb := Cardinal.mk_le_aleph0_iff.mpr hc
  rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0, Ordinal.card_omega] at hb
  exact Cardinal.aleph0_lt_aleph_one.not_ge hb

theorem comparison_stable_later {α β : Ordinal.{0}}
    (hα : Stabilizes (L := L) M α) (hβ : α ≤ β) {n : ℕ} (a b : Fin n → M) :
    comparison (L := L) β n a b ↔ comparison (L := L) α n a b := by
  induction β using Ordinal.limitRecOn generalizing n with
  | zero =>
    have heq : α = 0 := le_antisymm hβ bot_le
    subst α
    rfl
  | add_one β ih =>
    rcases lt_or_eq_of_le hβ with hlt | heq
    · have hle : α ≤ β := Order.lt_add_one_iff.mp hlt
      constructor
      · exact comparison_decreasing hβ
      · intro hR
        have hs := (comparison_successor α a b).mp ((hα n a b).mp hR)
        apply (comparison_successor β a b).mpr
        refine ⟨(ih hle a b).mpr hR, ?_, ?_⟩
        · intro c
          obtain ⟨d,hd⟩ := hs.2.1 c
          exact ⟨d,(ih hle (Fin.snoc a c) (Fin.snoc b d)).mpr hd⟩
        · intro d
          obtain ⟨c,hc⟩ := hs.2.2 d
          exact ⟨c,(ih hle (Fin.snoc a c) (Fin.snoc b d)).mpr hc⟩
    · subst α
      rfl
  | limit β hlim ih =>
    constructor
    · exact comparison_decreasing hβ
    · intro hR
      apply (comparison_limit β hlim a b).mpr
      intro γ hγ
      by_cases hle : α ≤ γ
      · exact (ih γ hγ hle a b).mpr hR
      · exact comparison_decreasing (le_of_lt (lt_of_not_ge hle)) hR

/-- Close exactly the finite protected context, from the final slot inward. -/
def universalClosure : {n : ℕ} → ScopedFormula L n → IL.Sentence L
  | 0, φ => φ
  | _n+1, φ => universalClosure (.all φ)

theorem universalClosure_realize {n : ℕ} (φ : ScopedFormula L n) :
    Lemmatheca.MathematicalLogic.InfinitaryLogic.Sentence.Realize (universalClosure φ) N ↔
      ∀ b : Fin n → N, IL.Realize φ Empty.elim b := by
  revert φ
  induction n with
  | zero =>
    intro φ
    change IL.Realize φ Empty.elim Fin.elim0 ↔ ∀ b : Fin 0 → N, IL.Realize φ Empty.elim b
    constructor
    · intro h b
      have hb : b = Fin.elim0 := Subsingleton.elim _ _
      simpa only [hb] using h
    · intro h
      exact h Fin.elim0
  | succ n ih =>
    intro φ
    rw [universalClosure, ih]
    change (∀ b : Fin n → N, ∀ x : N, IL.Realize φ Empty.elim (Fin.snoc b x)) ↔ _
    constructor
    · intro h b
      simpa only [Fin.snoc_init_self] using h (Fin.init b) (b (Fin.last n))
    · intro h b x
      exact h (Fin.snoc b x)

section ScottSentence
variable [Countable L.Symbols] [Countable M]

private theorem countable_successor {α : Ordinal.{0}} (hα : α < ω₁) : α+1 < ω₁ := by
  simpa only [Order.succ_eq_add_one] using (Cardinal.isSuccLimit_omega 1).succ_lt hα

/-- The specified sentence for a supplied countable rank. -/
noncomputable def sentenceAt (α : Ordinal.{0}) (hα : α < ω₁) : IL.Sentence L :=
  (comparisonFormula (L := L) (M := M) α hα 0 Fin.elim0).and
    (indexedConj fun p : Σ n : ℕ, Fin n → M =>
      universalClosure (.imp (comparisonFormula α hα p.fst p.snd)
        (comparisonFormula (α+1) (countable_successor hα) p.fst p.snd)))

theorem sentenceAt_self (α : Ordinal.{0}) (hα : α < ω₁)
    (hstable : Stabilizes (L := L) M α) :
    Lemmatheca.MathematicalLogic.InfinitaryLogic.Sentence.Realize (sentenceAt (L := L) (M := M) α hα) M := by
  change IL.Realize _ Empty.elim Fin.elim0
  rw [sentenceAt, realize_and]
  constructor
  · exact (comparisonFormula_realize α hα Fin.elim0 Fin.elim0).mpr
      (comparison_reflexive α Fin.elim0)
  · rw [realize_indexedConj]
    rintro ⟨n,a⟩
    change Lemmatheca.MathematicalLogic.InfinitaryLogic.Sentence.Realize (universalClosure _) M
    rw [universalClosure_realize]
    intro b
    change IL.Realize (comparisonFormula α hα n a) Empty.elim b → _
    intro h
    exact (comparisonFormula_realize (α+1) _ a b).mpr
      ((hstable n a b).mp ((comparisonFormula_realize α hα a b).mp h))

omit [Countable L.Symbols] [Countable M] in
private theorem atomic_eq_iff {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : AtomicAgreement (L := L) a b) (i j : Fin n) : a i = a j ↔ b i = b j :=
  h ⟨.equal (.var (.inl i)) (.var (.inl j)), .equal _ _⟩

/-- The finite coordinate map is specified, rather than an unrelated partial map. -/
noncomputable def tupleMap {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : AtomicAgreement (L := L) a b) : BackAndForth.FinitePartialIso L M N := by
  classical
  refine
  { dom := Set.range a
    finite_dom := Set.finite_range a
    toFun := fun x => b (Classical.choose x.property)
    injective := ?_
    atomic := ?_ }
  · intro x y hxy
    apply Subtype.ext
    exact (Classical.choose_spec x.property).symm.trans
      (((atomic_eq_iff h (Classical.choose x.property) (Classical.choose y.property)).mpr hxy).trans
        (Classical.choose_spec y.property))
  · intro k φ hφ x
    let idx : Fin k → Fin n := fun i => Classical.choose (x i).property
    have hφ' : (φ.relabel idx).IsAtomic := hφ.relabel (fun i => Sum.inl (idx i))
    have hh := h ⟨φ.relabel idx, hφ'⟩
    rw [FirstOrder.Language.Formula.realize_relabel,
      FirstOrder.Language.Formula.realize_relabel] at hh
    have hx : a ∘ idx = Subtype.val ∘ x := by
      funext i
      exact Classical.choose_spec (x i).property
    change φ.Realize (b ∘ idx) ↔ φ.Realize (Subtype.val ∘ x)
    simpa only [hx] using hh.symm

omit [Countable L.Symbols] [Countable M] in
theorem tupleMap_coordinate {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : AtomicAgreement (L := L) a b) (i : Fin n) :
    (tupleMap a b h).toFun ⟨a i, Set.mem_range_self i⟩ = b i := by
  change b (Classical.choose (Set.mem_range_self i)) = b i
  exact (atomic_eq_iff h _ i).mp (Classical.choose_spec (Set.mem_range_self i))

omit [Countable L.Symbols] [Countable M] in
theorem tupleMap_append {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (c : M) (d : N) (h : AtomicAgreement (L := L) a b)
    (h' : AtomicAgreement (L := L) (Fin.snoc a c) (Fin.snoc b d)) :
    tupleMap a b h ≤ tupleMap (Fin.snoc a c) (Fin.snoc b d) h' := by
  have hdom : Set.range a ⊆ Set.range (Fin.snoc a c) := by
    rintro x ⟨i,rfl⟩
    exact ⟨i.castSucc, by simp⟩
  refine ⟨hdom, ?_⟩
  rintro ⟨x, i, rfl⟩
  have hq := tupleMap_coordinate (Fin.snoc a c) (Fin.snoc b d) h' i.castSucc
  simp only [Fin.snoc_castSucc] at hq
  exact hq.trans (tupleMap_coordinate a b h i).symm

omit [Countable L.Symbols] [Countable M] in
private theorem realize_universalClosure {n : ℕ} (φ : ScopedFormula L n) :
    IL.Realize (universalClosure φ) Empty.elim (Fin.elim0 : Fin 0 → N) ↔
      ∀ b : Fin n → N, IL.Realize φ Empty.elim b := universalClosure_realize φ

private theorem sentenceAt_realize (α : Ordinal.{0}) (hα : α < ω₁) :
    Lemmatheca.MathematicalLogic.InfinitaryLogic.Sentence.Realize
      (sentenceAt (L := L) (M := M) α hα) N ↔
      comparison (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) ∧
        ∀ n (a : Fin n → M) (b : Fin n → N),
          comparison (L := L) α n a b → comparison (L := L) (α+1) n a b := by
  change IL.Realize _ Empty.elim Fin.elim0 ↔ _
  simp only [sentenceAt, realize_and, realize_indexedConj, realize_universalClosure,
    Lemmatheca.MathematicalLogic.InfinitaryLogic.Realize,
    comparisonFormula_realize, Sigma.forall]

/-- Maps coming from actual comparison-formula realization in the target structure. -/
noncomputable def sentenceSystem (α : Ordinal.{0}) (hα : α < ω₁)
    (hN : Lemmatheca.MathematicalLogic.InfinitaryLogic.Sentence.Realize (sentenceAt (L := L) (M := M) α hα) N) :
    BackAndForth.BackForthSystem L M N := by
  classical
  refine
  { maps := {p | ∃ (n : ℕ) (a : Fin n → M) (b : Fin n → N)
      (h : comparison (L := L) α n a b),
      p = tupleMap a b ((comparison_zero a b).mp (comparison_decreasing (show (0 : Ordinal) ≤ α from bot_le) h))}
    nonempty := ?_
    forth := ?_
    back := ?_ }
  · have h0 := (sentenceAt_realize α hα).mp hN |>.1
    exact ⟨_, 0, Fin.elim0, Fin.elim0, h0, rfl⟩
  · intro p hp c
    rcases hp with ⟨n,a,b,h,rfl⟩
    have hn := (comparison_successor α a b).mp (((sentenceAt_realize α hα).mp hN).2 n a b h)
    obtain ⟨d,hd⟩ := hn.2.1 c
    refine ⟨_, ⟨n+1,Fin.snoc a c,Fin.snoc b d,hd,rfl⟩,
      tupleMap_append a b c d _ _, ?_⟩
    exact ⟨Fin.last n, by simp⟩
  · intro p hp d
    rcases hp with ⟨n,a,b,h,rfl⟩
    have hn := (comparison_successor α a b).mp (((sentenceAt_realize α hα).mp hN).2 n a b h)
    obtain ⟨c,hc⟩ := hn.2.2 d
    refine ⟨_, ⟨n+1,Fin.snoc a c,Fin.snoc b d,hc,rfl⟩,
      tupleMap_append a b c d _ _, ⟨⟨c,⟨Fin.last n,by simp⟩⟩,?_⟩⟩
    simpa only [Fin.snoc_last] using
      tupleMap_coordinate (Fin.snoc a c) (Fin.snoc b d) _ (Fin.last n)

theorem sentenceAt_countable_isomorphism [Countable N]
    (α : Ordinal.{0}) (hα : α < ω₁)
    (hN : Lemmatheca.MathematicalLogic.InfinitaryLogic.Sentence.Realize (sentenceAt (L := L) (M := M) α hα) N) :
    Nonempty (M ≃[L] N) := by
  let S := sentenceSystem (L := L) (M := M) (N := N) α hα hN
  obtain ⟨p,hp⟩ := S.nonempty
  obtain ⟨e,_⟩ := BackAndForth.countable_isomorphism S p hp
  exact ⟨e⟩

noncomputable def stabilizingOrdinal : Ordinal.{0} :=
  Classical.choose (countable_stabilization (L := L) (M := M))

omit [Countable L.Symbols] in
theorem stabilizingOrdinal_spec :
    stabilizingOrdinal (L := L) (M := M) < ω₁ ∧
      Stabilizes (L := L) M (stabilizingOrdinal (L := L) (M := M)) := by
  exact Classical.choose_spec (countable_stabilization (L := L) (M := M))

noncomputable def scottSentence : IL.Sentence L :=
  sentenceAt (L := L) (M := M) (stabilizingOrdinal (L := L) (M := M))
    (stabilizingOrdinal_spec (L := L) (M := M)).1

theorem scottSentence_self : Lemmatheca.MathematicalLogic.InfinitaryLogic.Sentence.Realize (scottSentence (L := L) (M := M)) M := by
  exact sentenceAt_self _ (stabilizingOrdinal_spec (L := L) (M := M)).1
    (stabilizingOrdinal_spec (L := L) (M := M)).2

theorem scottSentence_characterization [Countable N] :
    Lemmatheca.MathematicalLogic.InfinitaryLogic.Sentence.Realize (scottSentence (L := L) (M := M)) N ↔ Nonempty (M ≃[L] N) := by
  constructor
  · exact sentenceAt_countable_isomorphism _ _
  · rintro ⟨e⟩
    exact (Lemmatheca.MathematicalLogic.InfinitaryLogic.sentence_isomorphism e
      (scottSentence (L := L) (M := M))).mp scottSentence_self

end ScottSentence
end Lemmatheca.ModelTheory.ScottSentences
