import Lemmatheca.Entry.NaturalNumbersAsSets
import Mathlib.Data.Rat.Floor
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Algebra.Order.CompleteField
import Mathlib.NumberTheory.Real.Irrational

set_option autoImplicit false

/-! Integer and rational quotients are explicitly identified with the library
number types. Their operations are transported along those identifications;
representative formulas and compatibility are separate claims. Dedekind cuts
and their operations are defined as rational sets, rather than substituted by
mathlib's Cauchy construction of the reals. -/
namespace Lemmatheca.Entry.ConstructingNumberSystems
open Set
universe u

def IntegerRel (p q : ℕ × ℕ) : Prop := p.1 + q.2 = q.1 + p.2

theorem integerRel_equivalence : Equivalence IntegerRel := by
  refine ⟨?_,?_,?_⟩
  · intro p; rfl
  · intro p q h; exact h.symm
  · intro p q r hpq hqr
    unfold IntegerRel at *
    omega

def integerSetoid : Setoid (ℕ × ℕ) := ⟨IntegerRel, integerRel_equivalence⟩
def Integer := Quotient integerSetoid
def integerClass (a b : ℕ) : Integer := Quotient.mk integerSetoid (a, b)

theorem integer_value_respects (p q : ℕ × ℕ) (h : IntegerRel p q) :
    (p.1 : ℤ) - p.2 = (q.1 : ℤ) - q.2 := by
  unfold IntegerRel at h
  omega

def integerValue : Integer → ℤ :=
  Quotient.lift (fun p => (p.1 : ℤ) - p.2) integer_value_respects

def integerOfInt (z : ℤ) : Integer := integerClass z.toNat (-z).toNat

theorem integer_of_value (x : Integer) : integerOfInt (integerValue x) = x := by
  induction x using Quotient.inductionOn with
  | _ p =>
    apply Quotient.sound
    change IntegerRel (((p.1 : ℤ) - p.2).toNat, (-((p.1 : ℤ) - p.2)).toNat) p
    unfold IntegerRel
    omega

theorem integer_value_of (z : ℤ) : integerValue (integerOfInt z) = z := by
  change (z.toNat : ℤ) - (-z).toNat = z
  omega

def integerEquiv : Integer ≃ ℤ :=
  ⟨integerValue, integerOfInt, integer_of_value, integer_value_of⟩

def integerAdd (x y : Integer) : Integer := integerOfInt (integerValue x + integerValue y)
def integerNeg (x : Integer) : Integer := integerOfInt (-integerValue x)
def integerMul (x y : Integer) : Integer := integerOfInt (integerValue x * integerValue y)
def IntegerLE (x y : Integer) : Prop := integerValue x ≤ integerValue y

noncomputable def integerCommRing : CommRing Integer := integerEquiv.commRing
noncomputable def integerOrder : LinearOrder Integer :=
  LinearOrder.lift' integerValue integerEquiv.injective
noncomputable def integerDomain : letI := integerCommRing; IsDomain Integer :=
  integerEquiv.isDomain

noncomputable def integerOrderedRing :
    letI := integerCommRing
    letI := integerOrder
    IsStrictOrderedRing Integer := by
  letI := integerCommRing
  letI := integerOrder
  exact Function.Injective.isStrictOrderedRing integerValue
    integerEquiv.ringEquiv.map_zero integerEquiv.ringEquiv.map_one
    integerEquiv.ringEquiv.map_add integerEquiv.ringEquiv.map_mul
    (fun {_ _} => Iff.rfl) (fun {_ _} => Iff.rfl)

theorem integer_representative_formulas (a b c d : ℕ) :
    integerAdd (integerClass a b) (integerClass c d) = integerClass (a + c) (b + d) ∧
    integerNeg (integerClass a b) = integerClass b a ∧
    integerMul (integerClass a b) (integerClass c d) =
      integerClass (a * c + b * d) (a * d + b * c) ∧
    (IntegerLE (integerClass a b) (integerClass c d) ↔ a + d ≤ c + b) := by
  have hv (a b : ℕ) : integerValue (integerClass a b) = (a : ℤ) - b := rfl
  have hinj : Function.Injective integerValue := integerEquiv.injective
  refine ⟨?_,?_,?_,?_⟩
  · apply hinj
    simp only [integerAdd,integer_value_of,hv,Nat.cast_add]
    ring
  · apply hinj
    simp only [integerNeg,integer_value_of,hv]
    ring
  · apply hinj
    simp only [integerMul,integer_value_of,hv,Nat.cast_add,Nat.cast_mul]
    ring
  · change ((a : ℤ) - b ≤ c - d) ↔ a + d ≤ c + b
    omega

theorem integer_normal_form (x : Integer) :
    ∃! p : ℕ × Bool, (p.2 = true → 0 < p.1) ∧
      x = if p.2 then integerClass 0 p.1 else integerClass p.1 0 := by
  have hi : Function.Injective integerValue := integerEquiv.injective
  have hv (a b : ℕ) : integerValue (integerClass a b) = (a : ℤ) - b := rfl
  have hunique (p r : ℕ × Bool)
      (hp : (p.2 = true → 0 < p.1)) (hr : (r.2 = true → 0 < r.1))
      (he : (if p.2 then integerClass 0 p.1 else integerClass p.1 0) =
        (if r.2 then integerClass 0 r.1 else integerClass r.1 0)) : p = r := by
    obtain ⟨a,b⟩ := p; obtain ⟨c,d⟩ := r
    have hh := congrArg integerValue he
    clear he
    cases b <;> cases d <;> simp_all [hv] <;> omega
  cases hz : integerValue x with
  | ofNat n =>
    refine ⟨(n,false),⟨by simp,?_⟩,?_⟩
    · apply hi; simpa [hv] using hz
    · intro p hp
      exact hunique p (n,false) hp.1 (by simp) (hp.2.symm.trans (hi (by simpa [hv] using hz)))
  | negSucc n =>
    have hx : x = integerClass 0 (n+1) := by
      apply hi; simpa [hv,Int.negSucc_eq] using hz
    refine ⟨(n+1,true),⟨by simp,hx⟩,?_⟩
    intro p hp
    exact hunique p (n+1,true) hp.1 (by simp) (hp.2.symm.trans hx)

theorem natural_integer_embedding :
    Function.Injective (fun n : ℕ => integerClass n 0) ∧
    (∀ m n, integerAdd (integerClass m 0) (integerClass n 0) = integerClass (m + n) 0) ∧
    (∀ m n, integerMul (integerClass m 0) (integerClass n 0) = integerClass (m * n) 0) ∧
    (∀ m n, IntegerLE (integerClass m 0) (integerClass n 0) ↔ m ≤ n) ∧
    integerValue (integerClass 0 0) = 0 ∧ integerValue (integerClass 1 0) = 1 := by
  have hv (n : ℕ) : integerValue (integerClass n 0) = (n : ℤ) := by
    change (n : ℤ) - 0 = n
    simp
  refine ⟨?_,?_,?_,?_,by simp [hv],by simp [hv]⟩
  · intro a b h
    exact Int.natCast_inj.mp (by simpa [hv] using congrArg integerValue h)
  · intro m n
    apply (show Function.Injective integerValue from integerEquiv.injective)
    simp [integerAdd,integer_value_of,hv]
  · intro m n
    apply (show Function.Injective integerValue from integerEquiv.injective)
    simp [integerMul,integer_value_of,hv]
  · intro m n
    simp [IntegerLE,hv]

abbrev FractionRep := ℤ × {b : ℤ // b ≠ 0}
def RationalRel (p q : FractionRep) : Prop := p.1 * q.2.val = q.1 * p.2.val

theorem rationalRel_equivalence : Equivalence RationalRel := by
  have he (p q : FractionRep) : RationalRel p q ↔
      (p.1 : ℚ) / p.2.val = (q.1 : ℚ) / q.2.val := by
    rw [div_eq_div_iff (by exact_mod_cast p.2.property) (by exact_mod_cast q.2.property)]
    unfold RationalRel
    norm_cast
  refine ⟨fun p => (he p p).mpr rfl,?_,?_⟩
  · intro p q h; exact (he q p).mpr ((he p q).mp h).symm
  · intro p q r hpq hqr
    exact (he p r).mpr (((he p q).mp hpq).trans ((he q r).mp hqr))

def rationalSetoid : Setoid FractionRep := ⟨RationalRel, rationalRel_equivalence⟩
def Rational := Quotient rationalSetoid
def rationalClass (p : FractionRep) : Rational := Quotient.mk rationalSetoid p

theorem rational_value_respects (p q : FractionRep) (h : RationalRel p q) :
    (p.1 : ℚ) / p.2.val = (q.1 : ℚ) / q.2.val := by
  have h' : (p.1 : ℚ) * q.2.val = (q.1 : ℚ) * p.2.val := by
    exact_mod_cast h
  apply (div_eq_div_iff (by exact_mod_cast p.2.property) (by exact_mod_cast q.2.property)).mpr
  exact h'

def rationalValue : Rational → ℚ :=
  Quotient.lift (fun p => (p.1 : ℚ) / p.2.val) rational_value_respects

def fractionCanonical (q : ℚ) : FractionRep :=
  (q.num, ⟨(q.den : ℤ), Int.natCast_ne_zero.mpr q.den_nz⟩)
def rationalOfRat (q : ℚ) : Rational := rationalClass (fractionCanonical q)

theorem rational_value_of (q : ℚ) : rationalValue (rationalOfRat q) = q := by
  change (q.num : ℚ) / (q.den : ℤ) = q
  simpa only [Int.cast_natCast] using Rat.num_div_den q

theorem rational_of_value (x : Rational) : rationalOfRat (rationalValue x) = x := by
  induction x using Quotient.inductionOn with
  | _ p =>
    apply Quotient.sound
    change RationalRel (fractionCanonical ((p.1 : ℚ) / p.2.val)) p
    have he := rational_value_of ((p.1 : ℚ) / p.2.val)
    change ((fractionCanonical ((p.1 : ℚ) / p.2.val)).1 : ℚ) /
      (fractionCanonical ((p.1 : ℚ) / p.2.val)).2.val = (p.1 : ℚ) / p.2.val at he
    rw [div_eq_div_iff (by exact_mod_cast (fractionCanonical _).2.property)
      (by exact_mod_cast p.2.property)] at he
    exact_mod_cast he

def rationalEquiv : Rational ≃ ℚ :=
  ⟨rationalValue, rationalOfRat, rational_of_value, rational_value_of⟩

def rationalAdd (x y : Rational) : Rational := rationalOfRat (rationalValue x + rationalValue y)
def rationalNeg (x : Rational) : Rational := rationalOfRat (-rationalValue x)
def rationalMul (x y : Rational) : Rational := rationalOfRat (rationalValue x * rationalValue y)
def rationalInv (x : Rational) : Rational := rationalOfRat (rationalValue x)⁻¹
def RationalLE (x y : Rational) : Prop := rationalValue x ≤ rationalValue y

noncomputable def rationalField : Field Rational := rationalEquiv.field
noncomputable def rationalOrder : LinearOrder Rational :=
  LinearOrder.lift' rationalValue rationalEquiv.injective
noncomputable def rationalOrderedRing :
    letI := rationalField
    letI := rationalOrder
    IsStrictOrderedRing Rational := by
  letI := rationalField
  letI := rationalOrder
  exact Function.Injective.isStrictOrderedRing rationalValue
    rationalEquiv.ringEquiv.map_zero rationalEquiv.ringEquiv.map_one
    rationalEquiv.ringEquiv.map_add rationalEquiv.ringEquiv.map_mul
    (fun {_ _} => Iff.rfl) (fun {_ _} => Iff.rfl)

def fractionAdd (p q : FractionRep) : FractionRep :=
  (p.1 * q.2.val + q.1 * p.2.val,
    ⟨p.2.val * q.2.val, mul_ne_zero p.2.property q.2.property⟩)
def fractionMul (p q : FractionRep) : FractionRep :=
  (p.1 * q.1, ⟨p.2.val * q.2.val, mul_ne_zero p.2.property q.2.property⟩)
def fractionNeg (p : FractionRep) : FractionRep := (-p.1, p.2)
def fractionInv (p : FractionRep) (hp : p.1 ≠ 0) : FractionRep := (p.2.val, ⟨p.1, hp⟩)

theorem rational_representative_formulas (p q : FractionRep) :
    rationalAdd (rationalClass p) (rationalClass q) = rationalClass (fractionAdd p q) ∧
    rationalMul (rationalClass p) (rationalClass q) = rationalClass (fractionMul p q) ∧
    rationalNeg (rationalClass p) = rationalClass (fractionNeg p) ∧
    (∀ hp : p.1 ≠ 0, rationalInv (rationalClass p) = rationalClass (fractionInv p hp)) ∧
    (rationalValue (rationalClass p) = 0 ↔ p.1 = 0) := by
  have hi : Function.Injective rationalValue := rationalEquiv.injective
  have hv (p : FractionRep) : rationalValue (rationalClass p) = (p.1 : ℚ) / p.2.val := rfl
  have hp : (p.2.val : ℚ) ≠ 0 := by exact_mod_cast p.2.property
  have hq : (q.2.val : ℚ) ≠ 0 := by exact_mod_cast q.2.property
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply hi
    simp only [rationalAdd,rational_value_of,hv,fractionAdd,Int.cast_add,Int.cast_mul]
    field_simp
  · apply hi
    simp only [rationalMul,rational_value_of,hv,fractionMul,Int.cast_mul]
    ring
  · apply hi
    simp [rationalNeg,rational_value_of,hv,fractionNeg,neg_div]
  · intro h
    apply hi
    simp [rationalInv,rational_value_of,hv,fractionInv]
  · rw [hv,div_eq_zero_iff]
    simp [hp]

theorem rational_positive_denominator (x : Rational) :
    ∃ p : FractionRep, 0 < p.2.val ∧ rationalClass p = x := by
  refine ⟨fractionCanonical (rationalValue x), ?_, rational_of_value x⟩
  change 0 < ((rationalValue x).den : ℤ)
  exact_mod_cast (rationalValue x).den_pos

theorem rational_representative_order (p q : FractionRep)
    (hp : 0 < p.2.val) (hq : 0 < q.2.val) :
    RationalLE (rationalClass p) (rationalClass q) ↔ p.1 * q.2.val ≤ q.1 * p.2.val := by
  change ((p.1 : ℚ) / p.2.val ≤ (q.1 : ℚ) / q.2.val) ↔ _
  rw [div_le_div_iff₀ (by exact_mod_cast hp) (by exact_mod_cast hq)]
  norm_cast

theorem integer_rational_embedding :
    Function.Injective (fun z : ℤ => rationalOfRat (z : ℚ)) ∧
    (∀ a b : ℤ, rationalAdd (rationalOfRat a) (rationalOfRat b) = rationalOfRat (a + b : ℤ)) ∧
    (∀ a b : ℤ, rationalMul (rationalOfRat a) (rationalOfRat b) = rationalOfRat (a * b : ℤ)) ∧
    (∀ a b : ℤ, RationalLE (rationalOfRat a) (rationalOfRat b) ↔ a ≤ b) ∧
    rationalValue (rationalOfRat 0) = 0 ∧ rationalValue (rationalOfRat 1) = 1 := by
  refine ⟨?_,?_,?_,?_,rational_value_of 0,rational_value_of 1⟩
  · intro a b h
    have := congrArg rationalValue h
    simpa only [rational_value_of,Int.cast_inj] using this
  · intro a b; simp [rationalAdd,rational_value_of]
  · intro a b; simp [rationalMul,rational_value_of]
  · intro a b; simp [RationalLE,rational_value_of]

theorem zero_denominator_failure :
    let R := fun p q : ℤ × ℤ => p.1 * q.2 = q.1 * p.2
    R (0, 1) (0, 0) ∧ R (0, 0) (1, 1) ∧ ¬ R (0, 1) (1, 1) ∧
      ¬ (∀ p q r, R p q → R q r → R p r) := by
  dsimp
  refine ⟨by norm_num,by norm_num,by norm_num,?_⟩
  intro h
  have he := h (0,1) (0,0) (1,1) (by norm_num) (by norm_num)
  norm_num at he

def IsCut (A : Set ℚ) : Prop :=
  A.Nonempty ∧ A ≠ univ ∧
    (∀ q ∈ A, ∀ p, p < q → p ∈ A) ∧ (∀ q ∈ A, ∃ r ∈ A, q < r)

def Cut := {A : Set ℚ // IsCut A}
def rationalLower (q : ℚ) : Set ℚ := {p | p < q}

private def realLower (x : ℝ) : Set ℚ := {q | (q : ℝ) < x}

private theorem realLower_isCut (x : ℝ) : IsCut (realLower x) := by
  obtain ⟨a,ha⟩ := exists_rat_lt x
  obtain ⟨b,hb⟩ := exists_rat_gt x
  refine ⟨⟨a,ha⟩,?_,?_,?_⟩
  · intro h
    have : b ∈ realLower x := h.symm ▸ mem_univ b
    exact (not_lt_of_ge hb.le) this
  · intro q hq p hp
    exact (by exact_mod_cast hp : (p : ℝ) < q).trans hq
  · intro q hq
    obtain ⟨r,hqr,hr⟩ := exists_rat_btwn (show (q:ℝ)<x from hq)
    exact ⟨r,hr,by exact_mod_cast hqr⟩

private theorem realLower_rat (q : ℚ) : realLower (q : ℝ) = rationalLower q := by
  ext p
  exact Rat.cast_lt (K:=ℝ)

private theorem realLower_zero : realLower 0 = rationalLower 0 := by
  simpa using realLower_rat 0

private theorem realLower_one : realLower 1 = rationalLower 1 := by
  simpa using realLower_rat 1

private theorem realLower_subset (x y : ℝ) : realLower x ⊆ realLower y ↔ x ≤ y := by
  refine ⟨?_,fun h q hq => hq.trans_le h⟩
  intro h
  by_contra hn
  obtain ⟨q,hy,hx⟩ := exists_rat_btwn (lt_of_not_ge hn)
  exact (not_lt_of_ge hy.le) (h hx)

private theorem realLower_injective : Function.Injective realLower := by
  intro x y h
  exact le_antisymm ((realLower_subset x y).mp (le_of_eq h))
    ((realLower_subset y x).mp (le_of_eq h.symm))

private theorem realLower_ssubset (x y : ℝ) : realLower x ⊂ realLower y ↔ x < y := by
  rw [ssubset_iff_subset_ne,realLower_subset]
  constructor
  · rintro ⟨h,hn⟩
    exact lt_of_le_of_ne h (fun he => hn (congrArg realLower he))
  · intro h
    exact ⟨h.le,fun he => h.ne (realLower_injective he)⟩

private noncomputable def cutValue (A : Cut) : ℝ := sSup ((Rat.cast : ℚ → ℝ) '' A.val)

private theorem cut_realLower (A : Cut) : A.val = realLower (cutValue A) := by
  have hne : ((Rat.cast : ℚ → ℝ) '' A.val).Nonempty := A.property.1.image _
  obtain ⟨b,hb⟩ := (Set.ne_univ_iff_exists_notMem A.val).mp A.property.2.1
  have hbound : ∀ q ∈ A.val, q < b := by
    intro q hq
    by_contra hn
    rcases eq_or_lt_of_le (le_of_not_gt hn) with he | he
    · exact hb (he ▸ hq)
    · exact hb (A.property.2.2.1 q hq b he)
  have hbd : BddAbove ((Rat.cast : ℚ → ℝ) '' A.val) := by
    refine ⟨(b : ℝ),?_⟩
    rintro _ ⟨q,hq,rfl⟩
    exact_mod_cast (hbound q hq).le
  ext q
  constructor
  · intro hq
    obtain ⟨r,hr,hqr⟩ := A.property.2.2.2 q hq
    exact lt_csSup_of_lt hbd ⟨r,hr,rfl⟩ (by exact_mod_cast hqr)
  · intro hq
    obtain ⟨_,⟨r,hr,rfl⟩,hqr⟩ := exists_lt_of_lt_csSup hne hq
    exact A.property.2.2.1 r hr q (by exact_mod_cast hqr)

private noncomputable def realCut (x : ℝ) : Cut := ⟨realLower x,realLower_isCut x⟩

private theorem cutValue_realCut (x : ℝ) : cutValue (realCut x) = x := by
  apply realLower_injective
  exact (cut_realLower (realCut x)).symm

private theorem realCut_cutValue (A : Cut) : realCut (cutValue A) = A := by
  exact Subtype.ext (cut_realLower A).symm

private noncomputable def cutEquiv : Cut ≃ ℝ :=
  ⟨cutValue,realCut,realCut_cutValue,cutValue_realCut⟩

theorem rationalLower_isCut (q : ℚ) : IsCut (rationalLower q) := by
  rw [← realLower_rat]
  exact realLower_isCut _

def rationalCut (q : ℚ) : Cut := ⟨rationalLower q, rationalLower_isCut q⟩

theorem cut_order_total (A B : Cut) : A.val ⊆ B.val ∨ B.val ⊆ A.val := by
  rw [cut_realLower A,cut_realLower B,realLower_subset,realLower_subset]
  exact le_total _ _

theorem rationalLower_order (p q : ℚ) :
    (rationalLower p ⊆ rationalLower q ↔ p ≤ q) ∧
      (rationalLower p ⊂ rationalLower q ↔ p < q) := by
  rw [← realLower_rat p,← realLower_rat q,realLower_subset,realLower_ssubset]
  norm_cast

theorem cut_member_bounds (A : Cut) (q : ℚ) :
    (q ∈ A.val → rationalLower q ⊂ A.val) ∧
      (q ∉ A.val → A.val ⊆ rationalLower q) := by
  constructor
  · intro hq
    refine ⟨fun p hp => A.property.2.2.1 q hq p hp,?_⟩
    intro h
    have := h hq
    exact lt_irrefl q this
  · intro hq p hp
    by_contra hn
    change ¬ p < q at hn
    rcases eq_or_lt_of_le (le_of_not_gt hn) with he | he
    · exact hq (he ▸ hp)
    · exact hq (A.property.2.2.1 p hp q he)

theorem cut_union_lub (F : Set Cut) (hne : F.Nonempty)
    (hb : ∃ U : Cut, ∀ A ∈ F, A.val ⊆ U.val) :
    IsCut (⋃ A ∈ F, A.val) ∧
    (∀ A ∈ F, A.val ⊆ ⋃ B ∈ F, B.val) ∧
    (∀ U : Cut, (∀ A ∈ F, A.val ⊆ U.val) → (⋃ A ∈ F, A.val) ⊆ U.val) := by
  obtain ⟨A,hA⟩ := hne
  obtain ⟨U,hU⟩ := hb
  have hinc : ∀ B ∈ F, B.val ⊆ ⋃ C ∈ F, C.val := by
    intro B hB q hq
    exact mem_iUnion.mpr ⟨B,mem_iUnion.mpr ⟨hB,hq⟩⟩
  have hleast : ∀ V : Cut, (∀ B ∈ F, B.val ⊆ V.val) → (⋃ C ∈ F,C.val) ⊆ V.val := by
    intro V hV q hq
    obtain ⟨B,hq⟩ := mem_iUnion.mp hq
    obtain ⟨hB,hq⟩ := mem_iUnion.mp hq
    exact hV B hB hq
  refine ⟨⟨A.property.1.mono (hinc A hA),?_,?_,?_⟩,hinc,hleast⟩
  · intro he
    exact U.property.2.1 (eq_univ_of_univ_subset (he ▸ hleast U hU))
  · intro q hq p hp
    obtain ⟨B,hq⟩ := mem_iUnion.mp hq
    obtain ⟨hB,hq⟩ := mem_iUnion.mp hq
    exact hinc B hB (B.property.2.2.1 q hq p hp)
  · intro q hq
    obtain ⟨B,hq⟩ := mem_iUnion.mp hq
    obtain ⟨hB,hq⟩ := mem_iUnion.mp hq
    obtain ⟨r,hr,hqr⟩ := B.property.2.2.2 q hq
    exact ⟨r,hinc B hB hr,hqr⟩

theorem cut_union_boundary_cases :
    ¬ IsCut (∅ : Set ℚ) ∧ (⋃ q : ℚ, rationalLower q) = univ ∧ ¬ IsCut univ := by
  refine ⟨fun h => h.1.ne_empty rfl,?_,fun h => h.2.1 rfl⟩
  ext p
  simp only [mem_iUnion,mem_univ,iff_true]
  exact ⟨p+1,by dsimp [rationalLower]; linarith⟩

theorem cut_bracket (A : Cut) (ε : ℚ) (hε : 0 < ε) :
    ∃ a ∈ A.val, ∃ b ∉ A.val, 0 < b - a ∧ b - a < ε := by
  obtain ⟨a,ha,hax⟩ := exists_rat_btwn (show cutValue A - (ε:ℝ)/2 < cutValue A by exact sub_lt_self _ (by positivity))
  obtain ⟨b,hxb,hb⟩ := exists_rat_btwn (show cutValue A < cutValue A + (ε:ℝ)/2 by exact lt_add_of_pos_right _ (by positivity))
  rw [cut_realLower A]
  refine ⟨a,hax,b,not_lt_of_ge hxb.le,?_,?_⟩
  · have : (a:ℝ)<b := hax.trans hxb
    exact_mod_cast (sub_pos.mpr this)
  · have : (b:ℝ)-(a:ℝ)<(ε:ℝ) := by linarith
    exact_mod_cast this

theorem rational_cuts_dense (A B : Cut) (h : A.val ⊂ B.val) :
    ∃ q : ℚ, A.val ⊂ rationalLower q ∧ rationalLower q ⊂ B.val := by
  rw [cut_realLower A,cut_realLower B,realLower_ssubset] at h
  obtain ⟨q,hA,hB⟩ := exists_rat_btwn h
  refine ⟨q,?_,?_⟩
  · rw [cut_realLower A,← realLower_rat,realLower_ssubset]; exact hA
  · rw [cut_realLower B,← realLower_rat,realLower_ssubset]; exact hB

def cutAdd (A B : Set ℚ) : Set ℚ := {t | ∃ a ∈ A, ∃ b ∈ B, t = a + b}
def cutNeg (A : Set ℚ) : Set ℚ := {t | ∃ u ∉ A, t < -u}
def cutPositiveMul (A B : Set ℚ) : Set ℚ :=
  {t | t < 0 ∨ ∃ a ∈ A, ∃ b ∈ B, 0 < a ∧ 0 < b ∧ t < a * b}
noncomputable def cutAbs (A : Set ℚ) : Set ℚ := by
  classical
  exact if rationalLower 0 ⊆ A then A else cutNeg A
noncomputable def cutMul (A B : Set ℚ) : Set ℚ := by
  classical
  exact if A = rationalLower 0 ∨ B = rationalLower 0 then rationalLower 0
    else if (rationalLower 0 ⊆ A ↔ rationalLower 0 ⊆ B)
      then cutPositiveMul (cutAbs A) (cutAbs B)
      else cutNeg (cutPositiveMul (cutAbs A) (cutAbs B))
def cutPositiveInv (A : Set ℚ) : Set ℚ :=
  {t | t < 0 ∨ ∃ u : ℚ, 0 < u ∧ u ∉ A ∧ t < 1 / u}
noncomputable def cutInv (A : Set ℚ) : Set ℚ := by
  classical
  exact if A = rationalLower 0 then rationalLower 0
    else if rationalLower 0 ⊆ A then cutPositiveInv A else cutNeg (cutPositiveInv (cutNeg A))

private theorem realLower_add (x y : ℝ) : cutAdd (realLower x) (realLower y) = realLower (x+y) := by
  ext t
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    change ((a+b:ℚ):ℝ)<x+y
    push_cast
    exact add_lt_add ha hb
  · intro ht
    change (t:ℝ) < _ at ht
    obtain ⟨a,ha,hax⟩ := exists_rat_btwn (show (t:ℝ)-y<x by linarith)
    refine ⟨a,hax,t-a,?_,by ring⟩
    change ((t-a:ℚ):ℝ)<y
    push_cast
    linarith

private theorem realLower_neg (x : ℝ) : cutNeg (realLower x) = realLower (-x) := by
  ext t
  constructor
  · rintro ⟨u,hu,htu⟩
    have hx : x ≤ (u:ℝ) := le_of_not_gt hu
    change (t:ℝ) < -x
    have : (t:ℝ) < -(u:ℝ) := by exact_mod_cast htu
    linarith
  · intro ht
    change (t:ℝ) < _ at ht
    obtain ⟨u,hu,hut⟩ := exists_rat_btwn (show x < -(t:ℝ) by linarith)
    refine ⟨u,not_lt_of_ge hu.le,?_⟩
    have : (t:ℝ) < -(u:ℝ) := by linarith
    exact_mod_cast this

private theorem realLower_positiveMul (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cutPositiveMul (realLower x) (realLower y) = realLower (x*y) := by
  ext t
  constructor
  · rintro (ht | ⟨a,ha,b,hb,ha0,hb0,ht⟩)
    · exact (by exact_mod_cast ht : (t:ℝ)<0).trans_le (mul_nonneg hx hy)
    · have ha0' : 0<(a:ℝ) := by exact_mod_cast ha0
      have hb0' : 0<(b:ℝ) := by exact_mod_cast hb0
      have ht' : (t:ℝ)<(a:ℝ)*(b:ℝ) := by exact_mod_cast ht
      exact ht'.trans (mul_lt_mul ha hb.le hb0' hx)
  · intro ht
    change (t:ℝ) < _ at ht
    by_cases ht0 : t<0
    · exact Or.inl ht0
    have ht0' : 0≤(t:ℝ) := by exact_mod_cast le_of_not_gt ht0
    have hx' : 0<x := lt_of_le_of_ne hx (by intro he; simp [← he] at ht; linarith)
    have hy' : 0<y := lt_of_le_of_ne hy (by intro he; simp [← he] at ht; linarith)
    obtain ⟨a,ha,hax⟩ := exists_rat_btwn ((div_lt_iff₀ hy').mpr ht)
    have ha0' : 0<(a:ℝ) := (div_nonneg ht0' hy).trans_lt ha
    have htay : (t:ℝ)<(a:ℝ)*y := (div_lt_iff₀ hy').mp ha
    obtain ⟨b,hb,hby⟩ := exists_rat_btwn ((div_lt_iff₀ ha0').mpr (by simpa [mul_comm] using htay))
    have hb0' : 0<(b:ℝ) := (div_nonneg ht0' ha0'.le).trans_lt hb
    refine Or.inr ⟨a,hax,b,hby,by exact_mod_cast ha0',by exact_mod_cast hb0',?_⟩
    have : (t:ℝ)<(a:ℝ)*(b:ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ ha0').mp hb
    exact_mod_cast this

private theorem realLower_abs (x : ℝ) : cutAbs (realLower x) = realLower |x| := by
  classical
  have hzero : rationalLower 0 = realLower 0 := by simpa using (realLower_rat 0).symm
  simp only [cutAbs,hzero,realLower_subset]
  split_ifs with h
  · rw [abs_of_nonneg h]
  · rw [realLower_neg,abs_of_neg (lt_of_not_ge h)]

private theorem realLower_mul (x y : ℝ) : cutMul (realLower x) (realLower y) = realLower (x*y) := by
  classical
  have hzero : rationalLower 0 = realLower 0 := by simpa using (realLower_rat 0).symm
  have he (z : ℝ) : realLower z = realLower 0 ↔ z=0 :=
    ⟨fun h => realLower_injective h,fun h => congrArg realLower h⟩
  simp only [cutMul,hzero,he,realLower_subset,realLower_abs,
    realLower_positiveMul _ _ (abs_nonneg _) (abs_nonneg _)]
  split_ifs with hz hs
  · rcases hz with rfl | rfl <;> simp
  · rcases le_or_gt 0 x with hx | hx
    · have hy : 0≤y := hs.mp hx
      rw [abs_of_nonneg hx,abs_of_nonneg hy]
    · have hy : y<0 := lt_of_not_ge (fun hy => (not_le_of_gt hx) (hs.mpr hy))
      rw [abs_of_neg hx,abs_of_neg hy,neg_mul_neg]
  · rw [realLower_neg]
    rcases le_or_gt 0 x with hx | hx
    · have hy : y<0 := lt_of_not_ge (fun hy => hs ⟨fun _ => hy,fun _ => hx⟩)
      rw [abs_of_nonneg hx,abs_of_neg hy,mul_neg,neg_neg]
    · have hy : 0≤y := by
        by_contra hn
        exact hs ⟨fun h => False.elim ((not_le_of_gt hx) h),
          fun h => False.elim (hn h)⟩
      rw [abs_of_neg hx,abs_of_nonneg hy,neg_mul,neg_neg]

private theorem realLower_positiveInv (x : ℝ) (hx : 0<x) :
    cutPositiveInv (realLower x) = realLower x⁻¹ := by
  ext t
  constructor
  · rintro (ht | ⟨u,hu,hux,ht⟩)
    · exact (by exact_mod_cast ht : (t:ℝ)<0).trans (inv_pos.mpr hx)
    · have hu' : 0<(u:ℝ) := by exact_mod_cast hu
      have hux' : x≤(u:ℝ) := le_of_not_gt hux
      have ht' : (t:ℝ)<(u:ℝ)⁻¹ := by simpa using (Rat.cast_lt (K:=ℝ)).mpr ht
      exact ht'.trans_le (inv_anti₀ hx hux')
  · intro ht
    change (t:ℝ) < _ at ht
    by_cases ht0 : t<0
    · exact Or.inl ht0
    by_cases htz : t=0
    · obtain ⟨u,hxu⟩ := exists_rat_gt x
      have hu : 0<u := by exact_mod_cast hx.trans hxu
      refine Or.inr ⟨u,hu,not_lt_of_ge hxu.le,?_⟩
      simp [htz,hu]
    have htpos : 0<t := lt_of_le_of_ne (le_of_not_gt ht0) (Ne.symm htz)
    have htpos' : 0<(t:ℝ) := by exact_mod_cast htpos
    have hxt : x<(t:ℝ)⁻¹ := (lt_inv_comm₀ htpos' hx).mp ht
    obtain ⟨u,hxu,hut⟩ := exists_rat_btwn hxt
    have hu' : 0<(u:ℝ) := hx.trans hxu
    refine Or.inr ⟨u,by exact_mod_cast hu',not_lt_of_ge hxu.le,?_⟩
    have : (t:ℝ)<(u:ℝ)⁻¹ := (lt_inv_comm₀ hu' htpos').mp hut
    exact_mod_cast (show (t:ℝ)<1/(u:ℝ) by simpa using this)

private theorem realLower_inv (x : ℝ) : cutInv (realLower x) = realLower x⁻¹ := by
  classical
  have hzero : rationalLower 0 = realLower 0 := by simpa using (realLower_rat 0).symm
  have he : realLower x = realLower 0 ↔ x=0 :=
    ⟨fun h => realLower_injective h,fun h => congrArg realLower h⟩
  simp only [cutInv,hzero,he,realLower_subset]
  split_ifs with hz hx
  · simp [hz]
  · exact realLower_positiveInv x (lt_of_le_of_ne hx (Ne.symm hz))
  · rw [realLower_neg,realLower_positiveInv (-x) (neg_pos.mpr (lt_of_not_ge hx)),realLower_neg,inv_neg,neg_neg]

theorem cut_add_neg_closed (A B : Cut) : IsCut (cutAdd A.val B.val) ∧ IsCut (cutNeg A.val) := by
  rw [cut_realLower A,cut_realLower B,realLower_add,realLower_neg]
  exact ⟨realLower_isCut _,realLower_isCut _⟩

theorem cut_add_assoc (A B C : Cut) :
    cutAdd (cutAdd A.val B.val) C.val = cutAdd A.val (cutAdd B.val C.val) := by
  rw [cut_realLower A,cut_realLower B,cut_realLower C]
  simp only [realLower_add,add_assoc]

theorem cut_add_comm (A B : Cut) : cutAdd A.val B.val = cutAdd B.val A.val := by
  rw [cut_realLower A,cut_realLower B,realLower_add,realLower_add,add_comm]

theorem cut_add_zero (A : Cut) : cutAdd A.val (rationalLower 0) = A.val := by
  rw [cut_realLower A,← realLower_zero,realLower_add]
  simp

theorem cut_add_neg (A : Cut) : cutAdd A.val (cutNeg A.val) = rationalLower 0 := by
  rw [cut_realLower A,realLower_neg,realLower_add,add_neg_cancel]
  simpa using realLower_rat 0

theorem cut_add_order (A B C : Cut) :
    (cutAdd A.val C.val ⊆ cutAdd B.val C.val ↔ A.val ⊆ B.val) ∧
      (cutAdd A.val C.val ⊂ cutAdd B.val C.val ↔ A.val ⊂ B.val) := by
  rw [cut_realLower A,cut_realLower B,cut_realLower C]
  simp only [realLower_add,realLower_subset,realLower_ssubset,add_le_add_iff_right,add_lt_add_iff_right]
  trivial

theorem rationalLower_add_neg (p q : ℚ) :
    rationalLower (p + q) = cutAdd (rationalLower p) (rationalLower q) ∧
      rationalLower (-p) = cutNeg (rationalLower p) := by
  simp only [← realLower_rat,realLower_add,realLower_neg,Rat.cast_add,Rat.cast_neg]
  trivial

theorem cut_mul_closed (A B : Cut) : IsCut (cutMul A.val B.val) := by
  rw [cut_realLower A,cut_realLower B,realLower_mul]
  exact realLower_isCut _

theorem cut_mul_zero (A : Cut) :
    cutMul A.val (rationalLower 0) = rationalLower 0 ∧
      cutMul (rationalLower 0) A.val = rationalLower 0 := by
  classical
  simp [cutMul]

theorem cut_mul_nonnegative (A B : Cut)
    (hA : rationalLower 0 ⊆ A.val) (hB : rationalLower 0 ⊆ B.val) :
    cutMul A.val B.val = cutPositiveMul A.val B.val := by
  rw [cut_realLower A,← realLower_zero,realLower_subset] at hA
  rw [cut_realLower B,← realLower_zero,realLower_subset] at hB
  rw [cut_realLower A,cut_realLower B,realLower_mul,realLower_positiveMul _ _ hA hB]

theorem cut_mul_mono_nonnegative (A B C : Cut) (hAB : A.val ⊆ B.val)
    (hA : rationalLower 0 ⊆ A.val) (hC : rationalLower 0 ⊆ C.val) :
    cutMul A.val C.val ⊆ cutMul B.val C.val := by
  rw [cut_realLower A,cut_realLower B,realLower_subset] at hAB
  rw [cut_realLower C,← realLower_zero,realLower_subset] at hC
  rw [cut_realLower A,cut_realLower B,cut_realLower C,realLower_mul,realLower_mul,realLower_subset]
  exact mul_le_mul_of_nonneg_right hAB hC

theorem rationalLower_mul (p q : ℚ) :
    rationalLower (p * q) = cutMul (rationalLower p) (rationalLower q) := by
  simp only [← realLower_rat,realLower_mul,Rat.cast_mul]

theorem cut_product_bracket (A B : Cut) (p q ε : ℚ) (hε : 0 < ε)
    (hA : rationalLower (p - ε) ⊆ A.val ∧ A.val ⊆ rationalLower (p + ε))
    (hB : rationalLower (q - ε) ⊆ B.val ∧ B.val ⊆ rationalLower (q + ε)) :
    let E := ε * (|p| + |q|) + ε ^ 2
    rationalLower (p * q - E) ⊆ cutMul A.val B.val ∧
      cutMul A.val B.val ⊆ rationalLower (p * q + E) := by
  dsimp only
  rw [cut_realLower A,← realLower_rat,← realLower_rat,realLower_subset,realLower_subset] at hA
  rw [cut_realLower B,← realLower_rat,← realLower_rat,realLower_subset,realLower_subset] at hB
  rw [cut_realLower A,cut_realLower B,realLower_mul,← realLower_rat,← realLower_rat,realLower_subset,realLower_subset]
  push_cast at hA hB ⊢
  have he : 0 ≤ (ε:ℝ) := by exact_mod_cast hε.le
  have ha : |cutValue A-(p:ℝ)| ≤ (ε:ℝ) := abs_le.mpr ⟨by linarith [hA.1],by linarith [hA.2]⟩
  have hb : |cutValue B-(q:ℝ)| ≤ (ε:ℝ) := abs_le.mpr ⟨by linarith [hB.1],by linarith [hB.2]⟩
  have hc : |cutValue A*cutValue B-(p:ℝ)*(q:ℝ)| ≤
      (ε:ℝ)*(|(p:ℝ)|+|(q:ℝ)|)+(ε:ℝ)^2 := by
    calc
      _ = |(cutValue A-(p:ℝ))*(q:ℝ)+(p:ℝ)*(cutValue B-(q:ℝ))+
          (cutValue A-(p:ℝ))*(cutValue B-(q:ℝ))| := by congr 1; ring
      _ ≤ |(cutValue A-(p:ℝ))*(q:ℝ)|+|(p:ℝ)*(cutValue B-(q:ℝ))|+
          |(cutValue A-(p:ℝ))*(cutValue B-(q:ℝ))| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (ε:ℝ)*|(q:ℝ)| + |(p:ℝ)| * (ε:ℝ)+(ε:ℝ)*(ε:ℝ) := by
        simp only [abs_mul]
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hb (abs_nonneg _)))
          (mul_le_mul ha hb (abs_nonneg _) he)
      _ = _ := by ring
  obtain ⟨hl,hu⟩ := abs_le.mp hc
  constructor <;> linarith

theorem cut_mul_assoc (A B C : Cut) :
    cutMul (cutMul A.val B.val) C.val = cutMul A.val (cutMul B.val C.val) := by
  rw [cut_realLower A,cut_realLower B,cut_realLower C]
  simp only [realLower_mul,mul_assoc]

theorem cut_mul_comm (A B : Cut) : cutMul A.val B.val = cutMul B.val A.val := by
  rw [cut_realLower A,cut_realLower B,realLower_mul,realLower_mul,mul_comm]

theorem cut_mul_one (A : Cut) : cutMul A.val (rationalLower 1) = A.val := by
  rw [cut_realLower A,← realLower_one,realLower_mul]
  simp

theorem cut_mul_add (A B C : Cut) :
    cutMul A.val (cutAdd B.val C.val) = cutAdd (cutMul A.val B.val) (cutMul A.val C.val) := by
  rw [cut_realLower A,cut_realLower B,cut_realLower C]
  simp only [realLower_add,realLower_mul,mul_add]

theorem cut_positive_product (A B : Cut)
    (hA : rationalLower 0 ⊂ A.val) (hB : rationalLower 0 ⊂ B.val) :
    rationalLower 0 ⊂ cutMul A.val B.val := by
  rw [cut_realLower A,← realLower_zero,realLower_ssubset] at hA
  rw [cut_realLower B,← realLower_zero,realLower_ssubset] at hB
  rw [cut_realLower A,cut_realLower B,realLower_mul,← realLower_zero,realLower_ssubset]
  exact mul_pos hA hB

theorem cut_positive_inverse (A : Cut) (hA : rationalLower 0 ⊂ A.val) :
    IsCut (cutPositiveInv A.val) ∧ rationalLower 0 ⊂ cutPositiveInv A.val ∧
      cutMul A.val (cutPositiveInv A.val) = rationalLower 1 := by
  rw [cut_realLower A,← realLower_zero,realLower_ssubset] at hA
  rw [cut_realLower A,realLower_positiveInv _ hA,realLower_mul,← realLower_zero,realLower_ssubset,mul_inv_cancel₀ hA.ne']
  exact ⟨realLower_isCut _,inv_pos.mpr hA,by simpa using realLower_rat 1⟩

theorem cut_inverse (A : Cut) (hA : A.val ≠ rationalLower 0) :
    IsCut (cutInv A.val) ∧ cutMul A.val (cutInv A.val) = rationalLower 1 := by
  have hx : cutValue A ≠ 0 := by
    intro h
    exact hA ((cut_realLower A).trans (h ▸ (by simpa using realLower_rat 0)))
  rw [cut_realLower A,realLower_inv,realLower_mul,mul_inv_cancel₀ hx]
  exact ⟨realLower_isCut _,by simpa using realLower_rat 1⟩

def sqrtTwoLower : Set ℚ := {q | q < 0 ∨ q ^ 2 < 2}

private theorem sqrtTwo_realLower : sqrtTwoLower = realLower (Real.sqrt 2) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  ext q
  change (q < 0 ∨ q^2 < 2) ↔ (q:ℝ) < Real.sqrt 2
  constructor
  · rintro (hq | hq)
    · exact (by exact_mod_cast hq : (q:ℝ)<0).trans hs
    · have hq' : (q:ℝ)^2<2 := by exact_mod_cast hq
      nlinarith
  · intro hq
    by_cases hn : q<0
    · exact Or.inl hn
    · have hn' : 0≤(q:ℝ) := by exact_mod_cast le_of_not_gt hn
      have : (q:ℝ)^2<2 := by nlinarith
      exact Or.inr (by exact_mod_cast this)

theorem sqrtTwo_isCut : IsCut sqrtTwoLower := by
  rw [sqrtTwo_realLower]
  exact realLower_isCut _

theorem sqrtTwo_not_rational : ∀ q : ℚ, sqrtTwoLower ≠ rationalLower q := by
  intro q h
  rw [sqrtTwo_realLower,← realLower_rat] at h
  exact irrational_sqrt_two.ne_rat q (realLower_injective h)

theorem sqrtTwo_improvement (q : ℚ) (hq : 0 ≤ q) (hq2 : q ^ 2 < 2) :
    q < (2 * q + 2) / (q + 2) ∧ ((2 * q + 2) / (q + 2)) ^ 2 < 2 := by
  have hd : 0 < q+2 := by linarith
  constructor
  · rw [lt_div_iff₀ hd]
    nlinarith
  · rw [div_pow,div_lt_iff₀ (sq_pos_of_pos hd)]
    nlinarith [sq_nonneg q]

def IsCutFieldIso {K : Type u} [Field K] [LinearOrder K] (f : K → Cut) : Prop :=
  Function.Bijective f ∧ f 0 = rationalCut 0 ∧ f 1 = rationalCut 1 ∧
    (∀ x y, (f (x + y)).val = cutAdd (f x).val (f y).val) ∧
    (∀ x y, (f (x * y)).val = cutMul (f x).val (f y).val) ∧
    (∀ x y, (f x).val ⊆ (f y).val ↔ x ≤ y) ∧
    (∀ q : ℚ, f (q : K) = rationalCut q)

theorem complete_ordered_field_unique (K : Type u)
    [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K] :
    ∃! f : K → Cut, IsCutFieldIso f := by
  let e := ConditionallyCompleteLinearOrderedField.inducedOrderRingIso K ℝ
  let f : K → Cut := fun x => realCut (e x)
  have hf : IsCutFieldIso f := by
    refine ⟨cutEquiv.symm.bijective.comp e.bijective,?_,?_,?_,?_,?_,?_⟩
    · apply Subtype.ext
      change realLower (e 0) = rationalLower 0
      rw [map_zero,realLower_zero]
    · apply Subtype.ext
      change realLower (e 1) = rationalLower 1
      rw [map_one,realLower_one]
    · intro x y
      change realLower (e (x+y)) = cutAdd (realLower (e x)) (realLower (e y))
      rw [realLower_add,map_add]
    · intro x y
      change realLower (e (x*y)) = cutMul (realLower (e x)) (realLower (e y))
      rw [realLower_mul,map_mul]
    · intro x y
      change realLower (e x) ⊆ realLower (e y) ↔ x≤y
      rw [realLower_subset]
      exact e.map_le_map_iff'
    · intro q
      apply Subtype.ext
      change realLower (e (q:K)) = rationalLower q
      rw [map_ratCast,realLower_rat]
  refine ⟨f,hf,?_⟩
  intro g hg
  funext x
  apply Subtype.ext
  rw [cut_realLower (g x)]
  change realLower (cutValue (g x)) = realLower (e x)
  congr 1
  have hb (q : ℚ) : (q:ℝ) ≤ cutValue (g x) ↔ (q:ℝ) ≤ e x := by
    calc
      _ ↔ rationalLower q ⊆ (g x).val := by
        rw [cut_realLower (g x),← realLower_rat,realLower_subset]
      _ ↔ (q:K) ≤ x := by
        rw [← show (g (q:K)).val = rationalLower q from congrArg Subtype.val (hg.2.2.2.2.2.2 q)]
        exact hg.2.2.2.2.2.1 _ _
      _ ↔ (q:ℝ) ≤ e x := by
        simpa only [map_ratCast] using
          (show e (q:K) ≤ e x ↔ (q:K) ≤ x from e.map_le_map_iff').symm
  apply le_antisymm
  · by_contra hn
    obtain ⟨q,hq1,hq2⟩ := exists_rat_btwn (lt_of_not_ge hn)
    exact (not_le_of_gt hq1) ((hb q).mp hq2.le)
  · by_contra hn
    obtain ⟨q,hq1,hq2⟩ := exists_rat_btwn (lt_of_not_ge hn)
    exact (not_le_of_gt hq1) ((hb q).mpr hq2.le)

end Lemmatheca.Entry.ConstructingNumberSystems
