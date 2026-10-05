import Lemmatheca.Entry.NaturalNumbersAsSets
import Mathlib.Data.Rat.Floor
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Algebra.Order.Ring.InjSurj

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
  sorry

def integerSetoid : Setoid (ℕ × ℕ) := ⟨IntegerRel, integerRel_equivalence⟩
def Integer := Quotient integerSetoid
def integerClass (a b : ℕ) : Integer := Quotient.mk integerSetoid (a, b)

theorem integer_value_respects (p q : ℕ × ℕ) (h : IntegerRel p q) :
    (p.1 : ℤ) - p.2 = (q.1 : ℤ) - q.2 := by
  sorry

def integerValue : Integer → ℤ :=
  Quotient.lift (fun p => (p.1 : ℤ) - p.2) integer_value_respects

def integerOfInt (z : ℤ) : Integer := integerClass z.toNat (-z).toNat

theorem integer_of_value (x : Integer) : integerOfInt (integerValue x) = x := by
  sorry

theorem integer_value_of (z : ℤ) : integerValue (integerOfInt z) = z := by
  sorry

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
  sorry

theorem integer_normal_form (x : Integer) :
    ∃! p : ℕ × Bool, (p.2 = true → 0 < p.1) ∧
      x = if p.2 then integerClass 0 p.1 else integerClass p.1 0 := by
  sorry

theorem natural_integer_embedding :
    Function.Injective (fun n : ℕ => integerClass n 0) ∧
    (∀ m n, integerAdd (integerClass m 0) (integerClass n 0) = integerClass (m + n) 0) ∧
    (∀ m n, integerMul (integerClass m 0) (integerClass n 0) = integerClass (m * n) 0) ∧
    (∀ m n, IntegerLE (integerClass m 0) (integerClass n 0) ↔ m ≤ n) ∧
    integerValue (integerClass 0 0) = 0 ∧ integerValue (integerClass 1 0) = 1 := by
  sorry

abbrev FractionRep := ℤ × {b : ℤ // b ≠ 0}
def RationalRel (p q : FractionRep) : Prop := p.1 * q.2.val = q.1 * p.2.val

theorem rationalRel_equivalence : Equivalence RationalRel := by
  sorry

def rationalSetoid : Setoid FractionRep := ⟨RationalRel, rationalRel_equivalence⟩
def Rational := Quotient rationalSetoid
def rationalClass (p : FractionRep) : Rational := Quotient.mk rationalSetoid p

theorem rational_value_respects (p q : FractionRep) (h : RationalRel p q) :
    (p.1 : ℚ) / p.2.val = (q.1 : ℚ) / q.2.val := by
  sorry

def rationalValue : Rational → ℚ :=
  Quotient.lift (fun p => (p.1 : ℚ) / p.2.val) rational_value_respects

def fractionCanonical (q : ℚ) : FractionRep :=
  (q.num, ⟨(q.den : ℤ), Int.natCast_ne_zero.mpr q.den_nz⟩)
def rationalOfRat (q : ℚ) : Rational := rationalClass (fractionCanonical q)

theorem rational_of_value (x : Rational) : rationalOfRat (rationalValue x) = x := by
  sorry

theorem rational_value_of (q : ℚ) : rationalValue (rationalOfRat q) = q := by
  sorry

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
  sorry

theorem rational_positive_denominator (x : Rational) :
    ∃ p : FractionRep, 0 < p.2.val ∧ rationalClass p = x := by
  sorry

theorem rational_representative_order (p q : FractionRep)
    (hp : 0 < p.2.val) (hq : 0 < q.2.val) :
    RationalLE (rationalClass p) (rationalClass q) ↔ p.1 * q.2.val ≤ q.1 * p.2.val := by
  sorry

theorem integer_rational_embedding :
    Function.Injective (fun z : ℤ => rationalOfRat (z : ℚ)) ∧
    (∀ a b : ℤ, rationalAdd (rationalOfRat a) (rationalOfRat b) = rationalOfRat (a + b : ℤ)) ∧
    (∀ a b : ℤ, rationalMul (rationalOfRat a) (rationalOfRat b) = rationalOfRat (a * b : ℤ)) ∧
    (∀ a b : ℤ, RationalLE (rationalOfRat a) (rationalOfRat b) ↔ a ≤ b) ∧
    rationalValue (rationalOfRat 0) = 0 ∧ rationalValue (rationalOfRat 1) = 1 := by
  sorry

theorem zero_denominator_failure :
    let R := fun p q : ℤ × ℤ => p.1 * q.2 = q.1 * p.2
    R (0, 1) (0, 0) ∧ R (0, 0) (1, 1) ∧ ¬ R (0, 1) (1, 1) ∧
      ¬ (∀ p q r, R p q → R q r → R p r) := by
  sorry

def IsCut (A : Set ℚ) : Prop :=
  A.Nonempty ∧ A ≠ univ ∧
    (∀ q ∈ A, ∀ p, p < q → p ∈ A) ∧ (∀ q ∈ A, ∃ r ∈ A, q < r)

def Cut := {A : Set ℚ // IsCut A}
def rationalLower (q : ℚ) : Set ℚ := {p | p < q}

theorem rationalLower_isCut (q : ℚ) : IsCut (rationalLower q) := by
  sorry

def rationalCut (q : ℚ) : Cut := ⟨rationalLower q, rationalLower_isCut q⟩

theorem cut_order_total (A B : Cut) : A.val ⊆ B.val ∨ B.val ⊆ A.val := by
  sorry

theorem rationalLower_order (p q : ℚ) :
    (rationalLower p ⊆ rationalLower q ↔ p ≤ q) ∧
      (rationalLower p ⊂ rationalLower q ↔ p < q) := by
  sorry

theorem cut_member_bounds (A : Cut) (q : ℚ) :
    (q ∈ A.val → rationalLower q ⊂ A.val) ∧
      (q ∉ A.val → A.val ⊆ rationalLower q) := by
  sorry

theorem cut_union_lub (F : Set Cut) (hne : F.Nonempty)
    (hb : ∃ U : Cut, ∀ A ∈ F, A.val ⊆ U.val) :
    IsCut (⋃ A ∈ F, A.val) ∧
    (∀ A ∈ F, A.val ⊆ ⋃ B ∈ F, B.val) ∧
    (∀ U : Cut, (∀ A ∈ F, A.val ⊆ U.val) → (⋃ A ∈ F, A.val) ⊆ U.val) := by
  sorry

theorem cut_union_boundary_cases :
    ¬ IsCut (∅ : Set ℚ) ∧ (⋃ q : ℚ, rationalLower q) = univ ∧ ¬ IsCut univ := by
  sorry

theorem cut_bracket (A : Cut) (ε : ℚ) (hε : 0 < ε) :
    ∃ a ∈ A.val, ∃ b ∉ A.val, 0 < b - a ∧ b - a < ε := by
  sorry

theorem rational_cuts_dense (A B : Cut) (h : A.val ⊂ B.val) :
    ∃ q : ℚ, A.val ⊂ rationalLower q ∧ rationalLower q ⊂ B.val := by
  sorry

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

theorem cut_add_neg_closed (A B : Cut) : IsCut (cutAdd A.val B.val) ∧ IsCut (cutNeg A.val) := by
  sorry

theorem cut_add_assoc (A B C : Cut) :
    cutAdd (cutAdd A.val B.val) C.val = cutAdd A.val (cutAdd B.val C.val) := by
  sorry

theorem cut_add_comm (A B : Cut) : cutAdd A.val B.val = cutAdd B.val A.val := by
  sorry

theorem cut_add_zero (A : Cut) : cutAdd A.val (rationalLower 0) = A.val := by
  sorry

theorem cut_add_neg (A : Cut) : cutAdd A.val (cutNeg A.val) = rationalLower 0 := by
  sorry

theorem cut_add_order (A B C : Cut) :
    (cutAdd A.val C.val ⊆ cutAdd B.val C.val ↔ A.val ⊆ B.val) ∧
      (cutAdd A.val C.val ⊂ cutAdd B.val C.val ↔ A.val ⊂ B.val) := by
  sorry

theorem rationalLower_add_neg (p q : ℚ) :
    rationalLower (p + q) = cutAdd (rationalLower p) (rationalLower q) ∧
      rationalLower (-p) = cutNeg (rationalLower p) := by
  sorry

theorem cut_mul_closed (A B : Cut) : IsCut (cutMul A.val B.val) := by
  sorry

theorem cut_mul_zero (A : Cut) :
    cutMul A.val (rationalLower 0) = rationalLower 0 ∧
      cutMul (rationalLower 0) A.val = rationalLower 0 := by
  sorry

theorem cut_mul_nonnegative (A B : Cut)
    (hA : rationalLower 0 ⊆ A.val) (hB : rationalLower 0 ⊆ B.val) :
    cutMul A.val B.val = cutPositiveMul A.val B.val := by
  sorry

theorem cut_mul_mono_nonnegative (A B C : Cut) (hAB : A.val ⊆ B.val)
    (hA : rationalLower 0 ⊆ A.val) (hC : rationalLower 0 ⊆ C.val) :
    cutMul A.val C.val ⊆ cutMul B.val C.val := by
  sorry

theorem rationalLower_mul (p q : ℚ) :
    rationalLower (p * q) = cutMul (rationalLower p) (rationalLower q) := by
  sorry

theorem cut_product_bracket (A B : Cut) (p q ε : ℚ) (hε : 0 < ε)
    (hA : rationalLower (p - ε) ⊆ A.val ∧ A.val ⊆ rationalLower (p + ε))
    (hB : rationalLower (q - ε) ⊆ B.val ∧ B.val ⊆ rationalLower (q + ε)) :
    let E := ε * (|p| + |q|) + ε ^ 2
    rationalLower (p * q - E) ⊆ cutMul A.val B.val ∧
      cutMul A.val B.val ⊆ rationalLower (p * q + E) := by
  sorry

theorem cut_mul_assoc (A B C : Cut) :
    cutMul (cutMul A.val B.val) C.val = cutMul A.val (cutMul B.val C.val) := by
  sorry

theorem cut_mul_comm (A B : Cut) : cutMul A.val B.val = cutMul B.val A.val := by
  sorry

theorem cut_mul_one (A : Cut) : cutMul A.val (rationalLower 1) = A.val := by
  sorry

theorem cut_mul_add (A B C : Cut) :
    cutMul A.val (cutAdd B.val C.val) = cutAdd (cutMul A.val B.val) (cutMul A.val C.val) := by
  sorry

theorem cut_positive_product (A B : Cut)
    (hA : rationalLower 0 ⊂ A.val) (hB : rationalLower 0 ⊂ B.val) :
    rationalLower 0 ⊂ cutMul A.val B.val := by
  sorry

theorem cut_positive_inverse (A : Cut) (hA : rationalLower 0 ⊂ A.val) :
    IsCut (cutPositiveInv A.val) ∧ rationalLower 0 ⊂ cutPositiveInv A.val ∧
      cutMul A.val (cutPositiveInv A.val) = rationalLower 1 := by
  sorry

theorem cut_inverse (A : Cut) (hA : A.val ≠ rationalLower 0) :
    IsCut (cutInv A.val) ∧ cutMul A.val (cutInv A.val) = rationalLower 1 := by
  sorry

def sqrtTwoLower : Set ℚ := {q | q < 0 ∨ q ^ 2 < 2}

theorem sqrtTwo_isCut : IsCut sqrtTwoLower := by
  sorry

theorem sqrtTwo_not_rational : ∀ q : ℚ, sqrtTwoLower ≠ rationalLower q := by
  sorry

theorem sqrtTwo_improvement (q : ℚ) (hq : 0 ≤ q) (hq2 : q ^ 2 < 2) :
    q < (2 * q + 2) / (q + 2) ∧ ((2 * q + 2) / (q + 2)) ^ 2 < 2 := by
  sorry

def IsCutFieldIso {K : Type u} [Field K] [LinearOrder K] (f : K → Cut) : Prop :=
  Function.Bijective f ∧ f 0 = rationalCut 0 ∧ f 1 = rationalCut 1 ∧
    (∀ x y, (f (x + y)).val = cutAdd (f x).val (f y).val) ∧
    (∀ x y, (f (x * y)).val = cutMul (f x).val (f y).val) ∧
    (∀ x y, (f x).val ⊆ (f y).val ↔ x ≤ y) ∧
    (∀ q : ℚ, f (q : K) = rationalCut q)

theorem complete_ordered_field_unique (K : Type u)
    [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K] :
    ∃! f : K → Cut, IsCutFieldIso f := by
  sorry

end Lemmatheca.Entry.ConstructingNumberSystems
