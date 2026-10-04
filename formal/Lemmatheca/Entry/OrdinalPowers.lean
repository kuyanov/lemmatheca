import Lemmatheca.Entry.OrdinalArithmetic
import Mathlib.SetTheory.Ordinal.CantorNormalForm
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.SetTheory.Cardinal.Ordinal

/-! Statements for arbitrary finite normal forms and the entry's concrete examples.
Coefficients are ordinals below omega, hence precisely finite natural numbers.
The canonical normal form itself is mathlib's `Ordinal.CNF`. -/
namespace Lemmatheca.Entry.OrdinalPowers
open Ordinal Order Set
open scoped Ordinal
universe u

def IsNormalForm (l : List (Ordinal.{u} × Ordinal.{u})) : Prop :=
  l.Pairwise (fun p q => q.1 < p.1) ∧ ∀ p ∈ l, 0 < p.2 ∧ p.2 < ω

noncomputable def evalNormalForm (l : List (Ordinal.{u} × Ordinal.{u})) : Ordinal.{u} :=
  l.foldr (fun p r => ω ^ p.1 * p.2 + r) 0

theorem normalForm_characterization (a : Ordinal.{u})
    (l : List (Ordinal.{u} × Ordinal.{u})) :
    (IsNormalForm l ∧ evalNormalForm l = a) ↔ l = CNF ω a := by sorry

theorem normalForm_lt_iff (l m : List (Ordinal.{u} × Ordinal.{u}))
    (hl : IsNormalForm l) (hm : IsNormalForm m) :
    evalNormalForm l < evalNormalForm m ↔
      List.Lex (Prod.Lex ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)
        ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)) l m := by sorry

theorem finite_sum_lt_power (g : Ordinal.{u}) (hg : 0 < g)
    (l : List (Ordinal.{u} × ℕ)) (hl : ∀ p ∈ l, p.1 < g) :
    l.foldr (fun p r => ω ^ p.1 * (p.2 : Ordinal.{u}) + r) 0 < ω ^ g := by sorry

theorem normalForm_example :
    CNF ω (ω ^ (2 : Ordinal.{u}) + ω + ω + 5) = [(2, 1), (1, 2), (0, 5)] ∧
    ω ^ (2 : Ordinal.{u}) + ω + ω + 5 < ω ^ (2 : Ordinal.{u}) * 2 := by sorry

theorem below_omega_power_omega_iff (a : Ordinal.{u}) :
    a < ω ^ (ω : Ordinal.{u}) ↔ ∀ p ∈ CNF ω a, p.1 < ω := by sorry

theorem absorption_example :
    (ω ^ (2 : Ordinal.{u}) + ω * 3 + 7) + ω ^ (2 : Ordinal.{u}) =
      ω ^ (2 : Ordinal.{u}) * 2 := by sorry

end Lemmatheca.Entry.OrdinalPowers
