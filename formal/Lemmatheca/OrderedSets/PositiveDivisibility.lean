import Mathlib.Data.PNat.Basic

/-!
# Positive integers ordered by divisibility

A separate carrier keeps the divisibility order distinct from the usual numerical
order on positive integers. The value lemmas identify its comparisons with
divisibility of the underlying natural numbers.
-/

namespace Lemmatheca.SetTheory.PositiveDivisibility

/-- A copy of the positive integers reserved for the divisibility order. -/
def DvdPNat := ℕ+

instance (n : ℕ) [NeZero n] : OfNat DvdPNat n := inferInstanceAs (OfNat ℕ+ n)
instance : Dvd DvdPNat := inferInstanceAs (Dvd ℕ+)

/-- Positive integers ordered by divisibility, not by their numerical size. -/
instance pnatDivisibility : PartialOrder DvdPNat where
  le := (· ∣ ·)
  lt a b := a ∣ b ∧ ¬ b ∣ a
  le_refl a := @dvd_refl ℕ+ _ a
  le_trans a b c := @dvd_trans ℕ+ _ a b c
  le_antisymm _ _ := PNat.dvd_antisymm

theorem dvdPNat_dvd_iff (a b : DvdPNat) : a ∣ b ↔ (a : ℕ+).val ∣ (b : ℕ+).val :=
  PNat.dvd_iff

theorem dvdPNat_le_iff (a b : DvdPNat) : a ≤ b ↔ (a : ℕ+).val ∣ (b : ℕ+).val :=
  PNat.dvd_iff

theorem dvdPNat_eq_iff (a b : DvdPNat) : a = b ↔ (a : ℕ+).val = (b : ℕ+).val :=
  Subtype.val_inj.symm

end Lemmatheca.SetTheory.PositiveDivisibility
