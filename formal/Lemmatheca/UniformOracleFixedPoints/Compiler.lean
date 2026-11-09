import Lemmatheca.OracleProgramNumberings.Universal
import Lemmatheca.OraclePadding.Basic

/-! A specified numerical self-reference compiler fixed before every oracle. -/
namespace Lemmatheca.ComputabilityTheory.UniformOracleFixedPoints

open OracleComputation OracleProgramNumberings

def IsAllOracleSelector (F : ℕ → ℕ → ℕ) (h : ℕ → ℕ) : Prop :=
  Computable h ∧ ∀ A : Set ℕ, ∀ a x,
    phi A (h a) x = phi A (F (h a) a) x

def driverInput (w : ℕ) : ℕ :=
  Nat.pair w.unpair.1
    (Nat.pair (specialize (specialize w.unpair.2.unpair.1 w.unpair.2.unpair.1)
      w.unpair.2.unpair.2.unpair.1) w.unpair.2.unpair.2)

theorem driver_input_primitive : Nat.Primrec driverInput := by
  have hp : Primrec (fun w : ℕ => w.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hb : Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hy : Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact Primrec.nat_iff.mp (Primrec₂.natPair.comp hp
    (Primrec₂.natPair.comp
      (specialize_primitive.comp (specialize_primitive.comp hb hb)
        (Primrec.fst.comp (Primrec.unpair.comp hy))) hy))

noncomputable def driverOrdinaryCode : Nat.Partrec.Code :=
  ordinaryCode driverInput driver_input_primitive

theorem driver_ordinary_eval (w : ℕ) :
    Nat.Partrec.Code.eval driverOrdinaryCode w = Part.some (driverInput w) := by
  exact ordinaryCode_eval driverInput driver_input_primitive w

noncomputable def driverIndex : ℕ :=
  encodeCode (.comp universalCode (embed driverOrdinaryCode))

theorem driver_eval (A : Set ℕ) (p b y : ℕ) :
    phi A driverIndex (Nat.pair p (Nat.pair b y)) =
      phi A p (Nat.pair (specialize (specialize b b) y.unpair.1) y) := by
  simp only [phi, driverIndex, decode_encode, eval, eval_embed, driver_ordinary_eval,
    Part.bind_some, driverInput, Nat.unpair_pair, universal_code_eval]

noncomputable def driverSpecialization (p : ℕ) : ℕ := specialize driverIndex p

noncomputable def selfSpecializedIndex (p : ℕ) : ℕ :=
  specialize (driverSpecialization p) (driverSpecialization p)

noncomputable def compiler (p a : ℕ) : ℕ := specialize (selfSpecializedIndex p) a

theorem compiler_primitive : Primrec₂ compiler := by
  have hr : Primrec driverSpecialization :=
    specialize_primitive.comp (Primrec.const driverIndex) Primrec.id
  have hq : Primrec selfSpecializedIndex := specialize_primitive.comp hr hr
  exact specialize_primitive.comp (hq.comp Primrec.fst) Primrec.snd

theorem compiler_injective {p a p' a' : ℕ}
    (h : compiler p a = compiler p' a') : p = p' ∧ a = a' := by
  have h₁ := OraclePadding.specialize_injective h
  have h₂ := OraclePadding.specialize_injective h₁.1
  have h₃ := OraclePadding.specialize_injective h₂.1
  exact ⟨h₃.2, h₁.2⟩

theorem specialized_driver_eval (A : Set ℕ) (p b y : ℕ) :
    phi A (driverSpecialization p) (Nat.pair b y) =
      phi A p (Nat.pair (specialize (specialize b b) y.unpair.1) y) := by
  rw [driverSpecialization, specialize_eval, driver_eval]

theorem compiler_eval (A : Set ℕ) (p a x : ℕ) :
    phi A (compiler p a) x =
      phi A p (Nat.pair (compiler p a) (Nat.pair a x)) := by
  rw [compiler, specialize_eval, selfSpecializedIndex, specialize_eval,
    specialized_driver_eval]
  simp only [Nat.unpair_pair]

theorem specified_partial_family_selector
    {g : Set ℕ → ℕ → ℕ → ℕ → Part ℕ} (p : ℕ)
    (hp : ∀ A : Set ℕ, ∀ n a x,
      phi A p (Nat.pair n (Nat.pair a x)) = g A n a x) :
    Primrec (compiler p) ∧ ∀ A : Set ℕ, ∀ a x,
      phi A (compiler p a) x = g A (compiler p a) a x := by
  refine ⟨compiler_primitive.comp (Primrec.const p) Primrec.id, ?_⟩
  intro A a x
  exact (compiler_eval A p a x).trans (hp A (compiler p a) a x)

end Lemmatheca.ComputabilityTheory.UniformOracleFixedPoints
