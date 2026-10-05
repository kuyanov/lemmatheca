import Lemmatheca.Entry.AxiomaticSetTheory
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Data.Nat.Basic
import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

/-! The constructed omega is connected explicitly to Lean's natural numbers.
Arithmetic statements about `Nat` specialize along this bijection; ordinal casts
identify their addition, multiplication and order with the finite ordinals. -/
namespace Lemmatheca.Entry.NaturalNumbersAsSets
open Lemmatheca.Entry.AxiomaticSetTheory
open scoped ZFSet Ordinal
universe u v

def naturalSet (n : ℕ) : ZFSet.{u} := ZFSet.mk (PSet.ofNat n)

private theorem naturalSet_zero : naturalSet.{u} 0 = ∅ := rfl

private theorem naturalSet_succ (n : ℕ) :
    naturalSet.{u} (n + 1) = insert (naturalSet n) (naturalSet n) := rfl

private theorem ofNat_naturalSet (n : ℕ) :
    ZFSet.mk (PSet.ofNat n) = naturalSet.{u} n := rfl

private theorem naturalSet_eq_toZFSet (n : ℕ) :
    naturalSet.{u} n = (n : Ordinal.{u}).toZFSet := by
  induction n with
  | zero => exact Ordinal.toZFSet_zero.symm
  | succ n ih =>
    rw [naturalSet_succ, Nat.cast_succ, Ordinal.toZFSet_add_one, ih]

theorem omega_members (x : ZFSet.{u}) : x ∈ ZFSet.omega ↔ ∃ n, naturalSet n = x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change (∃ n : ULift ℕ, PSet.Equiv x (PSet.ofNat n.down)) ↔
      ∃ n, naturalSet n = ZFSet.mk x
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n.down, (ofNat_naturalSet _).symm.trans (ZFSet.sound hn).symm⟩
    · rintro ⟨n,hn⟩
      refine ⟨⟨n⟩, ZFSet.exact ?_⟩
      exact hn.symm.trans (ofNat_naturalSet _).symm

theorem omega_eq_ordinal : ZFSet.omega.{u} = Ordinal.omega0.toZFSet := by
  apply ZFSet.ext
  intro x
  rw [omega_members, Ordinal.mem_toZFSet_iff]
  simp only [naturalSet_eq_toZFSet]
  constructor
  · rintro ⟨n,rfl⟩
    exact ⟨n, Ordinal.natCast_lt_omega0 n, rfl⟩
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp ha
    exact ⟨n,rfl⟩

theorem omega_least (I : ZFSet.{u}) (hI : IsInductive I) : ZFSet.omega ⊆ I := by
  have hn : ∀ n : ℕ, naturalSet.{u} n ∈ I := by
    intro n
    induction n with
    | zero => rw [naturalSet_zero]; exact hI.1
    | succ n ih => rw [naturalSet_succ]; exact hI.2 _ ih
  intro x hx
  obtain ⟨n,rfl⟩ := (omega_members x).mp hx
  exact hn n

theorem omega_unique_least :
    ∃! W : ZFSet.{u}, IsInductive W ∧ ∀ I, IsInductive I → W ⊆ I := by
  have hω : IsInductive ZFSet.omega.{u} := ⟨ZFSet.omega_zero, fun _ => ZFSet.omega_succ⟩
  refine ⟨ZFSet.omega, ⟨hω, omega_least⟩, ?_⟩
  intro W hW
  exact le_antisymm (hW.2 _ hω) (omega_least W hW.1)

theorem omega_subset_induction (A : ZFSet.{u}) (hA : A ⊆ ZFSet.omega)
    (hz : ∅ ∈ A) (hs : ∀ n ∈ A, insert n n ∈ A) : A = ZFSet.omega := by
  exact le_antisymm hA (omega_least A ⟨hz,hs⟩)

theorem omega_predicate_induction (P : ZFSet.{u} → Prop) (hz : P ∅)
    (hs : ∀ n ∈ ZFSet.omega, P n → P (insert n n)) : ∀ n ∈ ZFSet.omega, P n := by
  let A := ZFSet.sep P ZFSet.omega
  have he : A = ZFSet.omega := omega_subset_induction A ZFSet.sep_subset
    (ZFSet.mem_sep.mpr ⟨ZFSet.omega_zero,hz⟩)
    (fun n hn => ZFSet.mem_sep.mpr ⟨ZFSet.omega_succ (ZFSet.mem_sep.mp hn).1,
      hs n (ZFSet.mem_sep.mp hn).1 (ZFSet.mem_sep.mp hn).2⟩)
  intro n hn
  exact (ZFSet.mem_sep.mp (he.symm ▸ hn)).2

private theorem naturalSet_members (n : ℕ) (x : ZFSet.{u}) :
    x ∈ naturalSet n ↔ ∃ k < n, naturalSet k = x := by
  induction n with
  | zero =>
    rw [naturalSet_zero]
    exact ⟨fun h => (ZFSet.notMem_empty _ h).elim,
      fun ⟨k, hk, _⟩ => (Nat.not_lt_zero k hk).elim⟩
  | succ n ih =>
    rw [naturalSet_succ, ZFSet.mem_insert_iff, ih]
    constructor
    · rintro (h | ⟨k, hk, he⟩)
      · exact ⟨n, Nat.lt_succ_self n, h.symm⟩
      · exact ⟨k, Nat.lt_succ_of_lt hk, he⟩
    · rintro ⟨k, hk, he⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact Or.inr ⟨k, hk, he⟩
      · exact Or.inl he.symm

private theorem naturalSet_mem_of_lt {m n : ℕ} (h : m < n) :
    naturalSet.{u} m ∈ naturalSet n := (naturalSet_members n _).mpr ⟨m, h, rfl⟩

private theorem naturalSet_injective : Function.Injective naturalSet.{u} := by
  intro m n he
  rcases Nat.lt_trichotomy m n with h | h | h
  · exact (ZFSet.mem_irrefl _ (he ▸ naturalSet_mem_of_lt h)).elim
  · exact h
  · exact (ZFSet.mem_irrefl _ (he.symm ▸ naturalSet_mem_of_lt h)).elim

theorem omega_peano :
    (∀ n ∈ ZFSet.omega.{u}, insert n n ≠ ∅) ∧
    (∀ n ∈ ZFSet.omega.{u}, ∀ m ∈ ZFSet.omega, insert n n = insert m m → n = m) ∧
    (∀ n ∈ ZFSet.omega.{u}, n ≠ ∅ → ∃! m, m ∈ ZFSet.omega ∧ insert m m = n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n _ he
    exact ZFSet.notMem_empty n (he ▸ ZFSet.mem_insert n n)
  · intro n hn m hm he
    obtain ⟨j, rfl⟩ := (omega_members n).mp hn
    obtain ⟨k, rfl⟩ := (omega_members m).mp hm
    rw [← naturalSet_succ, ← naturalSet_succ] at he
    exact congrArg naturalSet (Nat.succ_inj.mp (naturalSet_injective he))
  · intro n hn hne
    obtain ⟨k, rfl⟩ := (omega_members n).mp hn
    have hk : k ≠ 0 := fun h => hne (h ▸ naturalSet_zero)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    refine ⟨naturalSet k, ⟨(omega_members _).mpr ⟨k, rfl⟩,
      (naturalSet_succ k).symm⟩, ?_⟩
    intro m hm
    obtain ⟨j, rfl⟩ := (omega_members m).mp hm.1
    have he := hm.2
    rw [← naturalSet_succ] at he
    exact congrArg naturalSet (Nat.succ_inj.mp (naturalSet_injective he))

theorem finite_ordinals (a : ZFSet.{u}) (ha : a.IsOrdinal) :
    a ∈ ZFSet.omega ↔ Finite a := by
  have hω : ZFSet.IsOrdinal ZFSet.omega.{u} := omega_eq_ordinal ▸ ZFSet.isOrdinal_toZFSet _
  have hmem : a ∈ ZFSet.omega ↔ a.rank < Ordinal.omega0 := by
    rw [← ha.rank_lt_iff_mem hω, omega_eq_ordinal, Ordinal.rank_toZFSet]
  have hcard : ZFSet.card a = a.rank.card := by
    calc
      ZFSet.card a = ZFSet.card a.rank.toZFSet := congrArg ZFSet.card ha.toZFSet_rank_eq.symm
      _ = a.rank.card := Ordinal.card_toZFSet _
  rw [hmem, ← Ordinal.card_lt_aleph0, ← hcard]
  have hh := Cardinal.mk_lt_aleph0_iff (α := a)
  rw [ZFSet.cardinalMk_coe_sort, Cardinal.lift_lt_aleph0] at hh
  exact hh

theorem omega_no_greatest : ∀ n ∈ ZFSet.omega.{u}, ∃ m ∈ ZFSet.omega, n ∈ m := by
  intro n hn
  exact ⟨insert n n, ZFSet.omega_succ hn, ZFSet.mem_insert n n⟩

theorem naturalSet_order (m n : ℕ) :
    (naturalSet.{u} m ∈ naturalSet n ↔ m < n) ∧
      (naturalSet.{u} m ⊆ naturalSet n ↔ m ≤ n) := by
  constructor
  · constructor
    · intro h
      obtain ⟨k, hk, he⟩ := (naturalSet_members n _).mp h
      exact naturalSet_injective he ▸ hk
    · exact naturalSet_mem_of_lt
  · constructor
    · intro h
      rcases le_or_gt m n with hle | hlt
      · exact hle
      · exact (ZFSet.mem_irrefl _ (h (naturalSet_mem_of_lt hlt))).elim
    · intro h x hx
      obtain ⟨k, hk, rfl⟩ := (naturalSet_members m x).mp hx
      exact naturalSet_mem_of_lt (Nat.lt_of_lt_of_le hk h)

theorem sequence_unique (C : Type v) (c : C) (g : C → C) :
    ∃! f : ℕ → C, f 0 = c ∧ ∀ n, f (n + 1) = g (f n) := by
  refine ⟨fun n => Nat.rec c (fun _ x => g x) n, ⟨rfl, fun _ => rfl⟩, ?_⟩
  intro f hf
  funext n
  induction n with
  | zero => exact hf.1
  | succ n ih => simpa [hf.2 n,ih]

theorem sequence_parameter_unique (C : Type v) (c : C) (g : ℕ → C → C) :
    ∃! f : ℕ → C, f 0 = c ∧ ∀ n, f (n + 1) = g n (f n) := by
  refine ⟨fun n => Nat.rec c g n, ⟨rfl, fun _ => rfl⟩, ?_⟩
  intro f hf
  funext n
  induction n with
  | zero => exact hf.1
  | succ n ih => simpa [hf.2 n,ih]

theorem natural_additive_difference (m n : ℕ) : m ≤ n ↔ ∃! k, m + k = n := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le h
    exact ⟨k,hk.symm,fun j hj => Nat.add_left_cancel (hj.trans hk)⟩
  · rintro ⟨k,hk,_⟩
    exact hk ▸ Nat.le_add_right m k

theorem peano_system_unique (C : Type v) (c : C) (g : C → C)
    (hg : Function.Injective g) (hc : ∀ x, g x ≠ c)
    (hInd : ∀ A : Set C, c ∈ A → (∀ x ∈ A, g x ∈ A) → A = Set.univ) :
    ∃! f : ℕ → C, Function.Bijective f ∧ f 0 = c ∧ ∀ n, f (n + 1) = g (f n) := by
  obtain ⟨f,hf,huniq⟩ := sequence_unique C c g
  have hsurj : Function.Surjective f := by
    have hr : Set.range f = Set.univ := hInd _ ⟨0,hf.1⟩ (by
      rintro x ⟨n,rfl⟩
      exact ⟨n+1,hf.2 n⟩)
    exact Set.range_eq_univ.mp hr
  have hinj : Function.Injective f := by
    intro n m
    induction n generalizing m with
    | zero =>
      cases m with
      | zero => simp
      | succ m => intro h; exact (hc (f m) ((hf.2 m).symm.trans (h.symm.trans hf.1))).elim
    | succ n ih =>
      cases m with
      | zero => intro h; exact (hc (f n) ((hf.2 n).symm.trans (h.trans hf.1))).elim
      | succ m => intro h; exact congrArg Nat.succ (ih (hg (by simpa [hf.2] using h)))
  refine ⟨f,⟨⟨hinj,hsurj⟩,hf⟩,fun h hh => huniq h hh.2⟩

def extraPointSucc : WithTop ℕ → WithTop ℕ
  | ⊤ => ⊤
  | (n : ℕ) => ((n + 1 : ℕ) : WithTop ℕ)

theorem extra_point_counterexample :
    Function.Injective extraPointSucc ∧ (∀ x, extraPointSucc x ≠ (0 : WithTop ℕ)) ∧
    (let A : Set (WithTop ℕ) := Set.range (fun n : ℕ => (n : WithTop ℕ))
     (0 : WithTop ℕ) ∈ A ∧ (∀ x ∈ A, extraPointSucc x ∈ A) ∧ A ≠ Set.univ) ∧
    (fun n : ℕ => (extraPointSucc^[n]) (0 : WithTop ℕ)) =
      (fun n : ℕ => (n : WithTop ℕ)) := by
  have hinj : Function.Injective extraPointSucc := by
    intro a b h
    cases a with
    | top =>
      cases b with
      | top => rfl
      | coe b => cases h
    | coe a =>
      cases b with
      | top => cases h
      | coe b => exact congrArg some (Nat.succ_inj.mp (Option.some.inj h))
  refine ⟨hinj, ?_, ?_, ?_⟩
  · intro x h
    cases x with
    | top => cases h
    | coe n => exact Nat.noConfusion (Option.some.inj h)
  · refine ⟨⟨0, rfl⟩, ?_, ?_⟩
    · rintro x ⟨n, rfl⟩
      exact ⟨n+1, rfl⟩
    · intro he
      have hm : (⊤ : WithTop ℕ) ∈ Set.range (fun n : ℕ => (n : WithTop ℕ)) :=
        he.symm ▸ Set.mem_univ _
      obtain ⟨n, hn⟩ := hm
      cases hn
  · funext n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',ih]; rfl

end Lemmatheca.Entry.NaturalNumbersAsSets
