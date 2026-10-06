import Lemmatheca.SetTheory.FoundationAndRank
import Mathlib.SetTheory.ZFC.VonNeumann

/-! Reusable CumulativeHierarchy definitions and results. -/

/-! Ordinal class rules are represented by universe-relative Lean functions
Ordinal → ZFSet. This is a semantic representation, not an encoding of formulas
with set parameters or Replacement in first-order ZF. Exhaustion of the hierarchy
is checked in the existing ZFSet model; its equivalence with Foundation over
ZF without Foundation remains an unbound logical claim. -/
set_option autoImplicit false
universe u
namespace Lemmatheca.SetTheory.CumulativeHierarchy
open Order
open scoped ZFSet Ordinal Cardinal
open Lemmatheca.SetTheory.FoundationAndRank

/-- A set is hereditarily finite if its singleton has finite transitive closure. -/
def HereditarilyFinite (x : ZFSet.{u}) : Prop := Finite (transitiveClosure {x})

private theorem finite_iff_card_lt (x : ZFSet.{u}) : Finite x ↔ x.card < ℵ₀ := by
  constructor
  · intro hx
    have h := Cardinal.mk_lt_aleph0_iff.mpr hx
    rw [ZFSet.cardinalMk_coe_sort] at h
    apply Cardinal.lift_lt.{u, u + 1}.mp
    simpa only [Cardinal.lift_aleph0] using h
  · intro hx
    apply Cardinal.mk_lt_aleph0_iff.mp
    rw [ZFSet.cardinalMk_coe_sort]
    simpa only [Cardinal.lift_aleph0] using Cardinal.lift_lt.{u, u + 1}.mpr hx

private theorem finite_vonNeumann (n : ℕ) : Finite (ZFSet.vonNeumann (n : Ordinal.{u})) := by
  apply (finite_iff_card_lt _).mpr
  induction n with
  | zero => simpa using Cardinal.aleph0_pos
  | succ n ih =>
    rw [Nat.cast_add_one, ZFSet.vonNeumann_add_one, ZFSet.card_powerset]
    exact Cardinal.power_lt_aleph0 Cardinal.natCast_lt_aleph0 ih

private theorem powerset_empty : ZFSet.powerset (∅ : ZFSet.{u}) = {∅} := by
  ext y
  rw [ZFSet.mem_powerset, ZFSet.mem_singleton]
  constructor
  · intro hy
    ext z
    exact ⟨fun hz => hy hz, fun hz => False.elim (ZFSet.notMem_empty _ hz)⟩
  · rintro rfl
    exact fun _ h => h

private theorem powerset_singleton (a : ZFSet.{u}) : ZFSet.powerset {a} = {∅, {a}} := by
  classical
  ext y
  rw [ZFSet.mem_powerset, ZFSet.mem_pair]
  constructor
  · intro hy
    by_cases ha : a ∈ y
    · right
      ext z
      rw [ZFSet.mem_singleton]
      exact ⟨fun hz => ZFSet.mem_singleton.mp (hy hz), fun hz => hz ▸ ha⟩
    · left
      ext z
      simp only [ZFSet.notMem_empty, iff_false]
      intro hz
      exact ha (ZFSet.mem_singleton.mp (hy hz) ▸ hz)
  · rintro (rfl | rfl)
    · exact fun _ h => False.elim (ZFSet.notMem_empty _ h)
    · exact fun _ h => h

private theorem powerset_pair (a b : ZFSet.{u}) :
    ZFSet.powerset {a,b} = {∅, {a}, {b}, {a,b}} := by
  classical
  ext y
  rw [ZFSet.mem_powerset]
  simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton]
  constructor
  · intro hy
    by_cases ha : a ∈ y <;> by_cases hb : b ∈ y
    · right; right; right
      ext z
      rw [ZFSet.mem_pair]
      exact ⟨fun hz => ZFSet.mem_pair.mp (hy hz), fun h => h.elim (fun h => h ▸ ha) (fun h => h ▸ hb)⟩
    · right; left
      ext z
      rw [ZFSet.mem_singleton]
      constructor
      · intro hz
        exact (ZFSet.mem_pair.mp (hy hz)).resolve_right (fun h => hb (h ▸ hz))
      · intro hz; exact hz ▸ ha
    · right; right; left
      ext z
      rw [ZFSet.mem_singleton]
      constructor
      · intro hz
        exact (ZFSet.mem_pair.mp (hy hz)).resolve_left (fun h => ha (h ▸ hz))
      · intro hz; exact hz ▸ hb
    · left
      ext z
      simp only [ZFSet.notMem_empty, iff_false]
      intro hz
      exact (ZFSet.mem_pair.mp (hy hz)).elim (fun h => ha (h ▸ hz)) (fun h => hb (h ▸ hz))
  · rintro (rfl | rfl | rfl | rfl)
    · exact fun _ h => False.elim (ZFSet.notMem_empty _ h)
    · intro z hz; simp only [ZFSet.mem_singleton] at hz; simp [hz]
    · intro z hz; simp only [ZFSet.mem_singleton] at hz; simp [hz]
    · exact fun _ h => h

/-- Finite stages, finite cardinalities, and the power-set recurrence. -/
theorem finite_stages :
    ZFSet.vonNeumann (0 : Ordinal.{u}) = ∅ ∧
    ZFSet.vonNeumann (1 : Ordinal.{u}) = {∅} ∧
    ZFSet.vonNeumann (2 : Ordinal.{u}) = {∅, {∅}} ∧
    ZFSet.vonNeumann (3 : Ordinal.{u}) = {∅, {∅}, {{∅}}, {∅, {∅}}} ∧
    (∀ n : ℕ, Finite (ZFSet.vonNeumann (n : Ordinal.{u}))) ∧
    (∀ n : ℕ, (ZFSet.vonNeumann ((n + 1 : ℕ) : Ordinal.{u})).card =
      2 ^ (ZFSet.vonNeumann (n : Ordinal.{u})).card) ∧
    (ZFSet.vonNeumann (4 : Ordinal.{u})).card = 16 ∧
    (ZFSet.vonNeumann (5 : Ordinal.{u})).card = 65536 := by
  have hrec : ∀ n : ℕ, (ZFSet.vonNeumann ((n + 1 : ℕ) : Ordinal.{u})).card =
      2 ^ (ZFSet.vonNeumann (n : Ordinal.{u})).card := by
    intro n
    rw [Nat.cast_add_one, ZFSet.vonNeumann_add_one, ZFSet.card_powerset]
  have h1 : ZFSet.vonNeumann (1 : Ordinal.{u}) = {∅} := by
    rw [show (1 : Ordinal.{u}) = 0 + 1 by simp, ZFSet.vonNeumann_add_one,
      ZFSet.vonNeumann_zero, powerset_empty]
  have h2 : ZFSet.vonNeumann (2 : Ordinal.{u}) = {∅, {∅}} := by
    rw [show (2 : Ordinal.{u}) = 1 + 1 by norm_num, ZFSet.vonNeumann_add_one,
      h1, powerset_singleton]
  have h3 : ZFSet.vonNeumann (3 : Ordinal.{u}) = {∅, {∅}, {{∅}}, {∅,{∅}}} := by
    rw [show (3 : Ordinal.{u}) = 2 + 1 by norm_num, ZFSet.vonNeumann_add_one,
      h2, powerset_pair]
  have hp22 : (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) = 4 := by
    change (2 : Cardinal.{u}) ^ (2 : ℕ) = 4
    norm_num
  have hp24 : (2 : Cardinal.{u}) ^ (4 : Cardinal.{u}) = 16 := by
    rw [show (4 : Cardinal.{u}) = (4 : ℕ) from rfl, Cardinal.power_natCast]
    norm_num
  have hp216 : (2 : Cardinal.{u}) ^ (16 : Cardinal.{u}) = 65536 := by
    rw [show (16 : Cardinal.{u}) = (16 : ℕ) from rfl, Cardinal.power_natCast]
    norm_num
  have hc1 : (ZFSet.vonNeumann (1 : Ordinal.{u})).card = 1 := by simpa using hrec 0
  have hc2 : (ZFSet.vonNeumann (2 : Ordinal.{u})).card = 2 := by simpa [hc1] using hrec 1
  have hc3 : (ZFSet.vonNeumann (3 : Ordinal.{u})).card = 4 := by simpa [hc2, hp22] using hrec 2
  have hc4 : (ZFSet.vonNeumann (4 : Ordinal.{u})).card = 16 := by simpa [hc3, hp24] using hrec 3
  have hc5 : (ZFSet.vonNeumann (5 : Ordinal.{u})).card = 65536 := by simpa [hc4, hp216] using hrec 4
  exact ⟨ZFSet.vonNeumann_zero, h1, h2, h3, finite_vonNeumann, hrec, hc4, hc5⟩

private theorem finite_rank_of_members (x : ZFSet.{u}) (hfinite : Finite x)
    (h : ∀ y ∈ x, y.rank < ω) : x.rank < ω := by
  rw [rank_equation]
  simp only [Order.succ_eq_add_one]
  apply Ordinal.lift_iSup_add_one_lt_of_lt_cof
  · simp
  · intro y
    exact h y.val y.property

/-- Hereditary finiteness is equivalent to finite rank and membership in the omega stage. -/
theorem hereditarilyFinite_iff (x : ZFSet.{u}) :
    (HereditarilyFinite x ↔ x.rank < ω) ∧
    (HereditarilyFinite x ↔ x ∈ ZFSet.vonNeumann ω) := by
  have hiff : HereditarilyFinite x ↔ x.rank < ω := by
    constructor
    · intro hx
      have hT := transitiveClosure_spec {x}
      have hall : ∀ y : ZFSet.{u}, y ∈ transitiveClosure {x} → y.rank < ω := by
        intro y
        induction y using ZFSet.inductionOn with
        | _ y ih =>
          intro hy
          have hsub : y ⊆ transitiveClosure {x} := hT.1 y hy
          have hyfin : Finite y := @Finite.of_injective _ _ hx
            (fun z : y => (⟨z.val, hsub z.property⟩ : transitiveClosure {x}))
            (fun a b hab => by
              apply Subtype.ext
              simpa only [Subtype.mk.injEq] using hab)
          exact finite_rank_of_members y hyfin (fun z hz => ih z hz (hsub hz))
      exact hall x (hT.2.1 (by simp))
    · intro hx
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hx
      have hmem : x ∈ ZFSet.vonNeumann ((n + 1 : ℕ) : Ordinal.{u}) := by
        rw [ZFSet.mem_vonNeumann, Nat.cast_add_one, hn]
        exact lt_add_one _
      have hsub : transitiveClosure {x} ⊆ ZFSet.vonNeumann ((n + 1 : ℕ) : Ordinal.{u}) :=
        (transitiveClosure_spec {x}).2.2 _ (ZFSet.isTransitive_vonNeumann _)
          (by intro z hz; exact ZFSet.mem_singleton.mp hz ▸ hmem)
      let := finite_vonNeumann.{u} (n + 1)
      exact Finite.of_injective
        (fun z : transitiveClosure {x} =>
          (⟨z.val, hsub z.property⟩ : ZFSet.vonNeumann ((n + 1 : ℕ) : Ordinal.{u})))
        (fun a b hab => by
              apply Subtype.ext
              simpa only [Subtype.mk.injEq] using hab)
  exact ⟨hiff, hiff.trans ZFSet.mem_vonNeumann.symm⟩

/-- The ordinal members of a stage are exactly the smaller ordinals. -/
theorem ordinal_part (a b : Ordinal.{u}) : b.toZFSet ∈ ZFSet.vonNeumann a ↔ b < a := by
  rw [ZFSet.mem_vonNeumann, Ordinal.rank_toZFSet]

/-- The omega stage is infinite but each of its members is finite. -/
theorem omega_stage : Infinite (ZFSet.vonNeumann (ω : Ordinal.{u})) ∧
    ∀ x ∈ ZFSet.vonNeumann (ω : Ordinal.{u}), Finite x := by
  have hinf : Infinite (ZFSet.vonNeumann (ω : Ordinal.{u})) := by
    apply Infinite.of_injective (fun n : ℕ =>
      (⟨(n : Ordinal.{u}).toZFSet, (ordinal_part _ _).mpr (Ordinal.natCast_lt_omega0 n)⟩ :
        ZFSet.vonNeumann (ω : Ordinal.{u})))
    intro a b hab
    exact_mod_cast Ordinal.toZFSet_injective (congrArg Subtype.val hab)
  refine ⟨hinf, ?_⟩
  intro x hx
  have hfin := (hereditarilyFinite_iff x).2.mpr hx
  have hsub : x ⊆ transitiveClosure {x} :=
    (transitiveClosure_spec {x}).1 x ((transitiveClosure_spec {x}).2.1 (by simp))
  exact @Finite.of_injective _ _ hfin
    (fun z : x => (⟨z.val, hsub z.property⟩ : transitiveClosure {x}))
    (fun a b hab => by
              apply Subtype.ext
              simpa only [Subtype.mk.injEq] using hab)

/-- Rank plus one is the least containing stage. -/
theorem least_stage (x : ZFSet.{u}) :
    IsLeast {a : Ordinal.{u} | x ∈ ZFSet.vonNeumann a} (x.rank + 1) := by
  refine ⟨?_, ?_⟩
  · exact ZFSet.mem_vonNeumann.mpr (lt_add_one _)
  · intro a ha
    exact Order.succ_le_of_lt (ZFSet.mem_vonNeumann.mp ha)

/-- Union stays in a stage; pairing and power sets stay within a nonzero limit stage. -/
theorem stage_closure (a : Ordinal.{u}) (x y : ZFSet.{u})
    (hx : x ∈ ZFSet.vonNeumann a) (hy : y ∈ ZFSet.vonNeumann a) :
    ⋃₀ x ∈ ZFSet.vonNeumann a ∧
    {x, y} ∈ ZFSet.vonNeumann (a + 1) ∧ ZFSet.powerset x ∈ ZFSet.vonNeumann (a + 1) ∧
    (IsSuccLimit a → {x,y} ∈ ZFSet.vonNeumann a ∧ ZFSet.powerset x ∈ ZFSet.vonNeumann a) := by
  have hxrank := ZFSet.mem_vonNeumann.mp hx
  have hyrank := ZFSet.mem_vonNeumann.mp hy
  refine ⟨ZFSet.mem_vonNeumann.mpr ((ZFSet.rank_sUnion_le x).trans_lt hxrank),
    ?_, ?_, ?_⟩
  · rw [ZFSet.mem_vonNeumann, ZFSet.rank_pair]
    exact max_lt (by simpa only [Order.succ_eq_add_one] using Order.succ_strictMono hxrank)
      (by simpa only [Order.succ_eq_add_one] using Order.succ_strictMono hyrank)
  · rw [ZFSet.mem_vonNeumann, ZFSet.rank_powerset]
    simpa only [Order.succ_eq_add_one] using Order.succ_strictMono hxrank
  · intro ha
    constructor
    · rw [ZFSet.mem_vonNeumann, ZFSet.rank_pair]
      exact max_lt (ha.succ_lt hxrank) (ha.succ_lt hyrank)
    · rw [ZFSet.mem_vonNeumann, ZFSet.rank_powerset]
      exact ha.succ_lt hxrank

/-- The least rank of an equinumerous representative. -/
noncomputable def scottRank (A : ZFSet.{u}) : Ordinal.{u} :=
  sInf {a | ∃ B : ZFSet.{u}, Nonempty (B ≃ A) ∧ B.rank = a}

/-- The set of all equinumerous representatives of least rank. -/
noncomputable def scottCardinal (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun B => B.rank = scottRank A ∧ Nonempty (B ≃ A))
    (ZFSet.vonNeumann (scottRank A + 1))

/-- Scott cardinals are nonempty and contain exactly the minimal-rank representatives. -/
theorem scottCardinal_spec (A : ZFSet.{u}) :
    (∃ B, B ∈ scottCardinal A) ∧
    (∀ B, B ∈ scottCardinal A ↔ B.rank = scottRank A ∧ Nonempty (B ≃ A)) ∧
    (∀ B : ZFSet.{u}, Nonempty (B ≃ A) → scottRank A ≤ B.rank) := by
  have hne : ({a | ∃ B : ZFSet.{u}, Nonempty (B ≃ A) ∧ B.rank = a} :
      Set Ordinal.{u}).Nonempty := ⟨A.rank, A, ⟨Equiv.refl A⟩, rfl⟩
  have hm := csInf_mem hne
  obtain ⟨B, he, hr⟩ := hm
  have mem_iff : ∀ B, B ∈ scottCardinal A ↔
      B.rank = scottRank A ∧ Nonempty (B ≃ A) := by
    intro B
    simp only [scottCardinal, ZFSet.mem_sep]
    constructor
    · exact And.right
    · intro hB
      exact ⟨ZFSet.mem_vonNeumann.mpr (hB.1 ▸ lt_add_one _), hB⟩
  refine ⟨⟨B, (mem_iff B).mpr ⟨hr, he⟩⟩, mem_iff, ?_⟩
  intro B hB
  exact csInf_le ⟨0, fun _ _ => bot_le⟩ ⟨B, hB, rfl⟩

/-- Scott cardinals classify equinumerosity. -/
theorem scottCardinal_eq_iff (A B : ZFSet.{u}) :
    scottCardinal A = scottCardinal B ↔ Nonempty (A ≃ B) := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := (scottCardinal_spec A).1
    have hCA := ((scottCardinal_spec A).2.1 C).mp hC
    have hCB := ((scottCardinal_spec B).2.1 C).mp (h ▸ hC)
    exact ⟨hCA.2.some.symm.trans hCB.2.some⟩
  · rintro ⟨e⟩
    have hr : scottRank A = scottRank B := by
      unfold scottRank
      congr 1
      ext a
      constructor
      · rintro ⟨C, ⟨f⟩, hc⟩
        exact ⟨C, ⟨f.trans e⟩, hc⟩
      · rintro ⟨C, ⟨f⟩, hc⟩
        exact ⟨C, ⟨f.trans e.symm⟩, hc⟩
    ext C
    rw [(scottCardinal_spec A).2.1, (scottCardinal_spec B).2.1, hr]
    constructor
    · rintro ⟨hC, ⟨f⟩⟩
      exact ⟨hC, ⟨f.trans e⟩⟩
    · rintro ⟨hC, ⟨f⟩⟩
      exact ⟨hC, ⟨f.trans e.symm⟩⟩

end Lemmatheca.SetTheory.CumulativeHierarchy
