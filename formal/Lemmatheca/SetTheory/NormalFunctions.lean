import Mathlib.SetTheory.Ordinal.Veblen
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Tactic

/-! Reusable NormalFunctions definitions and results. -/

/-! Normal functions use universe-relative ordinals. Finite hereditary
notations ONote and their ordinal evaluations use universe zero; this
specialization does not encode the ZF derivability claims of the prose. -/
set_option autoImplicit false
universe u
namespace Lemmatheca.SetTheory.NormalFunctions
open Order
open scoped Ordinal

/-- Successor is strictly increasing but is not a normal ordinal function. -/
theorem successor_not_normal : StrictMono (Order.succ : Ordinal.{u} → Ordinal.{u}) ∧
    ¬ IsNormal (Order.succ : Ordinal.{u} → Ordinal.{u}) := by
  refine ⟨Order.succ_strictMono, ?_⟩
  intro h
  have he := h.map_iSup (g := fun n : ℕ => (n : Ordinal.{u})) Ordinal.bddAbove_of_small
  have hs : (⨆ n : ℕ, Order.succ (n : Ordinal.{u})) = ω := by
    apply le_antisymm
    · apply ciSup_le
      intro n
      simpa only [Order.succ_eq_add_one, ← Nat.cast_add_one] using (Ordinal.natCast_lt_omega0 (n + 1)).le
    · rw [← Ordinal.iSup_natCast]
      apply ciSup_mono Ordinal.bddAbove_of_small
      intro n
      exact Order.le_succ _
  rw [Ordinal.iSup_natCast, hs] at he
  exact (lt_succ (ω : Ordinal.{u})).ne he.symm

/-- Nonempty bounded suprema of fixed points of a normal function are fixed. -/
theorem fixed_points_closed (f : Ordinal.{u} → Ordinal.{u}) (hf : IsNormal f)
    (S : Set Ordinal.{u}) (hS : S.Nonempty) (hb : BddAbove S)
    (hfixed : ∀ a ∈ S, f a = a) : f (sSup S) = sSup S := by
  rw [hf.map_sSup hS hb]
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa only [hfixed b hb] using hb
  · intro ha
    exact ⟨a, ha, hfixed a ha⟩

/-- The finite omega towers starting at one. -/
noncomputable def tower (n : ℕ) : Ordinal.{u} := (fun a => ω ^ a)^[n] 1

/-- Epsilon zero is the supremum of the strictly increasing towers; each lies below it. -/
theorem tower_spec : StrictMono (tower : ℕ → Ordinal.{u}) ∧
    (⨆ n, tower n : Ordinal.{u}) = Ordinal.epsilon 0 ∧
    (∀ n, tower n < (Ordinal.epsilon 0 : Ordinal.{u})) ∧
    (∀ a : Ordinal.{u}, a < Ordinal.epsilon 0 ↔ ∃ n, a < tower n) := by
  have hshift (n : ℕ) : tower n = (fun a : Ordinal.{u} => ω ^ a)^[n + 1] 0 := by
    rw [Function.iterate_succ_apply]
    simp [tower]
  have hmono : StrictMono (tower : ℕ → Ordinal.{u}) := by
    apply strictMono_nat_of_lt_succ
    intro n
    change (fun a : Ordinal.{u} => ω ^ a)^[n] 1 < (fun a => ω ^ a)^[n + 1] 1
    rw [Function.iterate_succ_apply]
    exact (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono.iterate n
      (by simp)
  have hlt : ∀ n, tower n < (Ordinal.epsilon 0 : Ordinal.{u}) := by
    intro n
    rw [hshift]
    exact Ordinal.iterate_omega0_opow_lt_epsilon_zero (n + 1)
  have hsup : (⨆ n, tower n : Ordinal.{u}) = Ordinal.epsilon 0 := by
    apply le_antisymm
    · exact Ordinal.iSup_le (fun n => (hlt n).le)
    · apply le_of_not_gt
      intro h
      obtain ⟨n, hn⟩ := Ordinal.lt_epsilon_zero.mp h
      cases n with
      | zero => simp at hn
      | succ n =>
        rw [← hshift n] at hn
        exact hn.not_ge (Ordinal.le_iSup tower.{u} n)
  refine ⟨hmono, hsup, hlt, ?_⟩
  intro a
  rw [← hsup]
  exact Ordinal.lt_iSup_iff

/-- Every finite ordinal notation denotes an ordinal below epsilon zero. -/
theorem notation_below_epsilon (t : ONote) : ONote.repr t < Ordinal.epsilon 0 := by
  induction t with
  | zero => exact Ordinal.epsilon_pos 0
  | oadd e c a ihe iha =>
    have hp : (ω : Ordinal.{0}) ^ ONote.repr e < Ordinal.epsilon 0 := by
      conv_rhs => rw [← Ordinal.omega0_opow_epsilon 0]
      exact (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono ihe
    have hprincipal : Ordinal.IsPrincipal (· + ·) (Ordinal.epsilon 0 : Ordinal.{0}) := by
      conv_rhs => rw [← Ordinal.omega0_opow_epsilon 0]
      exact Ordinal.isPrincipal_add_omega0_opow _
    exact hprincipal (hprincipal.mul_natCast_lt hp c.val) iha

/-- Finite hereditary Cantor normal forms denote exactly the ordinals below epsilon zero. -/
theorem hereditary_forms (a : Ordinal.{0}) :
    a < Ordinal.epsilon 0 ↔ ∃ t : ONote, ONote.NF t ∧ ONote.repr t = a := by
  constructor
  · intro ha
    induction a using (wellFounded_lt (α := Ordinal.{0})).induction with
    | h a ih =>
      by_cases hz : a = 0
      · exact ⟨.zero, ONote.NF.zero, hz.symm⟩
      have hpow : a < ω ^ a := by
        by_contra hp
        exact ha.not_ge (Ordinal.epsilon_zero_le_of_omega0_opow_le (le_of_not_gt hp))
      have he : Ordinal.log ω a < a :=
        (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hz).mp hpow
      have hr := Ordinal.mod_opow_log_lt_self ω hz
      obtain ⟨e, hNF_e, heq⟩ := ih _ he (he.trans ha)
      obtain ⟨r, hNF_r, hrq⟩ := ih _ hr (hr.trans ha)
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (Ordinal.div_opow_log_lt a Ordinal.one_lt_omega0)
      have hnpos : 0 < n := by
        have := Ordinal.div_opow_log_pos ω hz
        rw [hn] at this
        exact_mod_cast this
      refine ⟨.oadd e ⟨n, hnpos⟩ r, ?_, ?_⟩
      · apply hNF_e.oadd
        exact hNF_r.below_of_lt' (by
          rw [hrq, heq]
          exact Ordinal.mod_lt _ (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero))
      · change ω ^ ONote.repr e * (n : Ordinal.{0}) + ONote.repr r = a
        rw [heq, hrq, ← hn]
        exact Ordinal.div_add_mod a (ω ^ Ordinal.log ω a)
  · rintro ⟨t, _, rfl⟩
    exact notation_below_epsilon t

/-- Evaluation of a hereditary expression at a natural-number base. -/
def evalNat (b : ℕ) : ONote → ℕ
  | .zero => 0
  | .oadd e c a => b ^ evalNat b e * c.val + evalNat b a

/-- The canonical hereditary base expansion, using the exponents below the represented number. -/
def hereditary (b : ℕ) : ℕ → ONote :=
  Nat.lt_wfRel.wf.fix fun m rec =>
    (List.finRange m).reverse.foldr (fun e tail =>
      let digit := m / b ^ e.val % b
      if hd : digit = 0 then tail else
        ONote.oadd (rec e.val e.isLt) ⟨digit, Nat.pos_of_ne_zero hd⟩ tail) .zero

/-- Changing the base in a canonical hereditary expression. -/
def baseChange (b c m : ℕ) : ℕ := evalNat c (hereditary b m)

/-- Replacing every occurrence of the base by omega gives an ordinal measure. -/
noncomputable def ordinalMeasure (b m : ℕ) : Ordinal.{0} := ONote.repr (hereditary b m)

/-- A canonical base expression has small digits, normalized exponents, and decreasing exponents. -/
def Canonical (b : ℕ) : ONote → Prop
  | .zero => True
  | .oadd e c a => Canonical b e ∧ Canonical b a ∧ c.val < b ∧
      match a with
      | .zero => True
      | .oadd e' _ _ => evalNat b e' < evalNat b e

private def headBelow (b : ℕ) (t : ONote) (k : ℕ) : Prop :=
  match t with
  | .zero => True
  | .oadd e _ _ => evalNat b e < k

private theorem canonical_bound (b : ℕ) (hb : 2 ≤ b) (t : ONote) :
    ∀ k, Canonical b t → headBelow b t k → evalNat b t < b ^ k := by
  induction t with
  | zero =>
    intro k _ _
    exact pow_pos (by omega) k
  | oadd e c a _ iha =>
    intro k ht hk
    obtain ⟨he, ha, hc, htail⟩ := ht
    have htail' : headBelow b a (evalNat b e) := by
      cases a <;> exact htail
    have hbound := iha _ ha htail'
    have hpow : 0 < b ^ evalNat b e := pow_pos (by omega) _
    calc
      evalNat b (.oadd e c a) = b ^ evalNat b e * c.val + evalNat b a := rfl
      _ < b ^ evalNat b e * (c.val + 1) := by rw [Nat.mul_add, mul_one]; omega
      _ ≤ b ^ evalNat b e * b := Nat.mul_le_mul_left _ (by omega)
      _ = b ^ (evalNat b e + 1) := (pow_succ _ _).symm
      _ ≤ b ^ k := Nat.pow_le_pow_right (by omega) (by exact hk)

private theorem eval_positive (b : ℕ) (hb : 0 < b) (e : ONote) (c : ℕ+) (a : ONote) :
    0 < evalNat b (.oadd e c a) := by
  change 0 < b ^ evalNat b e * c.val + evalNat b a
  exact lt_of_lt_of_le (Nat.mul_pos (pow_pos hb _) c.pos) (Nat.le_add_right _ _)

private theorem canonical_cmp (b : ℕ) (hb : 2 ≤ b) :
    ∀ t s, Canonical b t → Canonical b s →
      (ONote.cmp t s).Compares (evalNat b t) (evalNat b s)
  | .zero, .zero, _, _ => rfl
  | .zero, .oadd e c a, _, _ => eval_positive b (by omega) e c a
  | .oadd e c a, .zero, _, _ => eval_positive b (by omega) e c a
  | .oadd e c a, .oadd f d r, ht, hs => by
    obtain ⟨he, ha, hc, htail⟩ := ht
    obtain ⟨hf, hr, hd, htail'⟩ := hs
    have hecmp := canonical_cmp b hb e f he hf
    have hacmp := canonical_cmp b hb a r ha hr
    have hba : evalNat b a < b ^ evalNat b e :=
      canonical_bound b hb a _ ha (by cases a <;> exact htail)
    have hbr : evalNat b r < b ^ evalNat b f :=
      canonical_bound b hb r _ hr (by cases r <;> exact htail')
    rw [ONote.cmp]
    cases hcmp : ONote.cmp e f with
    | lt =>
      simp only [hcmp, Ordering.Compares] at hecmp
      change evalNat b (.oadd e c a) < evalNat b (.oadd f d r)
      have hwhole : evalNat b (.oadd e c a) < b ^ evalNat b f :=
        canonical_bound b hb _ _ ⟨he, ha, hc, htail⟩ hecmp
      have hpow : b ^ evalNat b f ≤ b ^ evalNat b f * d.val :=
        Nat.le_mul_of_pos_right _ d.pos
      exact hwhole.trans_le (hpow.trans (Nat.le_add_right _ _))
    | gt =>
      simp only [hcmp, Ordering.Compares] at hecmp
      change evalNat b (.oadd f d r) < evalNat b (.oadd e c a)
      have hwhole : evalNat b (.oadd f d r) < b ^ evalNat b e :=
        canonical_bound b hb _ _ ⟨hf, hr, hd, htail'⟩ hecmp
      exact hwhole.trans_le ((Nat.le_mul_of_pos_right _ c.pos).trans (Nat.le_add_right _ _))
    | eq =>
      simp only [hcmp, Ordering.Compares] at hecmp
      have hccmp := (show (_root_.cmp c.val d.val).Compares c.val d.val from by
        unfold _root_.cmp cmpUsing
        split_ifs <;> simp only [Ordering.Compares] <;> omega)
      cases hcd : _root_.cmp c.val d.val with
      | lt =>
        simp only [hcd, Ordering.Compares] at hccmp
        change b ^ evalNat b e * c.val + evalNat b a < b ^ evalNat b f * d.val + evalNat b r
        rw [hecmp] at hba ⊢
        calc
          _ < b ^ evalNat b f * (c.val + 1) := by rw [Nat.mul_add, mul_one]; omega
          _ ≤ b ^ evalNat b f * d.val := Nat.mul_le_mul_left _ (by omega)
          _ ≤ _ := Nat.le_add_right _ _
      | gt =>
        simp only [hcd, Ordering.Compares] at hccmp
        change b ^ evalNat b f * d.val + evalNat b r < b ^ evalNat b e * c.val + evalNat b a
        rw [hecmp]
        calc
          _ < b ^ evalNat b f * (d.val + 1) := by rw [Nat.mul_add, mul_one]; omega
          _ ≤ b ^ evalNat b f * c.val := Nat.mul_le_mul_left _ (by omega)
          _ ≤ _ := Nat.le_add_right _ _
      | eq =>
        simp only [hcd, Ordering.Compares] at hccmp
        simp only [Ordering.then]
        cases hcmpa : ONote.cmp a r <;>
          simp only [hcmpa, Ordering.Compares] at hacmp ⊢ <;>
          simp only [evalNat, hecmp, hccmp] <;> omega
termination_by t s => sizeOf t + sizeOf s
decreasing_by
  all_goals
    change _ < (1 + sizeOf e + sizeOf c + sizeOf a) + (1 + sizeOf f + sizeOf d + sizeOf r)
    omega

private theorem canonical_nf (b : ℕ) (hb : 2 ≤ b) (t : ONote)
    (ht : Canonical b t) : ONote.NF t := by
  induction t with
  | zero => exact ONote.NF.zero
  | oadd e c a ihe iha =>
    obtain ⟨he, ha, hc, htail⟩ := ht
    have hNe := ihe he
    have hNa := iha ha
    apply hNe.oadd
    cases a with
    | zero => exact ONote.NFBelow.zero
    | oadd f d r =>
      have hNf := hNa.fst
      have hcomp := (canonical_cmp b hb f e ha.1 he).eq_lt.mpr htail
      exact hNa.below_of_lt ((@ONote.cmp_compares f e hNf hNe).eq_lt.mp hcomp)

private theorem canonical_mono_base (b c : ℕ) (hb : 2 ≤ b) (hbc : b ≤ c)
    (t : ONote) (ht : Canonical b t) : Canonical c t := by
  induction t with
  | zero => trivial
  | oadd e d a ihe iha =>
    obtain ⟨he, ha, hd, htail⟩ := ht
    have he' := ihe he
    have ha' := iha ha
    refine ⟨he', ha', hd.trans_le hbc, ?_⟩
    cases a with
    | zero => trivial
    | oadd f n r =>
      have hcmp := (canonical_cmp b hb f e ha.1 he).eq_lt.mpr htail
      exact (canonical_cmp c (hb.trans hbc) f e ha'.1 he').eq_lt.mp hcmp

private theorem canonical_unique (b : ℕ) (hb : 2 ≤ b) (t s : ONote)
    (ht : Canonical b t) (hs : Canonical b s) (hval : evalNat b t = evalNat b s) : t = s := by
  exact ONote.eq_of_cmp_eq ((canonical_cmp b hb t s ht hs).eq_eq.mpr hval)

private def expansion (b m k : ℕ) : ONote :=
  (List.range k).reverse.foldr (fun e tail =>
    let digit := m / b ^ e % b
    if hd : digit = 0 then tail else
      .oadd (hereditary b e) ⟨digit, Nat.pos_of_ne_zero hd⟩ tail) .zero

private theorem expansion_succ (b m k : ℕ) :
    expansion b m (k + 1) =
      if hd : m / b ^ k % b = 0 then expansion b m k else
        .oadd (hereditary b k) ⟨m / b ^ k % b, Nat.pos_of_ne_zero hd⟩ (expansion b m k) := by
  simp [expansion, List.range_succ, List.reverse_append]

private theorem hereditary_eq_expansion (b m : ℕ) : hereditary b m = expansion b m m := by
  rw [hereditary, WellFounded.fix_eq]
  have hmap : (List.finRange m).map Fin.val = List.range m := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp
  rw [expansion, ← hmap, ← List.map_reverse, List.foldr_map]
  rfl

private theorem expansion_spec (b m : ℕ) (hb : 2 ≤ b)
    (ih : ∀ e < m, Canonical b (hereditary b e) ∧ evalNat b (hereditary b e) = e) :
    ∀ k ≤ m, Canonical b (expansion b m k) ∧
      evalNat b (expansion b m k) = m % b ^ k ∧ headBelow b (expansion b m k) k := by
  intro k
  induction k with
  | zero => intro _; simp [expansion, Canonical, evalNat, headBelow, Nat.mod_one]
  | succ k hk =>
    intro hkm
    obtain ⟨hcan, hval, hhead⟩ := hk (by omega)
    obtain ⟨he, heval⟩ := ih k (by omega)
    rw [expansion_succ]
    split_ifs with hd
    · refine ⟨hcan, ?_, ?_⟩
      · rw [Nat.mod_pow_succ, hd, mul_zero, add_zero]
        exact hval
      · cases hnote : expansion b m k with
        | zero => trivial
        | oadd e c a =>
          rw [hnote] at hhead
          exact Nat.lt_trans hhead (Nat.lt_succ_self _)
    · refine ⟨⟨he, hcan, Nat.mod_lt _ (by omega), ?_⟩, ?_, ?_⟩
      · cases hnote : expansion b m k with
        | zero => trivial
        | oadd e c a =>
          rw [hnote] at hhead
          simpa only [headBelow, heval] using hhead
      · change b ^ evalNat b (hereditary b k) * (m / b ^ k % b) + evalNat b (expansion b m k) = _
        rw [heval, hval, Nat.mod_pow_succ, Nat.add_comm]
      · change evalNat b (hereditary b k) < k + 1
        rw [heval]
        omega

/-- Hereditary expansions are the unique canonical representations of their values. -/
theorem hereditary_spec (b m : ℕ) (hb : 2 ≤ b) :
    Canonical b (hereditary b m) ∧ evalNat b (hereditary b m) = m ∧
    ONote.NF (hereditary b m) ∧
    ∀ t, Canonical b t → evalNat b t = m → t = hereditary b m := by
  have hspec : ∀ m, Canonical b (hereditary b m) ∧ evalNat b (hereditary b m) = m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      obtain ⟨hcan, hval, _⟩ := expansion_spec b m hb ih m le_rfl
      rw [hereditary_eq_expansion]
      refine ⟨hcan, ?_⟩
      rw [hval]
      exact Nat.mod_eq_of_lt (Nat.lt_pow_self (by omega))
  obtain ⟨hcan, hval⟩ := hspec m
  refine ⟨hcan, hval, canonical_nf b hb _ hcan, ?_⟩
  intro t ht htm
  exact canonical_unique b hb t _ ht hcan (htm.trans hval.symm)

/-- Base change yields the same canonical expression and preserves its ordinal measure. -/
theorem base_change_spec (b c m : ℕ) (hb : 2 ≤ b) (hbc : b < c) :
    hereditary c (baseChange b c m) = hereditary b m ∧
    ordinalMeasure c (baseChange b c m) = ordinalMeasure b m ∧
    (0 < m → 0 < baseChange b c m) := by
  obtain ⟨ht, hval, _, huniq⟩ := hereditary_spec b m hb
  have hc : 2 ≤ c := by omega
  have ht' := canonical_mono_base b c hb hbc.le _ ht
  have heq : hereditary c (baseChange b c m) = hereditary b m :=
    ((hereditary_spec c (baseChange b c m) hc).2.2.2 _ ht' rfl).symm
  refine ⟨heq, congrArg ONote.repr heq, ?_⟩
  intro hm
  cases hnote : hereditary b m with
  | zero => simp [hnote, evalNat] at hval; omega
  | oadd e d a =>
    simpa only [baseChange, hnote] using eval_positive c (by omega) e d a

/-- The ordinal measure is strictly increasing on numbers in a fixed base. -/
theorem measure_strictMono (b : ℕ) (hb : 2 ≤ b) : StrictMono (ordinalMeasure b) := by
  intro m n hmn
  obtain ⟨hm, hvm, hNm, _⟩ := hereditary_spec b m hb
  obtain ⟨hn, hvn, hNn, _⟩ := hereditary_spec b n hb
  have hcmp := (canonical_cmp b hb _ _ hm hn).eq_lt.mpr (by simpa [hvm, hvn])
  exact (@ONote.cmp_compares _ _ hNm hNn).eq_lt.mp hcmp

/-- The Goodstein sequence starting with m uses base n plus two at stage n. -/
def goodstein (m : ℕ) : ℕ → ℕ
  | 0 => m
  | n + 1 => let x := goodstein m n
           if x = 0 then 0 else baseChange (n + 2) (n + 3) x - 1

/-- A positive Goodstein term gives a strict decrease of the next ordinal measure. -/
theorem goodstein_descent (m n : ℕ) (hp : 0 < goodstein m n) :
    ordinalMeasure (n + 3) (goodstein m (n + 1)) < ordinalMeasure (n + 2) (goodstein m n) := by
  obtain ⟨_, hmeasure, hpos⟩ := base_change_spec (n + 2) (n + 3) (goodstein m n)
    (by omega) (by omega)
  have hlt := measure_strictMono (n + 3) (by omega)
    (Nat.sub_lt (hpos hp) (by omega : 0 < 1))
  rw [goodstein, ite_eq_right (Nat.ne_of_gt hp)]
  exact hlt.trans_eq hmeasure

/-- Every Goodstein sequence reaches zero. -/
theorem goodstein_termination (m : ℕ) : ∃ n, goodstein m n = 0 := by
  by_contra h
  have hpos (n : ℕ) : 0 < goodstein m n := Nat.pos_of_ne_zero (fun hn => h ⟨n, hn⟩)
  let measures (n : ℕ) := ordinalMeasure (n + 2) (goodstein m n)
  obtain ⟨a, ⟨n, rfl⟩, hmin⟩ := (wellFounded_lt (α := Ordinal.{0})).has_min
    (Set.range measures) ⟨measures 0, ⟨0, rfl⟩⟩
  exact hmin (measures (n + 1)) ⟨n + 1, rfl⟩ (goodstein_descent m n (hpos n))

end Lemmatheca.SetTheory.NormalFunctions
