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

private theorem normalForm_cons {p : Ordinal.{u} × Ordinal.{u}} {l : List (Ordinal.{u} × Ordinal.{u})}
    (h : IsNormalForm (p :: l)) :
    (∀ q ∈ l, q.1 < p.1) ∧ IsNormalForm l ∧ 0 < p.2 ∧ p.2 < ω := by
  rcases List.pairwise_cons.mp h.1 with ⟨he, ht⟩
  exact ⟨he, ⟨ht, fun q hq => h.2 q (List.mem_cons_of_mem p hq)⟩,
    h.2 p (List.mem_cons_self ..)⟩

private theorem normalForm_canonical (a : Ordinal.{u}) : IsNormalForm (CNF ω a) := by
  constructor
  · simpa only [List.sortedGT_iff_pairwise, List.pairwise_map] using (CNF.sortedGT ω a)
  · intro p hp
    exact ⟨CNF.snd_pos hp, CNF.snd_lt Ordinal.one_lt_omega0 hp⟩

private theorem eval_lt_power (l : List (Ordinal.{u} × Ordinal.{u})) (g : Ordinal.{u})
    (hl : IsNormalForm l) (he : ∀ p ∈ l, p.1 < g) : evalNormalForm l < ω ^ g := by
  induction l with
  | nil => exact opow_pos g omega0_pos
  | cons p l ih =>
    have ht := normalForm_cons hl
    exact (isPrincipal_add_omega0_opow g)
      (opow_mul_lt_opow ht.2.2.2 (he p (List.mem_cons_self ..)))
      (ih ht.2.1 (fun q hq => he q (List.mem_cons_of_mem p hq)))

private theorem cnf_eval_normalForm (l : List (Ordinal.{u} × Ordinal.{u}))
    (hl : IsNormalForm l) : CNF ω (evalNormalForm l) = l := by
  induction l with
  | nil => simp [evalNormalForm]
  | cons p l ih =>
    have ht := normalForm_cons hl
    change CNF ω (ω ^ p.1 * p.2 + evalNormalForm l) = p :: l
    rw [CNF.opow_mul_add one_lt_omega0 ht.2.2.1.ne' ht.2.2.2
      (eval_lt_power l p.1 ht.2.1 ht.1), ih ht.2.1]

private theorem eval_pos_cons (p : Ordinal.{u} × Ordinal.{u}) (l : List (Ordinal.{u} × Ordinal.{u}))
    (h : IsNormalForm (p :: l)) : 0 < evalNormalForm (p :: l) :=
  (Ordinal.opow_mul_add_pos omega0_ne_zero p.1 (normalForm_cons h).2.2.1.ne' _)

private theorem lex_eval_lt {l m : List (Ordinal.{u} × Ordinal.{u})}
    (h : List.Lex (Prod.Lex ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)
      ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)) l m)
    (hl : IsNormalForm l) (hm : IsNormalForm m) : evalNormalForm l < evalNormalForm m := by
  induction h with
  | nil => exact eval_pos_cons _ _ hm
  | @rel p l q m hpq =>
    have ht := normalForm_cons hl
    have hu := normalForm_cons hm
    simp only [Prod.lex_iff] at hpq
    rcases hpq with he | ⟨he, hc⟩
    · exact (eval_lt_power (p :: l) q.1 hl (by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact he
        · exact (ht.1 r hr).trans he)).trans_le
        ((Ordinal.le_mul_left _ hu.2.2.1).trans le_self_add)
    · change ω ^ p.1 * p.2 + evalNormalForm l < ω ^ q.1 * q.2 + evalNormalForm m
      rw [he]
      exact (opow_mul_add_lt_opow_mul
        (he ▸ eval_lt_power l p.1 ht.2.1 ht.1) hc).trans_le le_self_add
  | cons h ih =>
    change _ + evalNormalForm _ < _ + evalNormalForm _
    exact (add_lt_add_iff_left _).mpr (ih (normalForm_cons hl).2.1 (normalForm_cons hm).2.1)

theorem normalForm_characterization (a : Ordinal.{u})
    (l : List (Ordinal.{u} × Ordinal.{u})) :
    (IsNormalForm l ∧ evalNormalForm l = a) ↔ l = CNF ω a := by
  constructor
  · rintro ⟨hl, rfl⟩
    exact (cnf_eval_normalForm l hl).symm
  · rintro rfl
    exact ⟨normalForm_canonical a, CNF.foldr ω a⟩

theorem normalForm_lt_iff (l m : List (Ordinal.{u} × Ordinal.{u}))
    (hl : IsNormalForm l) (hm : IsNormalForm m) :
    evalNormalForm l < evalNormalForm m ↔
      List.Lex (Prod.Lex ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)
        ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)) l m := by
  constructor
  · intro h
    rcases trichotomous_of (List.Lex (Prod.Lex
      ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)
      ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop))) l m with hlex | heq | hlex
    · exact hlex
    · subst m; exact False.elim (lt_irrefl _ h)
    · exact False.elim ((lex_eval_lt hlex hm hl).not_gt h)
  · exact fun h => lex_eval_lt h hl hm

theorem finite_sum_lt_power (g : Ordinal.{u}) (hg : 0 < g)
    (l : List (Ordinal.{u} × ℕ)) (hl : ∀ p ∈ l, p.1 < g) :
    l.foldr (fun p r => ω ^ p.1 * (p.2 : Ordinal.{u}) + r) 0 < ω ^ g := by
  induction l with
  | nil => exact opow_pos g omega0_pos
  | cons p l ih =>
    exact (isPrincipal_add_omega0_opow g)
      (opow_mul_lt_opow (natCast_lt_omega0 p.2) (hl p (List.mem_cons_self ..)))
      (ih (fun q hq => hl q (List.mem_cons_of_mem p hq)))

theorem normalForm_example :
    CNF ω (ω ^ (2 : Ordinal.{u}) + ω + ω + 5) = [(2, 1), (1, 2), (0, 5)] ∧
    ω ^ (2 : Ordinal.{u}) + ω + ω + 5 < ω ^ (2 : Ordinal.{u}) * 2 := by
  have hv : IsNormalForm ([(2, 1), (1, 2), (0, 5)] : List (Ordinal.{u} × Ordinal.{u})) := by
    norm_num [IsNormalForm, List.pairwise_cons]; exact ⟨natCast_lt_omega0 2, natCast_lt_omega0 5⟩
  constructor
  · simpa [evalNormalForm, Ordinal.mul_two, add_assoc] using cnf_eval_normalForm _ hv
  · have ht := finite_sum_lt_power (2 : Ordinal.{u}) (by norm_num)
      [(1, 2), (0, 5)] (by simp)
    have ht' : ω * 2 + (5 : Ordinal.{u}) < ω ^ (2 : Ordinal.{u}) := by
      simpa using ht
    simpa [Ordinal.mul_two, add_assoc] using
      (opow_mul_add_lt_opow_mul (b := ω) (u := (2 : Ordinal.{u})) ht'
        (show (1 : Ordinal.{u}) < 2 by norm_num))

theorem below_omega_power_omega_iff (a : Ordinal.{u}) :
    a < ω ^ (ω : Ordinal.{u}) ↔ ∀ p ∈ CNF ω a, p.1 < ω := by
  constructor
  · intro ha p hp
    by_cases hz : a = 0
    · simp [hz] at hp
    · exact (CNF.fst_le_log hp).trans_lt ((lt_opow_iff_log_lt one_lt_omega0 hz).mp ha)
  · intro he
    simpa only [evalNormalForm, CNF.foldr] using eval_lt_power (CNF ω a) ω (normalForm_canonical a) he

theorem absorption_example :
    (ω ^ (2 : Ordinal.{u}) + ω * 3 + 7) + ω ^ (2 : Ordinal.{u}) =
      ω ^ (2 : Ordinal.{u}) * 2 := by
  have ht := finite_sum_lt_power (2 : Ordinal.{u}) (by norm_num)
    [(1, 3), (0, 7)] (by simp)
  have ht' : ω * 3 + (7 : Ordinal.{u}) < ω ^ (2 : Ordinal.{u}) := by simpa using ht
  calc
    _ = ω ^ (2 : Ordinal.{u}) + ((ω * 3 + 7) + ω ^ (2 : Ordinal.{u})) := by simp only [add_assoc]
    _ = ω ^ (2 : Ordinal.{u}) + ω ^ (2 : Ordinal.{u}) := by rw [Ordinal.add_omega0_opow ht']
    _ = _ := (Ordinal.mul_two _).symm

end Lemmatheca.Entry.OrdinalPowers
