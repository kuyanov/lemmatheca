import Lemmatheca.PaInductionAndHistories.PAInternalDefinability
import Lemmatheca.PaInductionAndHistories.PAInduction
import Lemmatheca.PaInductionAndHistories.PAFormulaDefinability
import Lemmatheca.ArithmeticRepresentability.ArithmeticRepresentabilityRecursion

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u

theorem beta_model_total {M : Type u} [language.Structure M] [M ⊨ PA]
    (x : Fin 3 → M) : ∃! y, betaGraph.Realize (extend x y) := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  let m : M := succValue M (mulValue M (succValue M (x 2)) (x 1))
  have hm : m ≠ zeroValue M := successor_ne_zero _
  obtain ⟨qr, hqr, huniq⟩ := division_model m hm (x 0)
  have hz (a : M) : (0 : M) ≤ a := zero_le_value a
  have hmone : (1 : M) ≤ m := ⟨mulValue M (succValue M (x 2)) (x 1), add_one_value _⟩
  have hqbound : leValue M qr.1 (x 0) := by
    change qr.1 ≤ x 0
    calc
      qr.1 = 1 * qr.1 := (one_mul _).symm
      _ ≤ m * qr.1 := mul_le_mul_of_nonneg_right hmone (hz _)
      _ ≤ m * qr.1 + qr.2 := le_add_of_nonneg_right (hz _)
      _ = x 0 := hqr.1.symm
  have hgraph (y : M) : betaGraph.Realize (extend x y) ↔
      leValue M (succValue M y) m ∧ ∃ q, leValue M q (x 0) ∧
        x 0 = addValue M (mulValue M m q) y := by
    simp only [betaGraph, realize_betaFormula, Term.realize_var, extend,
      Sum.elim_inl, Sum.elim_inr, betaModulusTerm, realize_succTerm, realize_mulTerm]
    rfl
  refine ⟨qr.2, (hgraph _).mpr ⟨hqr.2, qr.1, hqbound, hqr.1⟩, ?_⟩
  intro y hy
  obtain ⟨hr, q, _, he⟩ := (hgraph y).mp hy
  exact congrArg Prod.snd (huniq (q, y) ⟨he, hr⟩)

def betaValue {M : Type u} [language.Structure M] [M ⊨ PA] (x : Fin 3 → M) : M :=
  Classical.choose (beta_model_total x)

theorem betaValue_graph {M : Type u} [language.Structure M] [M ⊨ PA] (x : Fin 3 → M) :
    betaGraph.Realize (extend x (betaValue x)) := (Classical.choose_spec (beta_model_total x)).1

theorem betaValue_iff {M : Type u} [language.Structure M] [M ⊨ PA]
    (x : Fin 3 → M) (y : M) :
    betaGraph.Realize (extend x y) ↔ y = betaValue x := by
  exact ⟨fun h => (Classical.choose_spec (beta_model_total x)).2 y h,
    fun h => h.symm ▸ betaValue_graph x⟩

@[fun_prop] theorem df_beta {M : Type u} [language.Structure M] [M ⊨ PA]
    {α : Type} [Finite α] (f g h : (α → M) → M)
    (hf : Set.univ.DefinableFun language f) (hg : Set.univ.DefinableFun language g)
    (hh : Set.univ.DefinableFun language h) :
    Set.univ.DefinableFun language (fun v => betaValue ![f v, g v, h v]) := by
  have hb : (∅ : Set M).DefinableFun language (betaValue : (Fin 3 → M) → M) := by
    rw [Set.empty_definableFun_iff]
    refine ⟨betaGraph.relabel (Sum.elim some (fun _ => none)), ?_⟩
    ext v
    simp only [Function.tupleGraph, Set.mem_ofPred_eq, Formula.realize_relabel]
    have he : v ∘ Sum.elim some (fun _ : Unit => none) = extend (v ∘ some) (v none) := by
      funext i
      cases i <;> rfl
    rw [he, betaValue_iff]
    exact eq_comm
  exact (hb.mono (Set.empty_subset _)).comp (fun i => by
    fin_cases i
    · exact hf
    · exact hg
    · exact hh)

@[fun_prop] theorem df_betaModulus {M : Type u} [language.Structure M]
    {α : Type} [Finite α] (f g : (α → M) → M)
    (hf : Set.univ.DefinableFun language f) (hg : Set.univ.DefinableFun language g) :
    Set.univ.DefinableFun language (fun v => succValue M (mulValue M (succValue M (g v)) (f v))) := by
  fun_prop

def betaModulusValue (M : Type u) [language.Structure M] (d i : M) : M :=
  succValue M (mulValue M (succValue M i) d)

@[fun_prop] theorem df_modulus {M : Type u} [language.Structure M]
    {α : Type} [Finite α] (f g : (α → M) → M)
    (hf : Set.univ.DefinableFun language f) (hg : Set.univ.DefinableFun language g) :
    Set.univ.DefinableFun language (fun v => betaModulusValue M (f v) (g v)) := by
  exact df_betaModulus f g hf hg

private def prescribedValue {M : Type u} [language.Structure M] [M ⊨ PA]
    (c d n a i : M) : M := by
  classical
  exact if i = n then a else betaValue ![c, d, i]

@[fun_prop] private theorem df_prescribed {M : Type u} [language.Structure M] [M ⊨ PA]
    {α : Type} [Finite α] (c d n a : M) (f : (α → M) → M)
    (hf : Set.univ.DefinableFun language f) :
    Set.univ.DefinableFun language (fun v => prescribedValue c d n a (f v)) := by
  classical
  apply Set.DefinableFun.ite
  · exact dp_eq _ _ hf (df_const n)
  · exact df_const a
  · exact df_beta _ _ _ (df_const c) (df_const d) hf

theorem betaValue_equation {M : Type u} [language.Structure M] [M ⊨ PA] (c d i : M) :
    leValue M (succValue M (betaValue ![c, d, i])) (betaModulusValue M d i) ∧
      ∃ q, leValue M q c ∧
        c = addValue M (mulValue M (betaModulusValue M d i) q) (betaValue ![c, d, i]) := by
  have h := betaValue_graph ![c, d, i]
  rw [betaGraph, realize_betaFormula] at h
  simpa [betaModulusValue, betaModulusTerm, extend] using h

theorem betaValue_le {M : Type u} [language.Structure M] [M ⊨ PA] (c d i : M) :
    leValue M (betaValue ![c, d, i]) c := by
  obtain ⟨_, q, _, hq⟩ := betaValue_equation c d i
  exact ⟨mulValue M (betaModulusValue M d i) q, hq.symm⟩

theorem betaValue_of_remainder {M : Type u} [language.Structure M] [M ⊨ PA]
    (c d i a q : M) (ha : leValue M (succValue M a) (betaModulusValue M d i))
    (he : c = addValue M (mulValue M (betaModulusValue M d i) q) a) :
    betaValue ![c, d, i] = a := by
  obtain ⟨hb, r, _, hr⟩ := betaValue_equation c d i
  obtain ⟨qr, _, huniq⟩ := division_model (betaModulusValue M d i) (successor_ne_zero _) c
  exact congrArg Prod.snd ((huniq (r, _) ⟨hr, hb⟩).trans (huniq (q, a) ⟨he, ha⟩).symm)

theorem betaValue_of_congruence {M : Type u} [language.Structure M] [M ⊨ PA]
    (c C d i u v : M)
    (h : addValue M c (mulValue M (betaModulusValue M d i) u) =
      addValue M C (mulValue M (betaModulusValue M d i) v)) :
    betaValue ![c, d, i] = betaValue ![C, d, i] := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  let m := betaModulusValue M d i
  obtain ⟨hc, q, _, he⟩ := betaValue_equation c d i
  obtain ⟨hC, Q, _, hE⟩ := betaValue_equation C d i
  change c = m * q + betaValue ![c, d, i] at he
  change C = m * Q + betaValue ![C, d, i] at hE
  change c + m * u = C + m * v at h
  obtain ⟨qr, _, huniq⟩ := division_model m (successor_ne_zero _) (c + m * u)
  have h₁ : (q + u, betaValue ![c, d, i]) = qr := huniq _ ⟨by
    change c + m * u = m * (q + u) + betaValue ![c, d, i]
    calc
      _ = (m * q + betaValue ![c, d, i]) + m * u := congrArg (fun z => z + m * u) he
      _ = _ := by ring, hc⟩
  have h₂ : (Q + v, betaValue ![C, d, i]) = qr := huniq _ ⟨by
    change c + m * u = m * (Q + v) + betaValue ![C, d, i]
    calc
      _ = C + m * v := h
      _ = (m * Q + betaValue ![C, d, i]) + m * v := congrArg (fun z => z + m * v) hE
      _ = _ := by ring, hC⟩
  exact congrArg Prod.snd (h₁.trans h₂.symm)

private def betaCRTInvariant {M : Type u} [language.Structure M] [M ⊨ PA]
    (c d n a d' k : M) : Prop :=
  ∃ s p, p ≠ zeroValue M ∧
    (∀ i, leValue M (succValue M i) k →
      betaValue ![s, d', i] = prescribedValue c d n a i) ∧
    (∀ i, leValue M (succValue M i) k → DividesModel M (betaModulusValue M d' i) p) ∧
    (∀ j, leValue M k j → leValue M j n → CoprimeModel M p (betaModulusValue M d' j))

private theorem betaCRTInvariant_definable {M : Type u} [language.Structure M] [M ⊨ PA]
    (c d n a d' : M) :
    Set.univ.Definable₁ language {k | leValue M k (succValue M n) → betaCRTInvariant c d n a d' k} := by
  change DPred (fun v : Fin 1 → M =>
    leValue M (v 0) (succValue M n) → betaCRTInvariant c d n a d' (v 0))
  dsimp only [betaCRTInvariant]
  pa_definable

theorem betaModulus_pairwise_model {M : Type u} [language.Structure M] [M ⊨ PA]
    (d n : M)
    (hD : ∀ t, t ≠ zeroValue M → leValue M t (succValue M n) → DividesModel M t d)
    (i j : M) (hi : leValue M i n) (hj : leValue M j n) (hne : i ≠ j) :
    CoprimeModel M (betaModulusValue M d i) (betaModulusValue M d j) := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have hs (a : M) : succValue M a = a + 1 := (add_one_value a).symm
  have forward (i j : M) (hij : leValue M (succValue M i) j) (hjn : leValue M j n) :
      CoprimeModel M (betaModulusValue M d i) (betaModulusValue M d j) := by
    obtain ⟨e, he⟩ := hij
    let δ := succValue M e
    have hδ : addValue M δ i = j := by
      rw [successor_add_value]
      simpa only [add_successor_value] using he
    have hδj : leValue M δ j := ⟨i, (add_comm_value _ _).trans hδ⟩
    have hδn : leValue M δ (succValue M n) :=
      le_trans_value (le_trans_value hδj hjn) (le_successor_value n)
    have hδd := hD δ (successor_ne_zero e) hδn
    intro r hri hrj
    have hcop : CoprimeModel M (betaModulusValue M d i) d :=
      coprime_succ_multiple_model d i
    have hrd : CoprimeModel M r d := by
      intro z hzr hzd
      exact hcop z (divides_trans_model hzr hri) hzd
    obtain ⟨qi, hqi⟩ := hri
    obtain ⟨qj, hqj⟩ := hrj
    have hr0 : r ≠ zeroValue M := by
      intro hr0
      have he0 : zeroValue M = betaModulusValue M d i := by
        simpa only [hr0, zero_mul_value] using hqi
      exact successor_ne_zero _ he0.symm
    have hdiff : DividesModel M r (mulValue M δ d) := by
      apply quotient_of_difference r qj qi (mulValue M δ d) hr0
      change r * qj = δ * d + r * qi
      calc
        _ = betaModulusValue M d j := hqj
        _ = betaModulusValue M d i + δ * d := by
          dsimp only [betaModulusValue]
          simp only [hs]
          change (j + 1) * d + 1 = ((i + 1) * d + 1) + δ * d
          change δ + i = j at hδ
          rw [← hδ]
          ring
        _ = δ * d + r * qi := by
          change r * qi = betaModulusValue M d i at hqi
          rw [← hqi]
          ring
    have hrδ : DividesModel M r δ := by
      apply coprime_cancellation_model r d δ hrd
      simpa only [mul_comm_value] using hdiff
    exact hcop r ⟨qi, hqi⟩ (divides_trans_model hrδ hδd)
  by_cases hij : leValue M (succValue M i) j
  · exact forward i j hij hj
  · have hji : leValue M (succValue M j) i := by
      apply (successor_le_iff_lt j i).mpr
      refine ⟨?_, ?_⟩
      · rcases le_or_successor_le j i with h | h
        · exact h
        · exact (hij h).elim
      · intro hij'
        have he : i = j := le_antisymm_value hij' (by
          rcases le_or_successor_le j i with h | h
          · exact h
          · exact (hij h).elim)
        exact hne he
    intro r hrj hri
    exact forward j i hji hi r hri hrj

private theorem beta_bounded_crt {M : Type u} [language.Structure M] [M ⊨ PA]
    (c d n a d' : M)
    (hD : ∀ t, t ≠ zeroValue M → leValue M t (succValue M n) → DividesModel M t d')
    (hbound : ∀ i, leValue M i n →
      leValue M (succValue M (prescribedValue c d n a i)) (betaModulusValue M d' i)) :
    ∃ s, ∀ i, leValue M i n → betaValue ![s, d', i] = prescribedValue c d n a i := by
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  have cancel (i k : M) (h : leValue M (succValue M i) (succValue M k)) :
      leValue M i k := by
    obtain ⟨w, hw⟩ := h
    exact ⟨w, successor_injective (by simpa only [add_successor_value] using hw)⟩
  have mono (i k : M) (h : leValue M i k) :
      leValue M (succValue M i) (succValue M k) := by
    obtain ⟨w, hw⟩ := h
    exact ⟨w, by rw [add_successor_value, hw]⟩
  have split (i k : M) (h : leValue M (succValue M i) (succValue M k)) :
      leValue M (succValue M i) k ∨ i = k := by
    rcases le_or_successor_le (succValue M i) k with h₁ | h₁
    · exact Or.inl h₁
    · have hi := cancel i k h
      have hk := cancel k i h₁
      exact Or.inr (le_antisymm_value hi hk)
  let P (k : M) := leValue M k (succValue M n) → betaCRTInvariant c d n a d' k
  have hall : ∀ k, P k := by
    apply definable_induction P (betaCRTInvariant_definable c d n a d')
    · intro _
      refine ⟨zeroValue M, numeralValue M 1, ?_, ?_, ?_, ?_⟩
      · rw [numeral_value_succ, numeral_value_zero]
        exact successor_ne_zero _
      · intro i hi
        exact (successor_ne_zero i (le_antisymm_value hi (zero_le_value _))).elim
      · intro i hi
        exact (successor_ne_zero i (le_antisymm_value hi (zero_le_value _))).elim
      · intro j _ _ r hr _
        exact divisor_of_one_model r hr
    · intro k hk hknext
      have hkn := cancel k n hknext
      obtain ⟨s, p, hp, hvalues, hdiv, hcop⟩ := hk (le_trans_value hkn (le_successor_value n))
      obtain ⟨qr, hqr, _⟩ := division_model p hp s
      obtain ⟨S, q, r, hSp, hSm⟩ := two_modulus_model p (betaModulusValue M d' k)
        qr.2 (prescribedValue c d n a k) hp (successor_ne_zero _)
        (hcop k (le_refl_value k) hkn) hqr.2 (hbound k hkn)
      have hcong : S + p * qr.1 = s + p * q := by
        change S = p * q + qr.2 at hSp
        have hs : s = p * qr.1 + qr.2 := hqr.1
        rw [hSp, hs]
        ring
      have hpreserve (i : M) (hi : leValue M (succValue M i) k) :
          betaValue ![S, d', i] = betaValue ![s, d', i] := by
        obtain ⟨t, ht⟩ := hdiv i hi
        apply betaValue_of_congruence S s d' i (t * qr.1) (t * q)
        change betaModulusValue M d' i * t = p at ht
        change S + betaModulusValue M d' i * (t * qr.1) =
          s + betaModulusValue M d' i * (t * q)
        simpa only [← ht, mul_assoc] using hcong
      refine ⟨S, mulValue M p (betaModulusValue M d' k),
        mul_ne_zero_value hp (successor_ne_zero _), ?_, ?_, ?_⟩
      · intro i hi
        rcases split i k hi with hiold | hieq
        · exact (hpreserve i hiold).trans (hvalues i hiold)
        · subst i
          exact betaValue_of_remainder S d' k _ r (hbound k hkn) hSm
      · intro i hi
        rcases split i k hi with hiold | hieq
        · obtain ⟨t, ht⟩ := hdiv i hiold
          exact ⟨mulValue M t (betaModulusValue M d' k), by rw [← mul_assoc_value, ht]⟩
        · subst i
          exact ⟨p, mul_comm_value _ _⟩
      · intro j hkj hjn
        have hkp := hcop j (le_trans_value (le_successor_value k) hkj) hjn
        have hneq : k ≠ j := by
          intro he
          subst j
          exact (successor_le_iff_lt k k).mp hkj |>.2 (le_refl_value k)
        have hkm := betaModulus_pairwise_model d' n hD k j hkn hjn hneq
        intro z hzProduct hzj
        exact coprime_product_model (betaModulusValue M d' j) p (betaModulusValue M d' k)
          (fun z hzj hzp => hkp z hzp hzj) (fun z hzj hzk => hkm z hzk hzj)
          z hzj hzProduct
  obtain ⟨s, _, _, hs, _, _⟩ := hall (succValue M n) (le_refl_value _)
  exact ⟨s, fun i hi => hs i (mono i n hi)⟩

theorem beta_extension_value {M : Type u} [language.Structure M] [M ⊨ PA]
    (c d n a : M) :
    ∃ c' d', betaValue ![c', d', n] = a ∧
      ∀ i, leValue M (succValue M i) n → betaValue ![c', d', i] = betaValue ![c, d, i] := by
  classical
  let := modelSemiring M
  let := modelLinearOrder M
  let := modelOrderedAdd M
  let := modelStrictOrderedRing M
  obtain ⟨D, hD0, hD⟩ := common_multiple_model (succValue M n)
  let L := succValue M (addValue M c a)
  let d' := mulValue M D L
  have hdiv (t : M) (ht : t ≠ zeroValue M) (htn : leValue M t (succValue M n)) :
      DividesModel M t d' :=
    divides_trans_model (hD t ht htn) ⟨L, rfl⟩
  have hDL : L ≤ d' := calc
    L = 1 * L := (one_mul _).symm
    _ ≤ D * L := by
      apply mul_le_mul_of_nonneg_right _ (zero_le_value _)
      change leValue M (succValue M (zeroValue M)) D
      have h := one_le_nonzero_model D hD0
      rw [numeral_value_succ, numeral_value_zero] at h
      exact h
  have hsum : c + a < L :=
    (successor_le_iff_lt (addValue M c a) L).mp (le_refl_value L)
  have hcD : c < d' := lt_of_lt_of_le
    (lt_of_le_of_lt (le_add_of_nonneg_right (zero_le_value a)) hsum) hDL
  have haD : a < d' := lt_of_lt_of_le
    (lt_of_le_of_lt (le_add_of_nonneg_left (zero_le_value c)) hsum) hDL
  have hmod (i : M) : d' < betaModulusValue M d' i := by
    have hle : d' ≤ mulValue M (succValue M i) d' := calc
      d' = 1 * d' := (one_mul _).symm
      _ ≤ succValue M i * d' := mul_le_mul_of_nonneg_right
        (show (1 : M) ≤ succValue M i from ⟨i, add_one_value i⟩) (zero_le_value _)
    exact lt_of_le_of_lt hle
      ((successor_le_iff_lt _ _).mp (le_refl_value (betaModulusValue M d' i)))
  have hbound (i : M) (_ : leValue M i n) :
      leValue M (succValue M (prescribedValue c d n a i)) (betaModulusValue M d' i) := by
    apply (successor_le_iff_lt _ _).mpr
    by_cases hi : i = n
    · subst i
      rw [(show prescribedValue c d n a n = a from by simp [prescribedValue])]
      change a < betaModulusValue M d' n
      exact lt_trans haD (hmod n)
    · have hb : betaValue ![c, d, i] < betaModulusValue M d' i :=
        lt_of_le_of_lt (betaValue_le c d i) (lt_trans hcD (hmod i))
      rw [(show prescribedValue c d n a i = betaValue ![c, d, i] from by simp [prescribedValue, hi])]
      change betaValue ![c, d, i] < betaModulusValue M d' i
      exact hb
  obtain ⟨s, hs⟩ := beta_bounded_crt c d n a d' hdiv hbound
  refine ⟨s, d', ?_, ?_⟩
  · simpa only [prescribedValue, ↓reduceIte] using hs n (le_refl_value n)
  · intro i hi
    have hin : leValue M i n := le_trans_value (le_successor_value i) hi
    have hine : i ≠ n := by
      intro he
      subst i
      exact (successor_le_iff_lt n n).mp hi |>.2 (le_refl_value n)
    simpa only [prescribedValue, hine, ↓reduceIte] using hs i hin

end
end Lemmatheca.ProofTheory.PAComputations
