import Lemmatheca.ArithmeticalHierarchy.FirstLevel
import Lemmatheca.ArithmeticDefinability.ArithmeticDefinability

/-! The positive-level bridge uses the actual shared arithmetic formula syntax. -/
namespace Lemmatheca.ComputabilityTheory.ArithmeticalHierarchy

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.ArithmeticTheories

/-- A one-variable prefix, binding first-choice variables before later choices. -/
noncomputable def bindPrefix : {α : Type} → (n : ℕ) → Bool → language.Formula (α ⊕ Fin n) →
    language.Formula α
  | _, 0, _, D => D.relabel (Sum.elim id Fin.elim0)
  | α, n + 1, p, D =>
      let shift : α ⊕ Fin (n + 1) → (α ⊕ Fin 1) ⊕ Fin n :=
        Sum.elim (fun i => .inl (.inl i)) (Fin.cases (.inl (.inr 0)) (fun i => .inr i))
      let inner := bindPrefix n (!p) (D.relabel shift)
      if p then inner.iExs (Fin 1) else inner.iAlls (Fin 1)

def lastPolarity (n : ℕ) (p : Bool) : Bool := if n % 2 = 1 then p else !p

private theorem prefix_assignment {α : Type} (n : ℕ) (x : α → ℕ)
    (v : Fin 1 → ℕ) (w : Fin n → ℕ) :
    (Sum.elim (Sum.elim x v) w) ∘
      (Sum.elim (fun i : α => .inl (.inl i))
        (Fin.cases (.inl (.inr 0)) (fun i => .inr i))) =
      Sum.elim x (Fin.cons (v 0) w) := by
  funext i
  cases i with
  | inl a => rfl
  | inr i => exact Fin.cases rfl (fun _ => rfl) i

theorem bindPrefix_realize {α : Type} (n : ℕ) (p : Bool)
    (D : language.Formula (α ⊕ Fin n)) (x : α → ℕ) :
    (bindPrefix n p D).Realize x ↔ quantify n p (fun y => D.Realize (Sum.elim x y)) := by
  classical
  induction n generalizing α p with
  | zero =>
      simp only [bindPrefix, Formula.realize_relabel, quantify]
      have he : x ∘ Sum.elim id Fin.elim0 = Sum.elim x Fin.elim0 := by
        funext i
        cases i with
        | inl a => rfl
        | inr i => exact Fin.elim0 i
      rw [he]
  | succ n ih =>
      cases p <;> simp only [bindPrefix, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, Formula.realize_iAlls, Formula.realize_iExs,
        quantify]
      · simp_rw [ih, Formula.realize_relabel, prefix_assignment]
        constructor
        · intro h y
          exact h (fun _ => y)
        · intro h v
          exact h (v 0)
      · simp_rw [ih, Formula.realize_relabel, prefix_assignment]
        constructor
        · rintro ⟨v, hv⟩
          exact ⟨v 0, hv⟩
        · rintro ⟨y, hy⟩
          exact ⟨fun _ => y, hy⟩

theorem bindPrefix_bounded {α : Type} (n : ℕ) (p : Bool)
    (D : language.Formula (α ⊕ Fin n))
    (hD : Lemmatheca.ProofTheory.ArithmeticRepresentability.BoundedArithmetic D) :
    ArithmeticDefinability.Prefix n p (bindPrefix n p D) := by
  induction n generalizing α p with
  | zero => exact hD.relabel _
  | succ n ih =>
      cases p <;> exact ⟨1, _, ih _ _ (hD.relabel _), rfl⟩

open Lemmatheca.ProofTheory.ArithmeticRepresentability
open Lemmatheca.MathematicalLogic.FirstOrderProofs

private theorem prefix_subst {α β : Type} (n : ℕ) (p : Bool)
    {D : language.Formula α} (hD : ArithmeticDefinability.Prefix n p D)
    (σ : α → language.Term β) : ArithmeticDefinability.Prefix n p (D.subst σ) := by
  induction n generalizing α β p with
  | zero => exact hD.subst σ
  | succ n ih =>
      cases p
      · obtain ⟨k, E, hE, rfl⟩ := hD
        rw [subst_iAlls]
        exact ⟨k, _, ih _ hE _, rfl⟩
      · obtain ⟨k, E, hE, rfl⟩ := hD
        rw [subst_iExs]
        exact ⟨k, _, ih _ hE _, rfl⟩

private theorem prefix_relabel {α β : Type} (n : ℕ) (p : Bool)
    {D : language.Formula α} (hD : ArithmeticDefinability.Prefix n p D)
    (f : α → β) : ArithmeticDefinability.Prefix n p (D.relabel f) := by
  rw [← formula_subst_vars]
  exact prefix_subst n p hD _

private def partialExs {α : Type} (m : ℕ) :
    (n : ℕ) → language.BoundedFormula α (m + n) → language.BoundedFormula α m
  | 0, φ => φ
  | n + 1, φ => partialExs m n φ.ex

private def partialAlls {α : Type} (m : ℕ) :
    (n : ℕ) → language.BoundedFormula α (m + n) → language.BoundedFormula α m
  | 0, φ => φ
  | n + 1, φ => partialAlls m n φ.all

private theorem exs_partialExs {α : Type} (m n : ℕ)
    (φ : language.BoundedFormula α (m + n)) :
    (partialExs m n φ).exs = φ.exs := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih φ.ex

private theorem alls_partialAlls {α : Type} (m n : ℕ)
    (φ : language.BoundedFormula α (m + n)) :
    (partialAlls m n φ).alls = φ.alls := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih φ.all

private theorem relabel_exs {α β : Type} {m n : ℕ}
    (φ : language.BoundedFormula α n) (f : α → β ⊕ Fin m) :
    BoundedFormula.relabel f φ.exs = partialExs m n (φ.relabel f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [BoundedFormula.exs, ih, BoundedFormula.relabel_ex, partialExs]

private theorem relabel_alls {α β : Type} {m n : ℕ}
    (φ : language.BoundedFormula α n) (f : α → β ⊕ Fin m) :
    BoundedFormula.relabel f φ.alls = partialAlls m n (φ.relabel f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [BoundedFormula.alls, ih, BoundedFormula.relabel_all, partialAlls]

private theorem raw_matrix {α : Type} {n m : ℕ}
    (φ : language.BoundedFormula α n) (hφ : BoundedArithmetic φ.toFormula)
    (e : Fin n ≃ Fin m) (hm : m = n) :
    ∃ δ : language.Formula (α ⊕ Fin n), BoundedArithmetic δ ∧
      (BoundedFormula.relabel (Sum.map id e) δ).exs = φ.exs ∧
      (BoundedFormula.relabel (Sum.map id e) δ).alls = φ.alls := by
  subst m
  let f : α ⊕ Fin n → α ⊕ Fin n := Sum.map id e.symm
  let f₀ : α ⊕ Fin n → (α ⊕ Fin n) ⊕ Fin 0 := Sum.inl ∘ f
  refine ⟨φ.toFormula.relabel f, hφ.relabel f, ?_⟩
  have hh := bounded_relabel_comp (m := 0) (n := n) φ.toFormula f₀ (Sum.map id e)
  simp only [BoundedFormula.castLE_rfl] at hh
  have hf : BoundedFormula.relabelAux (Sum.map id e) 0 ∘ f₀ =
      (id : α ⊕ Fin n → α ⊕ Fin n) := by
    funext x
    cases x with
    | inl x => rfl
    | inr i =>
      simp [f₀, f, BoundedFormula.relabelAux]
      exact Fin.ext rfl
  rw [hf, relabel_toFormula] at hh
  exact ⟨congrArg BoundedFormula.exs hh, congrArg BoundedFormula.alls hh⟩

private theorem prefix_one_raw {α : Type} {n : ℕ} (p : Bool)
    (φ : language.BoundedFormula α n) (hφ : BoundedArithmetic φ.toFormula) :
    ArithmeticDefinability.Prefix 1 p (if p then φ.exs else φ.alls) := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin (Fin n)))
  have hm : Classical.choose (Finite.exists_equiv_fin (Fin n)) = n := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr e).symm
  obtain ⟨δ, hδ, heq, hall⟩ := raw_matrix φ hφ e hm
  cases p
  · exact ⟨n, δ, hδ, hall.symm⟩
  · exact ⟨n, δ, hδ, heq.symm⟩

private theorem prefix_one_iQuantify {α β : Type} [Finite β] (p : Bool)
    {D : language.Formula (α ⊕ β)} (hD : ArithmeticDefinability.Prefix 1 p D) :
    ArithmeticDefinability.Prefix 1 p (if p then D.iExs β else D.iAlls β) := by
  classical
  cases p
  · obtain ⟨k, E, hE, rfl⟩ := hD
    change ArithmeticDefinability.Prefix 1 false ((E.iAlls (Fin k)).iAlls β)
    unfold Formula.iAlls
    dsimp only
    rw [relabel_alls]
    rw [alls_partialAlls (Classical.choose (Finite.exists_equiv_fin β))
      (Classical.choose (Finite.exists_equiv_fin (Fin k)) + 0)]
    apply prefix_one_raw false
    rw [toFormula_relabel, toFormula_relabel, toFormula_zero]
    exact ((hE.relabel _).relabel _).relabel _
  · obtain ⟨k, E, hE, rfl⟩ := hD
    change ArithmeticDefinability.Prefix 1 true ((E.iExs (Fin k)).iExs β)
    unfold Formula.iExs
    dsimp only
    rw [relabel_exs]
    rw [exs_partialExs (Classical.choose (Finite.exists_equiv_fin β))
      (Classical.choose (Finite.exists_equiv_fin (Fin k)) + 0)]
    apply prefix_one_raw true
    rw [toFormula_relabel, toFormula_relabel, toFormula_zero]
    exact ((hE.relabel _).relabel _).relabel _

private theorem lastPolarity_step (n : ℕ) (p : Bool) :
    lastPolarity (n + 2) p = lastPolarity (n + 1) (!p) := by
  by_cases h : (n + 2) % 2 = 1
  · have hn : (n + 1) % 2 ≠ 1 := by omega
    unfold lastPolarity
    rw [ite_eq_left h, ite_eq_right hn]
    exact (Bool.not_not p).symm
  · have hn : (n + 1) % 2 = 1 := by omega
    unfold lastPolarity
    rw [ite_eq_right h, ite_eq_left hn]

theorem bindPrefix_absorb {α : Type} (n : ℕ) (hn : 0 < n) (p : Bool)
    (D : language.Formula (α ⊕ Fin n))
    (hD : ArithmeticDefinability.Prefix 1 (lastPolarity n p) D) :
    ArithmeticDefinability.Prefix n p (bindPrefix n p D) := by
  induction n generalizing α p with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          dsimp only [bindPrefix]
          apply prefix_one_iQuantify p
          apply prefix_relabel 1 p
          apply prefix_relabel 1 p
          simpa only [lastPolarity, Nat.one_mod, ↓reduceIte] using hD
      | succ n =>
          let shift : α ⊕ Fin (n + 1 + 1) → (α ⊕ Fin 1) ⊕ Fin (n + 1) :=
            Sum.elim (fun i => .inl (.inl i))
              (Fin.cases (.inl (.inr 0)) (fun i => .inr i))
          have he : ArithmeticDefinability.Prefix 1
              (lastPolarity (n + 1) (!p)) (D.relabel shift) := by
            rw [← lastPolarity_step]
            exact prefix_relabel 1 _ hD shift
          have hi := ih (by omega) (!p) (D.relabel shift) he
          cases p <;> exact ⟨1, _, hi, rfl⟩

private theorem level_of_iff (A : Set ℕ) (n : ℕ) (p : Bool) {P Q : ℕ → Prop}
    (h : ∀ x, P x ↔ Q x) (hP : Level A n p P) : Level A n p Q := by
  obtain ⟨R, hR, hp⟩ := hP
  exact ⟨R, hR, fun x => (h x).symm.trans (hp x)⟩

private theorem prefix_semantic_level {α : Type} (n : ℕ) (p : Bool)
    {D : language.Formula α} (hD : ArithmeticDefinability.Prefix n p D)
    (v : ℕ → α → ℕ) (hv : ∀ i, Primrec (fun c => v c i)) :
    Level ∅ n p (fun c => D.Realize (v c)) := by
  classical
  induction n generalizing α p with
  | zero =>
      apply (level_zero_iff ∅ p _).mpr
      obtain ⟨d, hd⟩ := ArithmeticDefinability.bounded_truth_primitive hD v hv
      have hc : ComputablePred (fun c => D.Realize (v c)) := ⟨d, hd.to_comp⟩
      obtain ⟨r, _, hr⟩ := TuringDegrees.computable_uniform {c | D.Realize (v c)} hc
      exact ⟨OracleComputation.embed r, funext (hr ∅)⟩
  | succ n ih =>
      cases p
      · obtain ⟨k, E, hE, rfl⟩ := hD
        let R (c u : ℕ) : Prop := E.Realize (Sum.elim (v c) (tupleDecode k u))
        have hR : Sigma ∅ n (fun w => R w.unpair.1 w.unpair.2) := by
          apply ih true hE (fun w => Sum.elim (v w.unpair.1) (tupleDecode k w.unpair.2))
          intro i
          cases i with
          | inl a => exact (hv a).comp (Primrec.fst.comp Primrec.unpair)
          | inr i =>
              exact FiniteSequenceCoding.primrec_entry.comp
                (Primrec.snd.comp Primrec.unpair) (Primrec.const i.val)
        apply (pi_succ_iff ∅ n _).mpr
        refine ⟨R, hR, ?_⟩
        intro c
        rw [Formula.realize_iAlls]
        constructor
        · intro h u
          exact h (tupleDecode k u)
        · intro h w
          obtain ⟨u, rfl⟩ := tuple_decode_surjective k w
          exact h u
      · obtain ⟨k, E, hE, rfl⟩ := hD
        let R (c u : ℕ) : Prop := E.Realize (Sum.elim (v c) (tupleDecode k u))
        have hR : Pi ∅ n (fun w => R w.unpair.1 w.unpair.2) := by
          apply ih false hE (fun w => Sum.elim (v w.unpair.1) (tupleDecode k w.unpair.2))
          intro i
          cases i with
          | inl a => exact (hv a).comp (Primrec.fst.comp Primrec.unpair)
          | inr i =>
              exact FiniteSequenceCoding.primrec_entry.comp
                (Primrec.snd.comp Primrec.unpair) (Primrec.const i.val)
        apply (sigma_succ_iff ∅ n _).mpr
        refine ⟨R, hR, ?_⟩
        intro c
        rw [Formula.realize_iExs]
        constructor
        · rintro ⟨w, hw⟩
          obtain ⟨u, rfl⟩ := tuple_decode_surjective k w
          exact ⟨u, hw⟩
        · rintro ⟨u, hu⟩
          exact ⟨tupleDecode k u, hu⟩

private theorem quantify_congr (n : ℕ) (p : Bool) (R S : Tuple n → Prop)
    (h : ∀ v, R v ↔ S v) : quantify n p R ↔ quantify n p S := by
  induction n generalizing p with
  | zero => exact h Fin.elim0
  | succ n ih =>
      cases p
      · exact forall_congr' (fun y => ih true _ _ (fun w => h (Fin.cons y w)))
      · exact exists_congr (fun y => ih false _ _ (fun w => h (Fin.cons y w)))

theorem arithmetic_prefix_to_level (n : ℕ) (p : Bool) {k : ℕ} (P : Tuple k → Prop)
    (hP : ArithmeticDefinability.PrefixDefinable n p P) : FiniteLevel ∅ n p P := by
  obtain ⟨D, hD, hd⟩ := hP
  apply level_of_iff ∅ n p (fun c => hd (tupleDecode k c))
  apply prefix_semantic_level n p hD (tupleDecode k)
  intro i
  exact FiniteSequenceCoding.primrec_entry.comp Primrec.id (Primrec.const i.val)

theorem positive_level_arithmetic_iff (n : ℕ) (hn : 0 < n) (p : Bool) {k : ℕ}
    (P : Tuple k → Prop) :
    FiniteLevel ∅ n p P ↔ ArithmeticDefinability.PrefixDefinable n p P := by
  classical
  constructor
  · intro hP
    obtain ⟨R, hR, hp⟩ := (finite_matrix_normal_form ∅ n p P).mp hP
    have hc : ComputablePred R := (finite_decidable_empty_iff R).mp hR
    obtain ⟨hs, hu⟩ := (ArithmeticDefinability.decidable_iff_deltaOne R).mp hc
    have hm : ∃ D : language.Formula (Fin (k + n)),
        ArithmeticDefinability.Prefix 1 (lastPolarity n p) D ∧
          ArithmeticDefinability.Defines R D := by
      cases lastPolarity n p
      · exact hu
      · exact hs
    obtain ⟨D, hD, hd⟩ := hm
    let f : Fin (k + n) → Fin k ⊕ Fin n := finSumFinEquiv.symm
    let E := D.relabel f
    have he : ArithmeticDefinability.Prefix 1 (lastPolarity n p) E :=
      prefix_relabel 1 _ hD f
    refine ⟨bindPrefix n p E, bindPrefix_absorb n hn p E he, ?_⟩
    intro x
    calc
      (bindPrefix n p E).Realize x ↔
          quantify n p (fun y => E.Realize (Sum.elim x y)) := bindPrefix_realize n p E x
      _ ↔ quantify n p (fun y => R (appendTuple x y)) := by
        apply quantify_congr
        intro y
        change (D.relabel f).Realize (Sum.elim x y) ↔ _
        rw [Formula.realize_relabel]
        have hf : Sum.elim x y ∘ f = appendTuple x y := by
          funext i
          cases i using Fin.addCases <;> simp [f, appendTuple]
        rw [hf]
        exact hd (appendTuple x y)
      _ ↔ P x := (hp x).symm
  · exact arithmetic_prefix_to_level n p P

theorem positive_delta_arithmetic_iff (n : ℕ) (hn : 0 < n) {k : ℕ}
    (P : Tuple k → Prop) :
    FiniteDelta ∅ n P ↔ ArithmeticDefinability.PrefixDefinable n true P ∧
      ArithmeticDefinability.PrefixDefinable n false P := by
  exact and_congr (positive_level_arithmetic_iff n hn true P)
    (positive_level_arithmetic_iff n hn false P)

end Lemmatheca.ComputabilityTheory.ArithmeticalHierarchy
