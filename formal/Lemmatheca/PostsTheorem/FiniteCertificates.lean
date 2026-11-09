import Lemmatheca.OracleProgramNumberings.Universal

/-! Ordinary finite-oracle tables and their guarded consistency certificates. -/
namespace Lemmatheca.ComputabilityTheory.PostsTheorem

open OracleComputation OracleProgramNumberings UniversalComputation
open PartialRecursiveFunctions (Args)

set_option backward.isDefEq.respectTransparency false

def beta (u q : ℕ) : ℕ := FiniteSequenceCoding.entry u q % 2

def finiteOracle (u : ℕ) : Set ℕ := {q | beta u q = 1}

noncomputable def Agreement (u k : ℕ) (A : Set ℕ) : Prop :=
  ∀ q < k, beta u q = indicator (fun x => x ∈ A) q

noncomputable def prefixCode (A : Set ℕ) (k : ℕ) : ℕ :=
  FiniteSequenceCoding.code ((List.range k).map (indicator (fun x => x ∈ A)))

theorem beta_primitive : Primrec₂ beta := by
  exact (Primrec.nat_mod.comp (FiniteSequenceCoding.primrec_entry.comp Primrec.fst Primrec.snd)
    (Primrec.const 2)).to₂

theorem beta_bits (u q : ℕ) : beta u q = 0 ∨ beta u q = 1 := by
  have h := Nat.mod_lt (FiniteSequenceCoding.entry u q) (by decide : 0 < 2)
  unfold beta
  omega

theorem finiteOracle_finite (u : ℕ) : (finiteOracle u).Finite := by
  apply (Set.finite_Iio (FiniteSequenceCoding.length u)).subset
  intro q hq
  by_contra h
  have hz := FiniteSequenceCoding.entry_out_of_range u q (Nat.le_of_not_gt h)
  change beta u q = 1 at hq
  simp [beta, hz] at hq

theorem finiteOracle_indicator (u q : ℕ) :
    indicator (fun x => x ∈ finiteOracle u) q = beta u q := by
  classical
  rcases beta_bits u q with h | h <;> simp [indicator, finiteOracle, h]

theorem prefixCode_spec (A : Set ℕ) (k : ℕ) :
    FiniteSequenceCoding.length (prefixCode A k) = k ∧ Agreement (prefixCode A k) k A := by
  classical
  constructor
  · simp [prefixCode, FiniteSequenceCoding.length]
  · intro q hq
    have he : FiniteSequenceCoding.entry (prefixCode A k) q = indicator (fun x => x ∈ A) q := by
      simp [prefixCode, FiniteSequenceCoding.entry, List.getElem?_range hq]
    unfold beta
    rw [he]
    by_cases h : q ∈ A <;> simp [indicator,h]

def finiteValue (u k e x : ℕ) : ℕ := tableValue (beta u) k e x

def pack4 (u k e x : ℕ) : ℕ := Nat.pair u (Nat.pair k (Nat.pair e x))

def finiteValueInput (w : ℕ) : ℕ :=
  finiteValue w.unpair.1 w.unpair.2.unpair.1
    w.unpair.2.unpair.2.unpair.1 w.unpair.2.unpair.2.unpair.2

def finiteCheck (u k e x : ℕ) : Prop := 0 < finiteValue u k e x

def finiteCheckInput (w : ℕ) : ℕ := if 0 < finiteValueInput w then 1 else 0

private theorem appendTwo_primitive (n : ℕ) :
    Primrec (fun p : Args n × ℕ × ℕ => p.1 ++
      List.Vector.cons p.2.1 (List.Vector.cons p.2.2 List.Vector.nil)) := by
  apply Primrec.vector_toList_iff.mp
  simpa only [List.Vector.toList_append, List.Vector.toList_cons, List.Vector.toList_nil] using
    Primrec.list_append.comp (Primrec.vector_toList.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])))

private theorem initial_primitive (n : ℕ) : Primrec (@PrimitiveRecursion.initialPart n) :=
  Primrec.vector_ofFn (fun i => Primrec.vector_get.comp Primrec.id (Primrec.const i.castSucc))

private theorem uniform_beta_primitive {n : ℕ} {F : (ℕ → ℕ) → Args n → ℕ}
    (hF : UniformPrimitive F) : Primrec (fun p : ℕ × Args n => F (beta p.1) p.2) := by
  induction hF with
  | zero n => exact Primrec.const 0
  | succ => exact Primrec.succ.comp (Primrec.vector_get.comp Primrec.snd (Primrec.const 0))
  | proj i => exact Primrec.vector_get.comp Primrec.snd (Primrec.const i)
  | query =>
    exact beta_primitive.comp Primrec.fst
      (Primrec.vector_get.comp Primrec.snd (Primrec.const 0))
  | @comp m n h g hh hg ihh ihg =>
    exact ihh.comp (Primrec.fst.pair (Primrec.vector_ofFn ihg))
  | @prec n g h hg hh ihg ihh =>
    let H (p : ℕ × Args n) (t : ℕ) := PrimitiveRecursion.recValue (g (beta p.1))
      (fun v j z => h (beta p.1) (v ++ List.Vector.cons j (List.Vector.cons z List.Vector.nil))) p.2 t
    have hmove : Primrec (fun p : (ℕ × Args n) × (ℕ × ℕ) =>
        (p.1.1, p.1.2 ++ List.Vector.cons p.2.1 (List.Vector.cons p.2.2 List.Vector.nil))) :=
      (Primrec.fst.comp Primrec.fst).pair
        ((appendTwo_primitive n).comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
    have hrec : Primrec₂ H := by
      apply (Primrec.nat_rec ihg (ihh.comp hmove).to₂).of_eq
      intro p t
      rfl
    exact (hrec.comp
      (Primrec.fst.pair ((initial_primitive n).comp Primrec.snd))
      (Primrec.vector_get.comp Primrec.snd (Primrec.const (Fin.last n)))).of_eq (fun _ => rfl)

theorem finiteValue_primitive : Primrec finiteValueInput := by
  let g : Fin 3 → ℕ → ℕ := Fin.cases
    (fun w => w.unpair.2.unpair.1)
    (Fin.cases (fun w => w.unpair.2.unpair.2.unpair.1)
      (fun _ w => w.unpair.2.unpair.2.unpair.2))
  have hg : ∀ i, Primrec (g i) := by
    intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => ?_) i) i
    · exact Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
    · exact Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
    · exact Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have h := (uniform_beta_primitive boundedFamily_primitive).comp
    ((Primrec.fst.comp Primrec.unpair).pair (Primrec.vector_ofFn hg))
  exact h.of_eq (fun w => by simp only [boundedFamily, List.Vector.get_ofFn]; rfl)

theorem finiteCheck_primitive : Primrec finiteCheckInput := by
  exact Primrec.ite (Primrec.nat_lt.comp (Primrec.const 0) finiteValue_primitive)
    (Primrec.const 1) (Primrec.const 0)

noncomputable def finiteValueCode : Nat.Partrec.Code :=
  ordinaryCode finiteValueInput (Primrec.nat_iff.mp finiteValue_primitive)

noncomputable def finiteCheckCode : Nat.Partrec.Code :=
  ordinaryCode finiteCheckInput (Primrec.nat_iff.mp finiteCheck_primitive)

theorem finiteValueCode_eval (u k e x : ℕ) :
    Nat.Partrec.Code.eval finiteValueCode (pack4 u k e x) =
      Part.some (finiteValue u k e x) := by
  rw [finiteValueCode, ordinaryCode_eval]
  simp only [finiteValueInput, pack4, Nat.unpair_pair]

theorem finiteCheckCode_eval (u k e x : ℕ) :
    Nat.Partrec.Code.eval finiteCheckCode (pack4 u k e x) =
      Part.some (@ite ℕ (finiteCheck u k e x) (Classical.propDecidable _) 1 0) := by
  classical
  rw [finiteCheckCode, ordinaryCode_eval]
  simp only [finiteCheckInput, finiteValueInput, pack4, Nat.unpair_pair, finiteCheck]
  split_ifs <;> rfl

theorem finite_codes_uniform (A : Set ℕ) (u k e x : ℕ) :
    eval A (embed finiteValueCode) (pack4 u k e x) = Part.some (finiteValue u k e x) ∧
      eval A (embed finiteCheckCode) (pack4 u k e x) =
        Part.some (@ite ℕ (finiteCheck u k e x) (Classical.propDecidable _) 1 0) := by
  rw [eval_embed, eval_embed]
  exact ⟨finiteValueCode_eval u k e x, finiteCheckCode_eval u k e x⟩

theorem finiteValue_identity (u k e x : ℕ) :
    finiteValue u k e x = boundedValue (finiteOracle u) k e x := by
  have he : beta u = indicator (fun x => x ∈ finiteOracle u) :=
    funext (fun q => (finiteOracle_indicator u q).symm)
  unfold finiteValue
  rw [he, tableValue_correct]

theorem finiteValue_outside (u k e x : ℕ) (hx : k ≤ x) :
    finiteValue u k e x = 0 := by
  unfold finiteValue tableValue tableLookup
  simp only [ite_eq_right (Nat.not_lt.mpr hx)]

theorem bounded_query_dependence (q r : ℕ → ℕ) (k : ℕ)
    (h : ∀ z < k, q z = r z) (c : Code) (x : ℕ) :
    boundedQ q k c x = boundedQ r k c x := by
  induction k generalizing c x with
  | zero => simp only [boundedQ]
  | succ k ih =>
    induction c generalizing x with
    | zero | succ | left | right =>
      by_cases hx : x ≤ k <;> simp only [boundedQ, hx, ↓reduceIte]
    | query =>
      by_cases hx : x ≤ k
      · simp only [boundedQ, ite_eq_left hx, h x (by omega)]
      · simp only [boundedQ, ite_eq_right hx]
    | pair c d ihc ihd =>
      by_cases hx : x ≤ k
      · conv_lhs => rw [boundedQ, ite_eq_left hx]
        conv_rhs => rw [boundedQ, ite_eq_left hx]
        rw [ihc,ihd]
      · simp only [boundedQ, ite_eq_right hx]
    | comp c d ihc ihd =>
      by_cases hx : x ≤ k
      · conv_lhs => rw [boundedQ, ite_eq_left hx]
        conv_rhs => rw [boundedQ, ite_eq_left hx]
        rw [ihd]
        congr 1
        funext v
        exact ihc v
      · simp only [boundedQ, ite_eq_right hx]
    | prec c d ihc ihd =>
      by_cases hx : x ≤ k
      · conv_lhs => rw [boundedQ, ite_eq_left hx]
        conv_rhs => rw [boundedQ, ite_eq_left hx]
        cases x.unpair.2 with
        | zero => exact ihc x.unpair.1
        | succ m =>
          dsimp only
          rw [ih (fun z hz => h z (by omega)) (.prec c d)]
          congr 1
          funext v
          exact ihd _
      · simp only [boundedQ, ite_eq_right hx]
    | find' c ihc =>
      by_cases hx : x ≤ k
      · conv_lhs => rw [boundedQ, ite_eq_left hx]
        conv_rhs => rw [boundedQ, ite_eq_left hx]
        rw [ihc]
        congr 1
        funext v
        split_ifs
        · rfl
        · exact ih (fun z hz => h z (by omega)) (.find' c) _
      · simp only [boundedQ, ite_eq_right hx]

private theorem tableEntry_agree (q r : ℕ → ℕ) (old current k p x : ℕ) (h : q x = r x) :
    tableEntry q old current k p x = tableEntry r old current k p x := by
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · exact congrArg (fun z => z+1) h
  rfl

private theorem buildRow_agree (q r : ℕ → ℕ) (old current k p t : ℕ)
    (h : ∀ x < t, q x = r x) :
    buildRow q old current k p t = buildRow r old current k p t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [buildRow, buildRow, ih (fun x hx => h x (by omega)),
      tableEntry_agree q r old current k p t (h t (by omega))]

private theorem buildRows_agree (q r : ℕ → ℕ) (old k p : ℕ)
    (h : ∀ x < k+1, q x = r x) : buildRows q old k p = buildRows r old k p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    simp only [buildRows, ih, buildRow_agree q r old (buildRows r old k p) k p (k+1) h]

private theorem table_agree (q r : ℕ → ℕ) (k e : ℕ) (h : ∀ x < k, q x = r x) :
    finiteTable q e k = finiteTable r e k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [finiteTable, finiteTable, ih (fun x hx => h x (by omega))]
    exact buildRows_agree q r _ k (e+1) h

theorem finiteTable_agreement (A : Set ℕ) (u k e : ℕ) (h : Agreement u k A) :
    finiteTable (beta u) e k = finiteTable (indicator (fun x => x ∈ A)) e k := by
  exact table_agree (beta u) (indicator (fun x => x ∈ A)) k e h

theorem finiteValue_agreement (A : Set ℕ) (u k e x : ℕ) (h : Agreement u k A) :
    finiteValue u k e x = boundedValue A k e x := by
  unfold finiteValue tableValue
  rw [finiteTable_agreement A u k e h]
  exact tableValue_correct A k e x

theorem finite_certificate_domain (A : Set ℕ) (e x : ℕ) :
    (phi A e x).Dom ↔ ∃ u k, finiteCheck u k e x ∧ Agreement u k A := by
  rw [phi_domain_certificate]
  constructor
  · rintro ⟨k,hk⟩
    have ha := (prefixCode_spec A k).2
    refine ⟨prefixCode A k,k,?_,ha⟩
    change 0 < finiteValue (prefixCode A k) k e x
    rw [finiteValue_agreement A _ k e x ha]
    exact hk
  · rintro ⟨u,k,hk,ha⟩
    exact ⟨k, by simpa only [finiteCheck, finiteValue_agreement A u k e x ha] using hk⟩

theorem finite_certificate_output (A : Set ℕ) (e x y : ℕ) :
    y ∈ phi A e x ↔ ∃ u k, finiteValue u k e x = y + 1 ∧ Agreement u k A := by
  rw [phi_output_certificate]
  constructor
  · rintro ⟨k,hk⟩
    have ha := (prefixCode_spec A k).2
    exact ⟨prefixCode A k,k,by rw [finiteValue_agreement A _ k e x ha]; exact hk,ha⟩
  · rintro ⟨u,k,hk,ha⟩
    exact ⟨k, by simpa only [finiteValue_agreement A u k e x ha] using hk⟩

end Lemmatheca.ComputabilityTheory.PostsTheorem
