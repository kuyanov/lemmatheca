import Lemmatheca.ArithmeticalHierarchy.Prefixes
import Lemmatheca.TuringDegrees.Reductions

/-! Complementation, substitution, finite closure and bounded witness collection. -/
namespace Lemmatheca.ComputabilityTheory.ArithmeticalHierarchy

open OracleComputation
set_option backward.isDefEq.respectTransparency false

noncomputable def ComputableIn (A : Set ℕ) (f : ℕ → ℕ) : Prop :=
  OracleComputation.PartialComputable A (fun x => Part.some (f x))

private abbrev ncons {n : ℕ} (y : ℕ) (v : Tuple n) : Tuple (n+1) := Fin.cons y v

private theorem ci_of_comp (A : Set ℕ) {f : ℕ → ℕ} (hf : Computable f) : ComputableIn A f := by
  exact ordinary_inclusion A ((Partrec.nat_iff.mp hf.partrec).of_eq (fun _ => rfl))

private theorem ci_comp {A : Set ℕ} {f g : ℕ → ℕ} (hf : ComputableIn A f)
    (hg : ComputableIn A g) : ComputableIn A (fun x => f (g x)) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨.comp c d, ?_⟩
  funext x
  simp only [eval, congrFun hd, Part.bind_some, congrFun hc]

private theorem ci_pair {A : Set ℕ} {f g : ℕ → ℕ} (hf : ComputableIn A f)
    (hg : ComputableIn A g) : ComputableIn A (fun x => Nat.pair (f x) (g x)) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨.pair c d, ?_⟩
  funext x
  simp only [eval, congrFun hd, congrFun hc, Part.bind_some, Part.map_some]

private theorem rdec_preimage {A : Set ℕ} {S : Set ℕ} (hS : OracleProgramNumberings.RelativeDecidable A S)
    {f : ℕ → ℕ} (hf : ComputableIn A f) :
    OracleProgramNumberings.RelativeDecidable A {x | f x ∈ S} := by
  obtain ⟨c, hc⟩ := hS
  obtain ⟨d, hd⟩ := hf
  refine ⟨.comp c d, ?_⟩
  funext x
  change (eval A d x).bind (eval A c) = _
  rw [congrFun hd, Part.bind_some, congrFun hc]
  rfl

private theorem rdec_congr {A : Set ℕ} {S T : Set ℕ}
    (hS : OracleProgramNumberings.RelativeDecidable A S) (h : ∀ x, x ∈ S ↔ x ∈ T) :
    OracleProgramNumberings.RelativeDecidable A T := by
  have : S = T := Set.ext h
  simpa only [← this] using hS

private theorem rdec_not {A : Set ℕ} {S : Set ℕ}
    (hS : OracleProgramNumberings.RelativeDecidable A S) :
    OracleProgramNumberings.RelativeDecidable A {x | x ∉ S} := by
  classical
  obtain ⟨c, hc⟩ := hS
  refine ⟨.comp (embed zeroTest) c, ?_⟩
  funext x
  simp only [eval, congrFun hc, Part.bind_some, eval_embed, zeroTest_eval]
  by_cases hx : x ∈ S <;> simp [UniversalComputation.indicator, hx]

private theorem rdec_const (A : Set ℕ) (b : Prop) :
    OracleProgramNumberings.RelativeDecidable A {_x | b} := by
  classical
  exact ⟨OracleProgramNumberings.constantCode (if b then 1 else 0),
    funext (fun x => OracleProgramNumberings.constant_eval A _ x)⟩

private theorem pr_tuple {α : Type} [Primcodable α] {k : ℕ} {f : α → Tuple k}
    (hf : ∀ i, Primrec (fun x => f x i)) : Primrec f := by
  exact Primrec.fin_curry.mpr (Primrec.fin_curry₁.mpr hf).swap

private theorem pr_cons {α : Type} [Primcodable α] {n : ℕ}
    {a : α → ℕ} {v : α → Tuple n} (ha : Primrec a) (hv : Primrec v) :
    Primrec (fun x : α => (ncons (a x) (v x) : Tuple (n + 1))) := by
  apply pr_tuple
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa only [Fin.cons_zero] using ha
  · simpa only [Fin.cons_succ, id_eq] using Primrec.fin_app.comp hv (Primrec.const i)

private theorem pr_append {α : Type} [Primcodable α] {k n : ℕ}
    {v : α → Tuple k} {w : α → Tuple n} (hv : Primrec v) (hw : Primrec w) :
    Primrec (fun x => appendTuple (v x) (w x)) := by
  apply pr_tuple
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa only [appendTuple, Fin.append_left, id_eq] using Primrec.fin_app.comp hv (Primrec.const i)
  · simpa only [appendTuple, Fin.append_right, id_eq] using Primrec.fin_app.comp hw (Primrec.const i)

private theorem matrix_map {A : Set ℕ} {n m : ℕ} {R : ℕ → Tuple n → Prop}
    (hR : MatrixDecidable A R) (f : ℕ → Tuple m → ℕ) (g : ℕ → Tuple m → Tuple n)
    (hf : Primrec (fun w : ℕ => f w.unpair.1 (tupleDecode m w.unpair.2)))
    (hg : Primrec (fun w : ℕ => g w.unpair.1 (tupleDecode m w.unpair.2))) :
    MatrixDecidable A (fun x v => R (f x v) (g x v)) := by
  have hp := Primrec₂.natPair.comp hf ((tupleCode_primitive n).comp hg)
  apply rdec_congr (rdec_preimage hR (ci_of_comp A hp.to_comp))
  intro z
  simp only [Set.mem_ofPred_eq, Nat.unpair_pair, tuple_decode_code]

private theorem quantify_congr {n : ℕ} (p : Bool) {R S : Tuple n → Prop}
    (h : ∀ v, R v ↔ S v) : quantify n p R ↔ quantify n p S := by
  induction n generalizing p with
  | zero => exact h _
  | succ n ih =>
    cases p <;> simp only [quantify]
    · exact forall_congr' (fun y => ih _ (fun v => h (ncons y v)))
    · exact exists_congr (fun y => ih _ (fun v => h (ncons y v)))

private theorem level_congr {A : Set ℕ} {n : ℕ} {p : Bool} {P Q : ℕ → Prop}
    (hP : Level A n p P) (h : ∀ x, P x ↔ Q x) : Level A n p Q := by
  obtain ⟨R, hR, he⟩ := hP
  exact ⟨R, hR, fun x => (h x).symm.trans (he x)⟩

private theorem quantify_not (n : ℕ) (p : Bool) (R : Tuple n → Prop) :
    quantify n (!p) (fun v => ¬R v) ↔ ¬quantify n p R := by
  classical
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    cases p
    · simp only [Bool.not_false, quantify, not_forall]
      exact exists_congr (fun y => by simpa only [Bool.not_true] using ih true (fun v => R (ncons y v)))
    · simp only [Bool.not_true, quantify, not_exists]
      exact forall_congr' (fun y => by simpa only [Bool.not_false] using ih false (fun v => R (ncons y v)))

private theorem rdec_and {A : Set ℕ} {S T : Set ℕ}
    (hS : OracleProgramNumberings.RelativeDecidable A S)
    (hT : OracleProgramNumberings.RelativeDecidable A T) :
    OracleProgramNumberings.RelativeDecidable A {x | x ∈ S ∧ x ∈ T} := by
  classical
  have hm : Primrec (fun z : ℕ => z.unpair.1 * z.unpair.2) :=
    Primrec.nat_mul.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
  have h := ci_comp (ci_of_comp A hm.to_comp) (ci_pair hS hT)
  simp only [Nat.unpair_pair] at h
  change ComputableIn A (fun x => UniversalComputation.indicator (fun z => z ∈ S) x *
    UniversalComputation.indicator (fun z => z ∈ T) x) at h
  have he : (fun x => UniversalComputation.indicator (fun z => z ∈ S) x *
      UniversalComputation.indicator (fun z => z ∈ T) x) =
      (fun x => UniversalComputation.indicator (fun z => z ∈ S ∧ z ∈ T) x) := by
    funext x
    by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;> simp [UniversalComputation.indicator, hs, ht]
  rw [he] at h
  exact h

private theorem rdec_or {A : Set ℕ} {S T : Set ℕ}
    (hS : OracleProgramNumberings.RelativeDecidable A S)
    (hT : OracleProgramNumberings.RelativeDecidable A T) :
    OracleProgramNumberings.RelativeDecidable A {x | x ∈ S ∨ x ∈ T} := by
  classical
  exact rdec_congr (rdec_not (rdec_and (rdec_not hS) (rdec_not hT))) (fun x => by simp only [Set.mem_ofPred_eq]; tauto)

private theorem quantify_const (n : ℕ) (p : Bool) (Q : Prop) :
    quantify n p (fun _ => Q) ↔ Q := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => cases p <;> simp [quantify, ih]

private theorem level_const (A : Set ℕ) (n : ℕ) (p : Bool) (Q : Prop) : Level A n p (fun _ => Q) := by
  exact ⟨fun _ _ => Q, rdec_const A Q, fun _ => (quantify_const n p Q).symm⟩

private theorem prefix_cons (n : ℕ) (y : ℕ) (v : Tuple (n+1)) :
    (fun i : Fin (n+1) => ncons y v i.castSucc) =
      (ncons y (fun i : Fin n => v i.castSucc) : Tuple (n+1)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

private theorem quantify_drop_last (n : ℕ) (p : Bool) (R : Tuple n → Prop) :
    quantify (n+1) p (fun v => R (fun i => v i.castSucc)) ↔ quantify n p R := by
  induction n generalizing p with
  | zero =>
    have h (v : Tuple 1) : (fun i : Fin 0 => v i.castSucc) = Fin.elim0 := Subsingleton.elim _ _
    simp only [h, quantify_const, quantify]
  | succ n ih =>
    cases p
    · change (∀ y, quantify (n+1) true (fun v => R (fun i => ncons y v i.castSucc))) ↔
        ∀ y, quantify n true (fun v => R (ncons y v))
      simp only [prefix_cons]
      exact forall_congr' (fun y => ih true (fun v => R (ncons y v)))
    · change (∃ y, quantify (n+1) false (fun v => R (fun i => ncons y v i.castSucc))) ↔
        ∃ y, quantify n false (fun v => R (ncons y v))
      simp only [prefix_cons]
      exact exists_congr (fun y => ih false (fun v => R (ncons y v)))

private theorem pair_forall (R : ℕ → Prop) :
    (∀ c : ℕ, R c) ↔ ∀ a b, R (Nat.pair a b) := by
  exact ⟨fun h a b => h _, fun h c => by simpa only [Nat.pair_unpair] using h c.unpair.1 c.unpair.2⟩

private theorem pair_exists (R : ℕ → Prop) :
    (∃ c : ℕ, R c) ↔ ∃ a b, R (Nat.pair a b) := by
  exact ⟨fun ⟨c,hc⟩ => ⟨c.unpair.1,c.unpair.2, by simpa only [Nat.pair_unpair] using hc⟩,
    fun ⟨a,b,h⟩ => ⟨Nat.pair a b,h⟩⟩

private theorem cons_unpair_left (n y : ℕ) (v : Tuple n) :
    (fun i : Fin (n+1) => (ncons y v i).unpair.1) =
      (ncons y.unpair.1 (fun i => (v i).unpair.1) : Tuple (n+1)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

private theorem cons_unpair_right (n y : ℕ) (v : Tuple n) :
    (fun i : Fin (n+1) => (ncons y v i).unpair.2) =
      (ncons y.unpair.2 (fun i => (v i).unpair.2) : Tuple (n+1)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

private theorem quantify_and (n : ℕ) (p : Bool) (R S : Tuple n → Prop) :
    quantify n p (fun v => R (fun i => (v i).unpair.1) ∧ S (fun i => (v i).unpair.2)) ↔
      quantify n p R ∧ quantify n p S := by
  induction n generalizing p with
  | zero =>
    simp only [quantify]
    rw [Subsingleton.elim (fun i : Fin 0 => (Fin.elim0 i : ℕ).unpair.1) Fin.elim0,
      Subsingleton.elim (fun i : Fin 0 => (Fin.elim0 i : ℕ).unpair.2) Fin.elim0]
  | succ n ih =>
    cases p
    · change (∀ c, quantify n true (fun v => R (fun i => (ncons c v i).unpair.1) ∧
        S (fun i => (ncons c v i).unpair.2))) ↔
        (∀ a, quantify n true (fun v => R (ncons a v))) ∧
        ∀ b, quantify n true (fun v => S (ncons b v))
      rw [pair_forall]
      simp only [cons_unpair_left, cons_unpair_right, Nat.unpair_pair]
      have he (a b : ℕ) := ih true (fun v => R (ncons a v)) (fun v => S (ncons b v))
      simp_rw [he]
      exact ⟨fun h => ⟨fun a => (h a 0).1, fun b => (h 0 b).2⟩,
        fun ⟨hr,hs⟩ a b => ⟨hr a,hs b⟩⟩
    · change (∃ c, quantify n false (fun v => R (fun i => (ncons c v i).unpair.1) ∧
        S (fun i => (ncons c v i).unpair.2))) ↔
        (∃ a, quantify n false (fun v => R (ncons a v))) ∧
        ∃ b, quantify n false (fun v => S (ncons b v))
      rw [pair_exists]
      simp only [cons_unpair_left, cons_unpair_right, Nat.unpair_pair]
      have he (a b : ℕ) := ih false (fun v => R (ncons a v)) (fun v => S (ncons b v))
      simp_rw [he]
      aesop

private theorem quantify_or (n : ℕ) (p : Bool) (R S : Tuple n → Prop) :
    quantify n p (fun v => R (fun i => (v i).unpair.1) ∨ S (fun i => (v i).unpair.2)) ↔
      quantify n p R ∨ quantify n p S := by
  classical
  have h := quantify_and n (!p) (fun v => ¬R v) (fun v => ¬S v)
  have hn := not_congr h
  simp only [not_and_or, ← quantify_not, Bool.not_not] at hn
  simpa only [not_not] using hn

theorem level_complement (A : Set ℕ) (n : ℕ) (p : Bool) (P : ℕ → Prop) :
    Level A n p P ↔ Level A n (!p) (fun x => ¬P x) := by
  classical
  have forward (q : Bool) (Q : ℕ → Prop) (hQ : Level A n q Q) :
      Level A n (!q) (fun x => ¬Q x) := by
    obtain ⟨R, hR, he⟩ := hQ
    exact ⟨fun x v => ¬R x v, rdec_not hR,
      fun x => (not_congr (he x)).trans (quantify_not n q (R x)).symm⟩
  constructor
  · exact forward p P
  · intro h
    have hh := forward (!p) _ h
    simp only [Bool.not_not] at hh
    exact level_congr hh (fun x => by simp)

theorem finite_level_complement (A : Set ℕ) (n : ℕ) (p : Bool) {k : ℕ}
    (P : Tuple k → Prop) :
    FiniteLevel A n p P ↔ FiniteLevel A n (!p) (fun x => ¬P x) := by
  exact level_complement A n p _

theorem computable_preimage (A : Set ℕ) (n : ℕ) (p : Bool) (P : ℕ → Prop)
    (f : ℕ → ℕ) (hf : ComputableIn A f) (hP : Level A n p P) :
    Level A n p (fun x => P (f x)) := by
  obtain ⟨R, hR, he⟩ := hP
  refine ⟨fun x v => R (f x) v, ?_, fun x => he (f x)⟩
  have hleft : ComputableIn A (fun w : ℕ => w.unpair.1) :=
    ci_of_comp A (Primrec.fst.comp Primrec.unpair).to_comp
  have hright : ComputableIn A (fun w : ℕ => w.unpair.2) :=
    ci_of_comp A (Primrec.snd.comp Primrec.unpair).to_comp
  apply rdec_congr (rdec_preimage hR (ci_pair (ci_comp hf hleft) hright))
  intro z
  simp only [Set.mem_ofPred_eq, Nat.unpair_pair]

private theorem ci_tuple_code (A : Set ℕ) (k : ℕ) (f : ℕ → Tuple k)
    (hf : ∀ i, ComputableIn A (fun c => f c i)) : ComputableIn A (fun c => tupleCode (f c)) := by
  induction k with
  | zero =>
    have he : (fun c => tupleCode (f c)) = fun _ => 0 := by
      funext c
      rfl
    rw [he]
    exact ci_of_comp A (Computable.const 0)
  | succ k ih =>
    have ht := ih (fun c i => f c i.succ) (fun i => hf i.succ)
    have hc : Primrec (fun w : ℕ => FiniteSequenceCoding.cons w.unpair.1 w.unpair.2) :=
      FiniteSequenceCoding.primrec_cons.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
    have h := ci_comp (ci_of_comp A hc.to_comp) (ci_pair (hf 0) ht)
    simp only [Nat.unpair_pair] at h
    have he : (fun c => FiniteSequenceCoding.cons (f c 0) (tupleCode (fun i => f c i.succ))) =
        (fun c => tupleCode (f c)) := by
      funext c
      simp only [tupleCode, List.ofFn_succ, FiniteSequenceCoding.code_cons]
    rw [he] at h
    exact h

theorem finite_computable_preimage (A : Set ℕ) (n : ℕ) (p : Bool) {j k : ℕ}
    (P : Tuple k → Prop) (f : Tuple j → Tuple k)
    (hf : ∀ i, ComputableIn A (fun c => f (tupleDecode j c) i))
    (hP : FiniteLevel A n p P) : FiniteLevel A n p (fun x => P (f x)) := by
  have hc := ci_tuple_code A k (fun c => f (tupleDecode j c)) hf
  have h := computable_preimage A n p (fun c => P (tupleDecode k c))
    (fun c => tupleCode (f (tupleDecode j c))) hc hP
  exact level_congr h (fun c => by simp only [tuple_decode_code])

theorem manyOne_preimage (A : Set ℕ) (n : ℕ) (p : Bool) (P Q : ℕ → Prop)
    (hf : ManyOneReducible P Q) (hQ : Level A n p Q) : Level A n p P := by
  obtain ⟨f, hf, he⟩ := hf
  exact level_congr (computable_preimage A n p Q f (ci_of_comp A hf) hQ) (fun x => (he x).symm)

theorem level_padding (A : Set ℕ) (n : ℕ) (p q : Bool) (P : ℕ → Prop)
    (hP : Level A n p P) : Level A (n + 1) q P := by
  obtain ⟨R, hR, he⟩ := hP
  by_cases hpq : p = q
  · subst q
    refine ⟨fun x v => R x (fun i => v i.castSucc), ?_, fun x => (he x).trans (quantify_drop_last n p (R x)).symm⟩
    exact matrix_map hR (fun x _ => x) (fun _ v i => v i.castSucc)
      (Primrec.fst.comp Primrec.unpair)
      (pr_tuple (fun i => FiniteSequenceCoding.primrec_entry.comp
        (Primrec.snd.comp Primrec.unpair) (Primrec.const i.castSucc.val)))
  · have hflip : !q = p := by cases p <;> cases q <;> simp_all
    refine ⟨fun x v => R x (fun i => v i.succ), ?_, ?_⟩
    · exact matrix_map hR (fun x _ => x) (fun _ v i => v i.succ)
        (Primrec.fst.comp Primrec.unpair)
        (pr_tuple (fun i => FiniteSequenceCoding.primrec_entry.comp
          (Primrec.snd.comp Primrec.unpair) (Primrec.const i.succ.val)))
    · intro x
      cases q
      · simp_all only [quantify, Fin.cons_succ, forall_const]
      · simp_all only [quantify, Fin.cons_succ, exists_const]

theorem finite_padding (A : Set ℕ) (n : ℕ) (p q : Bool) {k : ℕ}
    (P : Tuple k → Prop) (hP : FiniteLevel A n p P) : FiniteLevel A (n + 1) q P := by
  exact level_padding A n p q _ hP

theorem level_and (A : Set ℕ) (n : ℕ) (p : Bool) (P Q : ℕ → Prop)
    (hP : Level A n p P) (hQ : Level A n p Q) : Level A n p (fun x => P x ∧ Q x) := by
  obtain ⟨R, hR, he⟩ := hP
  obtain ⟨S, hS, hf⟩ := hQ
  have hleft := matrix_map hR (fun x _ => x) (fun _ v i => (v i).unpair.1)
    (Primrec.fst.comp Primrec.unpair)
    (pr_tuple (fun i => Primrec.fst.comp (Primrec.unpair.comp
      (FiniteSequenceCoding.primrec_entry.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const i.val)))))
  have hright := matrix_map hS (fun x _ => x) (fun _ v i => (v i).unpair.2)
    (Primrec.fst.comp Primrec.unpair)
    (pr_tuple (fun i => Primrec.snd.comp (Primrec.unpair.comp
      (FiniteSequenceCoding.primrec_entry.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const i.val)))))
  refine ⟨fun x v => R x (fun i => (v i).unpair.1) ∧ S x (fun i => (v i).unpair.2),
    rdec_and hleft hright, ?_⟩
  intro x
  exact (Iff.and (he x) (hf x)).trans (quantify_and n p (R x) (S x)).symm

theorem level_or (A : Set ℕ) (n : ℕ) (p : Bool) (P Q : ℕ → Prop)
    (hP : Level A n p P) (hQ : Level A n p Q) : Level A n p (fun x => P x ∨ Q x) := by
  obtain ⟨R, hR, he⟩ := hP
  obtain ⟨S, hS, hf⟩ := hQ
  have hleft := matrix_map hR (fun x _ => x) (fun _ v i => (v i).unpair.1)
    (Primrec.fst.comp Primrec.unpair)
    (pr_tuple (fun i => Primrec.fst.comp (Primrec.unpair.comp
      (FiniteSequenceCoding.primrec_entry.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const i.val)))))
  have hright := matrix_map hS (fun x _ => x) (fun _ v i => (v i).unpair.2)
    (Primrec.fst.comp Primrec.unpair)
    (pr_tuple (fun i => Primrec.snd.comp (Primrec.unpair.comp
      (FiniteSequenceCoding.primrec_entry.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const i.val)))))
  refine ⟨fun x v => R x (fun i => (v i).unpair.1) ∨ S x (fun i => (v i).unpair.2),
    rdec_or hleft hright, ?_⟩
  intro x
  exact (Iff.or (he x) (hf x)).trans (quantify_or n p (R x) (S x)).symm

theorem finite_boolean_closure (A : Set ℕ) (n m : ℕ) (p : Bool) {k : ℕ}
    (P : Fin m → Tuple k → Prop) (hP : ∀ i, FiniteLevel A n p (P i)) :
    FiniteLevel A n p (fun x => ∀ i, P i x) ∧
      FiniteLevel A n p (fun x => ∃ i, P i x) := by
  induction m with
  | zero =>
    constructor
    · exact level_congr (level_const A n p True) (fun _ => by simp)
    · exact level_congr (level_const A n p False) (fun _ => by simp)
  | succ m ih =>
    obtain ⟨hAll,hEx⟩ := ih (fun i => P i.succ) (fun i => hP i.succ)
    constructor
    · exact level_congr (level_and A n p _ _ (hP 0) hAll) (fun c => by simpa only using (Fin.forall_fin_succ (P := fun i => P i (tupleDecode k c))).symm)
    · exact level_congr (level_or A n p _ _ (hP 0) hEx) (fun c => by simpa only using (Fin.exists_fin_succ (P := fun i => P i (tupleDecode k c))).symm)

theorem finite_witness_collection (m : ℕ) (R : ℕ → ℕ → Prop) :
    (∀ i < m, ∃ u, R i u) ↔ ∃ c, ∀ i < m, R i (FSC.entry c i) := by
  classical
  constructor
  · intro h
    let v : Tuple m := fun i => Classical.choose (h i.val i.isLt)
    refine ⟨tupleCode v, fun i hi => ?_⟩
    have he := congrFun (tuple_decode_code v) ⟨i, hi⟩
    change FSC.entry (tupleCode v) i = v ⟨i,hi⟩ at he
    rw [he]
    exact Classical.choose_spec (h i hi)
  · rintro ⟨c, hc⟩ i hi
    exact ⟨FSC.entry c i, hc i hi⟩

theorem finite_witness_code (m : ℕ) (v : Tuple m) :
    FSC.length (tupleCode v) = m ∧ ∀ i : Fin m, FSC.entry (tupleCode v) i = v i := by
  constructor
  · simp [tupleCode, FSC.length]
  · intro i
    exact congrFun (tuple_decode_code v) i

private theorem rdec_bounded_forall (A : Set ℕ) (R : ℕ → ℕ → Prop) (b : ℕ → ℕ)
    (hb : ComputableIn A b) (hR : OracleProgramNumberings.RelativeDecidableRelation A R) :
    OracleProgramNumberings.RelativeDecidable A {x | ∀ i < b x, R x i} := by
  classical
  obtain ⟨c, hc⟩ := hR
  obtain ⟨d, hd⟩ := hb
  let mul : Code := embed (OracleProgramNumberings.ordinaryCode
    (fun w : ℕ => w.unpair.1 * w.unpair.2)
    (Primrec.nat_iff.mp (Primrec.nat_mul.comp
      (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))))
  let step : Code := .comp mul (.pair (.comp c (.pair .left (.comp .left .right))) (.comp .right .right))
  let prog : Code := .prec (OracleProgramNumberings.constantCode 1) step
  have hs (x j z : ℕ) : eval A step (Nat.pair x (Nat.pair j z)) =
      Part.some ((if R x j then 1 else 0) * z) := by
    simp only [step, mul, eval, Nat.unpair_pair, Part.bind_some, Part.map_some,
      congrFun hc, eval_embed, OracleProgramNumberings.ordinaryCode_eval,
      UniversalComputation.indicator]
  have hp (x m : ℕ) : eval A prog (Nat.pair x m) =
      Part.some (if ∀ i < m, R x i then 1 else 0) := by
    induction m with
    | zero => simp [prog, eval, OracleProgramNumberings.constant_eval]
    | succ m ih =>
      rw [show prog = Code.prec (OracleProgramNumberings.constantCode 1) step from rfl, eval_prec_succ]
      change (eval A prog (Nat.pair x m)).bind (fun z => eval A step (Nat.pair x (Nat.pair m z))) = _
      rw [ih, Part.bind_some, hs]
      have hiff : (∀ i < m+1, R x i) ↔ (∀ i < m, R x i) ∧ R x m := by
        constructor
        · intro h
          exact ⟨fun i hi => h i (by omega), h m (by omega)⟩
        · rintro ⟨h,hm⟩ i hi
          by_cases he : i = m
          · simpa [he] using hm
          · exact h i (by omega)
      simp only [hiff]
      by_cases h : ∀ i < m, R x i <;> by_cases hm : R x m <;> simp [h,hm]
  refine ⟨.comp prog (.pair OracleProgramNumberings.identityCode d), ?_⟩
  funext x
  simp only [eval, OracleProgramNumberings.identity_eval, congrFun hd, Part.bind_some,
    Part.map_some, hp, UniversalComputation.indicator, Set.mem_ofPred_eq]
  split_ifs <;> rfl

private theorem entries_cons (n c i : ℕ) (v : Tuple n) :
    (fun j : Fin (n+1) => FSC.entry (ncons c v j) i) =
      ncons (FSC.entry c i) (fun j => FSC.entry (v j) i) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> rfl

private theorem quantify_collect (m n : ℕ) (p : Bool) (R : ℕ → Tuple n → Prop) :
    (∀ i < m, quantify n p (R i)) ↔
      quantify n p (fun v => ∀ i < m, R i (fun j => FSC.entry (v j) i)) := by
  induction n generalizing p with
  | zero =>
    simp only [quantify]
    exact forall_congr' (fun i => forall_congr' (fun _ =>
      iff_of_eq (congrArg (R i) (Subsingleton.elim _ _))))
  | succ n ih =>
    cases p
    · change (∀ i < m, ∀ y, quantify n true (fun v => R i (ncons y v))) ↔
        ∀ c, quantify n true (fun v => ∀ i < m, R i (fun j => FSC.entry (ncons c v j) i))
      simp only [entries_cons]
      constructor
      · intro h c
        exact (ih true (fun i v => R i (ncons (FSC.entry c i) v))).mp
          (fun i hi => h i hi (FSC.entry c i))
      · intro h i hi y
        let c := tupleCode (fun _ : Fin m => y)
        have hc := (ih true (fun i v => R i (ncons (FSC.entry c i) v))).mpr (h c)
        have he : FSC.entry c i = y := congrFun (tuple_decode_code (fun _ : Fin m => y)) ⟨i,hi⟩
        simpa only [he] using hc i hi
    · change (∀ i < m, ∃ y, quantify n false (fun v => R i (ncons y v))) ↔
        ∃ c, quantify n false (fun v => ∀ i < m, R i (fun j => FSC.entry (ncons c v j) i))
      rw [finite_witness_collection]
      simp only [entries_cons]
      exact exists_congr (fun c => ih false (fun i v => R i (ncons (FSC.entry c i) v)))

theorem bounded_forall (A : Set ℕ) (n : ℕ) (p : Bool) (R : ℕ → ℕ → Prop)
    (b : ℕ → ℕ) (hb : ComputableIn A b)
    (hR : Level A n p (fun w => R w.unpair.1 w.unpair.2)) :
    Level A n p (fun x => ∀ i < b x, R x i) := by
  obtain ⟨M, hM, he⟩ := hR
  let N : ℕ → Tuple n → Prop := fun x v => ∀ i < b x,
    M (Nat.pair x i) (fun j => FSC.entry (v j) i)
  have hz : Primrec (fun z : ℕ => Nat.pair
      (Nat.pair z.unpair.1.unpair.1 z.unpair.2)
      (tupleCode (fun j : Fin n => FSC.entry (FSC.entry z.unpair.1.unpair.2 j.val) z.unpair.2))) := by
    apply Primrec₂.natPair.comp
    · exact Primrec₂.natPair.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.snd.comp Primrec.unpair)
    · apply (tupleCode_primitive n).comp
      exact pr_tuple (fun j => FiniteSequenceCoding.primrec_entry.comp
        (FiniteSequenceCoding.primrec_entry.comp
          (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))) (Primrec.const j.val))
        (Primrec.snd.comp Primrec.unpair))
  have hrel : OracleProgramNumberings.RelativeDecidableRelation A
      (fun z i => M (Nat.pair z.unpair.1 i) (fun j => FSC.entry (tupleDecode n z.unpair.2 j) i)) := by
    apply rdec_congr (rdec_preimage hM (ci_of_comp A hz.to_comp))
    intro z
    simp only [Set.mem_ofPred_eq, Nat.unpair_pair, tuple_decode_code]
    rfl
  have hbound := ci_comp hb (ci_of_comp A (Primrec.fst.comp Primrec.unpair).to_comp)
  refine ⟨N, rdec_bounded_forall A _ _ hbound hrel, ?_⟩
  intro x
  have hh : (∀ i < b x, R x i) ↔ ∀ i < b x, quantify n p (M (Nat.pair x i)) := by
    apply forall_congr'
    intro i
    apply forall_congr'
    intro _
    simpa only [Nat.unpair_pair] using he (Nat.pair x i)
  exact hh.trans (quantify_collect (b x) n p (fun i => M (Nat.pair x i)))

theorem bounded_exists (A : Set ℕ) (n : ℕ) (p : Bool) (R : ℕ → ℕ → Prop)
    (b : ℕ → ℕ) (hb : ComputableIn A b)
    (hR : Level A n p (fun w => R w.unpair.1 w.unpair.2)) :
    Level A n p (fun x => ∃ i < b x, R x i) := by
  classical
  have hnot := (level_complement A n p _).mp hR
  have hall := bounded_forall A n (!p) (fun x i => ¬R x i) b hb hnot
  have h := (level_complement A n (!p) _).mp hall
  simp only [Bool.not_not] at h
  exact level_congr h (fun x => by simp only [not_forall, not_not, exists_prop])

private theorem pr_snoc {α : Type} [Primcodable α] {k : ℕ}
    {v : α → Tuple k} {a : α → ℕ} (hv : Primrec v) (ha : Primrec a) :
    Primrec (fun x => snocTuple (v x) (a x)) := by
  apply pr_tuple
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simpa [snocTuple] using ha
  · simpa [snocTuple] using Primrec.fin_app.comp hv (Primrec.const i)

private theorem finite_snoc_pullback (A : Set ℕ) (n : ℕ) (p : Bool) {k : ℕ}
    (R : Tuple (k+1) → Prop) (hR : FiniteLevel A n p R) :
    Level A n p (fun w => R (snocTuple (tupleDecode k w.unpair.1) w.unpair.2)) := by
  have hc : Primrec (fun w : ℕ => tupleCode (snocTuple (tupleDecode k w.unpair.1) w.unpair.2)) :=
    (tupleCode_primitive (k+1)).comp
      (pr_snoc ((tupleDecode_primitive k).comp (Primrec.fst.comp Primrec.unpair))
        (Primrec.snd.comp Primrec.unpair))
  have h := computable_preimage A n p (fun c => R (tupleDecode (k+1) c)) _ (ci_of_comp A hc.to_comp) hR
  exact level_congr h (fun _ => by simp only [tuple_decode_code])

theorem finite_bounded_quantifiers (A : Set ℕ) (n : ℕ) (p : Bool) {k : ℕ}
    (R : Tuple k → ℕ → Prop) (b : Tuple k → ℕ)
    (hb : ComputableIn A (fun c => b (tupleDecode k c)))
    (hR : FiniteLevel A n p (fun v : Tuple (k + 1) =>
      R (fun i => v i.castSucc) (v (Fin.last k)))) :
    FiniteLevel A n p (fun x => ∀ i < b x, R x i) ∧
      FiniteLevel A n p (fun x => ∃ i < b x, R x i) := by
  have hS := finite_snoc_pullback A n p _ hR
  have hs : Level A n p (fun w => R (tupleDecode k w.unpair.1) w.unpair.2) :=
    level_congr hS (fun w => by simp [snocTuple])
  exact ⟨bounded_forall A n p (fun c i => R (tupleDecode k c) i) _ hb hs,
    bounded_exists A n p (fun c i => R (tupleDecode k c) i) _ hb hs⟩

theorem positive_exists (A : Set ℕ) (n : ℕ) (hn : 0 < n) (R : ℕ → ℕ → Prop)
    (hR : Sigma A n (fun w => R w.unpair.1 w.unpair.2)) :
    Sigma A n (fun x => ∃ y, R x y) := by
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨S, hS, he⟩ := (sigma_succ_iff A n _).mp hR
    have hc : Primrec (fun z : ℕ => Nat.pair (Nat.pair z.unpair.1 z.unpair.2.unpair.1) z.unpair.2.unpair.2) :=
      Primrec₂.natPair.comp
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
    apply (sigma_succ_iff A n _).mpr
    have hpre := computable_preimage A n false _ _ (ci_of_comp A hc.to_comp) hS
    have hpre' : Pi A n (fun z => S (Nat.pair z.unpair.1 z.unpair.2.unpair.1) z.unpair.2.unpair.2) :=
      level_congr hpre (fun z => by simp only [Nat.unpair_pair])
    refine ⟨fun x w => S (Nat.pair x w.unpair.1) w.unpair.2, hpre', ?_⟩
    intro x
    have hey (y : ℕ) : R x y ↔ ∃ t, S (Nat.pair x y) t := by
      simpa only [Nat.unpair_pair] using he (Nat.pair x y)
    constructor
    · rintro ⟨y,hy⟩
      obtain ⟨t,ht⟩ := (hey y).mp hy
      exact ⟨Nat.pair y t, by simpa only [Nat.unpair_pair] using ht⟩
    · rintro ⟨w,hw⟩
      exact ⟨w.unpair.1, (hey _).mpr ⟨w.unpair.2,hw⟩⟩

theorem positive_forall (A : Set ℕ) (n : ℕ) (hn : 0 < n) (R : ℕ → ℕ → Prop)
    (hR : Pi A n (fun w => R w.unpair.1 w.unpair.2)) :
    Pi A n (fun x => ∀ y, R x y) := by
  classical
  have hnot := (level_complement A n false _).mp hR
  have hex := positive_exists A n hn (fun x y => ¬R x y) hnot
  have hall := (level_complement A n true _).mp hex
  exact level_congr hall (fun x => by simp only [not_exists, not_not])

theorem finite_positive_quantifiers (A : Set ℕ) (n : ℕ) (hn : 0 < n) {k : ℕ}
    (R : Tuple (k + 1) → Prop) :
    (FiniteLevel A n true R → FiniteLevel A n true (fun x => ∃ y, R (snocTuple x y))) ∧
    (FiniteLevel A n false R → FiniteLevel A n false (fun x => ∀ y, R (snocTuple x y))) := by
  constructor
  · intro hR
    exact positive_exists A n hn (fun c y => R (snocTuple (tupleDecode k c) y))
      (finite_snoc_pullback A n true R hR)
  · intro hR
    exact positive_forall A n hn (fun c y => R (snocTuple (tupleDecode k c) y))
      (finite_snoc_pullback A n false R hR)

theorem oracle_monotone {A B : Set ℕ} (hAB : TuringDegrees.Reducible A B)
    (n : ℕ) (p : Bool) (P : ℕ → Prop) (hP : Level A n p P) : Level B n p P := by
  obtain ⟨d, hd⟩ := hAB
  obtain ⟨R, ⟨c, hc⟩, he⟩ := hP
  refine ⟨R, ⟨subst d c, ?_⟩, he⟩
  funext x
  rw [subst_eval A B d hd c x]
  exact congrFun hc x

end Lemmatheca.ComputabilityTheory.ArithmeticalHierarchy
