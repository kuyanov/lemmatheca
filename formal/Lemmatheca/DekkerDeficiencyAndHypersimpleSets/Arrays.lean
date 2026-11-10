import Lemmatheca.DekkerDeficiencyAndHypersimpleSets.Programs
import Mathlib.Order.Interval.Set.Nat

namespace Lemmatheca.ComputabilityTheory.DekkerDeficiencyAndHypersimpleSets

open UniversalComputation OracleComputation HyperimmuneDegrees
open BusyBeaverFunctions (ordinaryProgram)

noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false
local notation "OCode" => Nat.Partrec.Code

def ArrayPass (a d : ℕ → ℕ) (x n : ℕ) : Prop :=
  ∀ s ∈ arraySet d n, x < a s

theorem bad_positions_bound (a : ℕ → ℕ) (ha : Function.Injective a) (x : ℕ) :
    Set.Finite {s | a s ≤ x} ∧ Set.ncard {s | a s ≤ x} ≤ x + 1 := by
  have hf : Set.Finite {s | a s ≤ x} :=
    Set.Finite.preimage ha.injOn (Set.finite_Iic x)
  refine ⟨hf, ?_⟩
  have hc := Set.ncard_le_ncard_of_injOn (s := {s | a s ≤ x}) (t := Set.Iic x)
    a (fun _ hs => hs) ha.injOn (Set.finite_Iic x)
  simpa only [Set.ncard_Iic_nat] using hc

theorem passing_member_bounded (a : ℕ → ℕ) (ha : Function.Injective a) (d : ℕ → ℕ)
    (hd : StrongArray d) (x : ℕ) : ∃ n < x + 2, ArrayPass a d x n := by
  by_contra h
  have hbad : ∀ n < x+2, ∃ s, s ∈ arraySet d n ∧ a s ≤ x := by
    intro n hn
    have hnot : ¬ ArrayPass a d x n := fun hp => h ⟨n,hn,hp⟩
    simp only [ArrayPass, not_forall, not_lt] at hnot
    obtain ⟨t,ht,hv⟩ := hnot
    exact ⟨t,ht,hv⟩
  let pick : Fin (x+2) → ℕ := fun i => Classical.choose (hbad i.val i.isLt)
  have hp (i : Fin (x+2)) : pick i ∈ arraySet d i.val ∧ a (pick i) ≤ x :=
    Classical.choose_spec (hbad i.val i.isLt)
  let B : Set ℕ := {s | a s ≤ x}
  let : Fintype B := (bad_positions_bound a ha x).1.fintype
  let f : Fin (x+2) → B := fun i => ⟨pick i,(hp i).2⟩
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    have he : pick i = pick j := congrArg Subtype.val hij
    exact Finset.disjoint_left.mp (hd.2 i.val j.val hne) (hp i).1 (he ▸ (hp j).1)
  have hc := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_fin, Set.fintypeCard_eq_ncard] at hc
  have hb := (bad_positions_bound a ha x).2
  change x+2 ≤ Set.ncard {s | a s ≤ x} at hc
  omega

theorem passing_member_exists (a : ℕ → ℕ) (ha : Function.Injective a) (d : ℕ → ℕ)
    (hd : StrongArray d) (x : ℕ) : ∃ n, ArrayPass a d x n := by
  obtain ⟨n,_,hn⟩ := passing_member_bounded a ha d hd x
  exact ⟨n,hn⟩

def firstPassing (a : ℕ → ℕ) (ha : Function.Injective a) (d : ℕ → ℕ)
    (hd : StrongArray d) (x : ℕ) : ℕ := Nat.find (passing_member_exists a ha d hd x)

theorem first_passing_spec (a : ℕ → ℕ) (ha : Function.Injective a) (d : ℕ → ℕ)
    (hd : StrongArray d) (x : ℕ) :
    ArrayPass a d x (firstPassing a ha d hd x) ∧ firstPassing a ha d hd x < x + 2 ∧
      ∀ n, ArrayPass a d x n → firstPassing a ha d hd x ≤ n := by
  have hex := passing_member_exists a ha d hd x
  have hmin : ∀ n, ArrayPass a d x n → Nat.find hex ≤ n := fun n hn => Nat.find_min' hex hn
  obtain ⟨n,hn,hp⟩ := passing_member_bounded a ha d hd x
  exact ⟨Nat.find_spec hex, (hmin n hp).trans_lt hn, hmin⟩


private theorem fold_max_bounds (xs : List ℕ) (z : ℕ) :
    z ≤ xs.foldl max z ∧ ∀ y ∈ xs, y ≤ xs.foldl max z := by
  induction xs generalizing z with
  | nil => simp
  | cons b bs ih =>
    have hb := ih (max z b)
    refine ⟨(le_max_left z b).trans hb.1, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (le_max_right z y).trans hb.1
    · exact hb.2 y hy

private theorem fold_max_mem_or (xs : List ℕ) (z : ℕ) :
    xs.foldl max z = z ∨ xs.foldl max z ∈ xs := by
  induction xs generalizing z with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    change bs.foldl max (max z b) = z ∨ bs.foldl max (max z b) ∈ b::bs
    rcases ih (max z b) with he | hm
    · rcases le_total z b with hz | hz
      · exact Or.inr (List.mem_cons.mpr (Or.inl (he.trans (max_eq_right hz))))
      · exact Or.inl (he.trans (max_eq_left hz))
    · exact Or.inr (List.mem_cons_of_mem b hm)

def singleMaximum (u : ℕ) : ℕ := (FiniteSequenceCoding.decode u).foldl max 0

theorem single_maximum_primitive : Primrec singleMaximum := by
  have hf : Primrec (fun l : List ℕ => l.foldl max 0) :=
    Primrec.list_foldl Primrec.id (Primrec.const 0)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact hf.comp (Primrec.ofNat (List ℕ))

theorem single_maximum_spec (d : ℕ → ℕ) (n : ℕ) :
    (∀ s ∈ arraySet d n, s ≤ singleMaximum (d n)) ∧
      ((arraySet d n).Nonempty → singleMaximum (d n) ∈ arraySet d n) := by
  constructor
  · intro s hs
    exact (fold_max_bounds (FiniteSequenceCoding.decode (d n)) 0).2 s (List.mem_toFinset.mp hs)
  · intro hn
    have hne : FiniteSequenceCoding.decode (d n) ≠ [] := by
      intro he
      obtain ⟨s,hs⟩ := hn
      simp [arraySet,he] at hs
    generalize he : FiniteSequenceCoding.decode (d n) = xs at *
    cases xs with
    | nil => exact False.elim (hne rfl)
    | cons b bs =>
      have hm := fold_max_mem_or bs b
      have hv : singleMaximum (d n) = bs.foldl max b := by
        simp [singleMaximum,he,List.foldl_cons]
      change singleMaximum (d n) ∈ (FiniteSequenceCoding.decode (d n)).toFinset
      rw [he,hv,List.mem_toFinset]
      exact List.mem_cons.mpr hm

-- Starting from (x,u), prepare ((x,u),length(u)) for the finite list recursion.
def arraySetup (w : ℕ) : ℕ := Nat.pair w (FiniteSequenceCoding.length w.unpair.2)

def arrayEntryInput (w : ℕ) : ℕ :=
  FiniteSequenceCoding.entry w.unpair.1.unpair.2 w.unpair.2.unpair.1

def arrayFold (w : ℕ) : ℕ :=
  if w.unpair.2.unpair.1 < w.unpair.2.unpair.2 then w.unpair.1 else 0

theorem array_setup_primitive : Primrec arraySetup := by
  exact Primrec₂.natPair.comp Primrec.id
    (FiniteSequenceCoding.primrec_length.comp (Primrec.snd.comp Primrec.unpair))

theorem array_entry_input_primitive : Primrec arrayEntryInput := by
  exact FiniteSequenceCoding.primrec_entry.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))

theorem array_fold_primitive : Primrec arrayFold := by
  exact Primrec.ite
    (Primrec.nat_lt.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
    (Primrec.fst.comp Primrec.unpair) (Primrec.const 0)

-- Recursion-step input ((x,u),(i,oldBit)); read the complete coded list.
def arrayStepCode (p : OCode) : OCode :=
  .comp (ordinaryProgram arrayFold array_fold_primitive.to_comp)
    (.pair (.comp .right .right)
      (.pair (.comp .left .left)
        (.comp p (ordinaryProgram arrayEntryInput array_entry_input_primitive.to_comp))))

def arrayPassCode (p q : OCode) : OCode :=
  .comp
    (.comp (.prec (Nat.Partrec.Code.const 1) (arrayStepCode p))
      (ordinaryProgram arraySetup array_setup_primitive.to_comp))
    (.pair .left (.comp q .right))

theorem array_pass_code_eval (a d : ℕ → ℕ) (p q : OCode)
    (hp : ∀ n, p.eval n = Part.some (a n))
    (hq : ∀ n, q.eval n = Part.some (d n)) (x n : ℕ) :
    (arrayPassCode p q).eval (Nat.pair x n) =
      Part.some (if ArrayPass a d x n then 1 else 0) := by
  let u := d n
  let P : ℕ → Prop := fun i => x < a (FiniteSequenceCoding.entry u i)
  have hs (i v : ℕ) : (arrayStepCode p).eval (Nat.pair (Nat.pair x u) (Nat.pair i v)) =
      Part.some (if P i then v else 0) := by
    simp [arrayStepCode, Nat.Partrec.Code.eval, Seq.seq, Part.bind_eq_bind,
      BusyBeaverFunctions.ordinaryProgram_eval, hp, arrayEntryInput, arrayFold, P]
  have rec_eval : ∀ k, (Nat.Partrec.Code.prec (.const 1) (arrayStepCode p)).eval
      (Nat.pair (Nat.pair x u) k) = Part.some (if ∀ i < k, P i then 1 else 0) := by
    intro k
    induction k with
    | zero => rw [Nat.Partrec.Code.eval_prec_zero,Nat.Partrec.Code.eval_const];simp
    | succ k ih =>
      rw [Nat.Partrec.Code.eval_prec_succ,ih]
      simp only [Part.bind_eq_bind,Part.bind_some]
      rw [hs]
      have hall : (∀ i < k+1, P i) ↔ (∀ i < k, P i) ∧ P k := by
        constructor
        · intro h;exact ⟨fun i hi => h i (by omega),h k (by omega)⟩
        · rintro ⟨h,hk⟩ i hi
          by_cases he : i=k
          · simpa [he] using hk
          · exact h i (by omega)
      simp only [hall]
      by_cases h0 : ∀ i < k,P i <;> by_cases h1 : P k <;>
        simp only [h0,h1,and_self,and_true,and_false,ite_true,ite_false]
  have he : (∀ i < FiniteSequenceCoding.length u, P i) ↔ ArrayPass a d x n := by
    constructor
    · intro h s hs
      have hm : s ∈ FiniteSequenceCoding.decode u := List.mem_toFinset.mp hs
      obtain ⟨i,hi,hv⟩ := List.mem_iff_getElem.mp hm
      have hh := h i hi
      simpa [P,FiniteSequenceCoding.entry,List.getElem?_eq_getElem hi,hv] using hh
    · intro h i hi
      have hv : FiniteSequenceCoding.entry u i = (FiniteSequenceCoding.decode u)[i] := by
        simp [FiniteSequenceCoding.entry,List.getElem?_eq_getElem hi]
      apply h
      change FiniteSequenceCoding.entry u i ∈ (FiniteSequenceCoding.decode u).toFinset
      rw [hv,List.mem_toFinset]
      exact List.getElem_mem hi
  have hi : (Nat.Partrec.Code.pair .left (.comp q .right)).eval (Nat.pair x n) =
      Part.some (Nat.pair x u) := by simp [Nat.Partrec.Code.eval,Seq.seq,hq,u]
  change ((Nat.Partrec.Code.pair .left (.comp q .right)).eval (Nat.pair x n)).bind _ = _
  rw [hi,Part.bind_some]
  change ((ordinaryProgram arraySetup array_setup_primitive.to_comp).eval (Nat.pair x u)).bind _ = _
  rw [BusyBeaverFunctions.ordinaryProgram_eval]
  simp only [arraySetup,Nat.unpair_pair,Part.bind_some]
  rw [rec_eval]
  simp only [he]

def arrayFailureCode (p q : OCode) : OCode := .comp zeroTest (arrayPassCode p q)

def arraySearchCode (p q : OCode) : OCode :=
  .comp (.rfind' (arrayFailureCode p q)) (.pair Nat.Partrec.Code.id .zero)

theorem array_search_eval (a : ℕ → ℕ) (ha : Function.Injective a) (d : ℕ → ℕ)
    (hd : StrongArray d) (p q : OCode)
    (hp : ∀ n, p.eval n = Part.some (a n))
    (hq : ∀ n, q.eval n = Part.some (d n)) (x : ℕ) :
    (arraySearchCode p q).eval x = Part.some (firstPassing a ha d hd x) := by
  let u := firstPassing a ha d hd x
  have hu : ArrayPass a d x u := (first_passing_spec a ha d hd x).1
  have hmin : ∀ t, ArrayPass a d x t → u ≤ t := (first_passing_spec a ha d hd x).2.2
  have test (n : ℕ) : (arrayFailureCode p q).eval (Nat.pair x n) =
      Part.some (if ArrayPass a d x n then 0 else 1) := by
    change ((arrayPassCode p q).eval (Nat.pair x n)).bind _ = _
    rw [array_pass_code_eval a d p q hp hq,Part.bind_some,zeroTest_eval]
    by_cases hn : ArrayPass a d x n <;> simp [hn]
  have hi : (Nat.Partrec.Code.pair Nat.Partrec.Code.id .zero).eval x = Part.some (Nat.pair x 0) := by
    rw [← eval_embed (∅ : Set ℕ) (Nat.Partrec.Code.pair Nat.Partrec.Code.id .zero) x]
    change eval (∅ : Set ℕ) (.pair (embed Nat.Partrec.Code.id) .zero) x = _
    simp [eval,eval_embed,Nat.Partrec.Code.eval_id]
  change ((Nat.Partrec.Code.pair Nat.Partrec.Code.id .zero).eval x).bind _ = _
  rw [hi,Part.bind_some]
  apply Part.eq_some_iff.mpr
  rw [ordinary_find_spec]
  refine ⟨Nat.zero_le _,?_,?_⟩
  · rw [test]
    change 0 ∈ Part.some (if ArrayPass a d x u then 0 else 1)
    rw [ite_eq_left hu]
    exact Part.mem_some 0
  · intro t _ htu
    have hn : ¬ ArrayPass a d x t := fun h => Nat.not_le_of_gt htu (hmin t h)
    refine ⟨1,?_,by decide⟩
    rw [test,ite_eq_right hn]
    exact Part.mem_some 1

def arrayDeciderCode (p q : OCode) : OCode :=
  .comp (rangeCode p)
    (.pair Nat.Partrec.Code.id
      (.comp (ordinaryProgram singleMaximum single_maximum_primitive.to_comp)
        (.comp q (arraySearchCode p q))))

theorem array_decider_eval (a : ℕ → ℕ) (ha : Function.Injective a) (d : ℕ → ℕ)
    (hd : StrongArray d) (hh : ArrayHits d (nondeficient a)) (p q : OCode)
    (hp : ∀ n, p.eval n = Part.some (a n))
    (hq : ∀ n, q.eval n = Part.some (d n)) (x : ℕ) :
    (arrayDeciderCode p q).eval x = Part.some (indicator (Set.range a) x) := by
  let n := firstPassing a ha d hd x
  let M := singleMaximum (d n)
  have hm : (Nat.Partrec.Code.comp (ordinaryProgram singleMaximum single_maximum_primitive.to_comp)
      (.comp q (arraySearchCode p q))).eval x = Part.some M := by
    change (((arraySearchCode p q).eval x).bind q.eval).bind _ = _
    rw [array_search_eval a ha d hd p q hp hq,Part.bind_some,hq,Part.bind_some,
      BusyBeaverFunctions.ordinaryProgram_eval]
  have hi : (Nat.Partrec.Code.pair Nat.Partrec.Code.id
      (.comp (ordinaryProgram singleMaximum single_maximum_primitive.to_comp)
        (.comp q (arraySearchCode p q)))).eval x = Part.some (Nat.pair x M) := by
    rw [← eval_embed (∅ : Set ℕ) (Nat.Partrec.Code.pair Nat.Partrec.Code.id
      (.comp (ordinaryProgram singleMaximum single_maximum_primitive.to_comp)
        (.comp q (arraySearchCode p q)))) x]
    change (eval (∅ : Set ℕ) (embed Nat.Partrec.Code.id) x).bind
      (fun v => (eval (∅ : Set ℕ) (embed (.comp
        (ordinaryProgram singleMaximum single_maximum_primitive.to_comp)
        (.comp q (arraySearchCode p q)))) x).map (Nat.pair v)) = _
    rw [eval_embed,Nat.Partrec.Code.eval_id,Part.bind_some,eval_embed,hm,Part.map_some]
  change ((Nat.Partrec.Code.pair Nat.Partrec.Code.id
    (.comp (ordinaryProgram singleMaximum single_maximum_primitive.to_comp)
      (.comp q (arraySearchCode p q)))).eval x).bind _ = _
  rw [hi,Part.bind_some,range_code_eval a p hp x M]
  obtain ⟨t,htF,htC⟩ := hh n
  have hxt : x < a t := (first_passing_spec a ha d hd x).1 t htF
  have htM : t ≤ M := (single_maximum_spec d n).1 t htF
  have hb := bounded_range_membership a ha t x htC hxt
  have he : (∃ i ≤ M,a i=x) ↔ x ∈ Set.range a := by
    constructor
    · rintro ⟨i,_,hi⟩;exact ⟨i,hi⟩
    · intro hx;obtain ⟨i,hi,hv⟩ := hb.mp hx;exact ⟨i,hi.trans htM,hv⟩
  unfold indicator
  simp only [Membership.mem,Set.Mem] at he ⊢
  simp only [he]

theorem array_hits_decides (a : ℕ → ℕ) (ha : Function.Injective a) (hc : Computable a)
    (d : ℕ → ℕ) (hd : StrongArray d) (hh : ArrayHits d (nondeficient a)) :
    ComputablePred (Set.range a) := by
  let p := ordinaryProgram a hc
  let q := ordinaryProgram d hd.1
  have hp (n : ℕ) : p.eval n = Part.some (a n) := BusyBeaverFunctions.ordinaryProgram_eval a hc n
  have hq (n : ℕ) : q.eval n = Part.some (d n) := BusyBeaverFunctions.ordinaryProgram_eval d hd.1 n
  have hf : Partrec (fun x => (arrayDeciderCode p q).eval x) :=
    Nat.Partrec.Code.eval_part.comp (Computable.const _) Computable.id
  have hbit : Computable (indicator (Set.range a)) := hf.of_eq_tot
    (fun x => Part.eq_some_iff.mp (array_decider_eval a ha d hd hh p q hp hq x))
  exact (decidable_iff_characteristic (Set.range a)).mpr ⟨_,hbit,fun _ => rfl⟩

theorem no_array_hits (a : ℕ → ℕ) (ha : Function.Injective a) (hc : Computable a)
    (hnc : ¬ ComputablePred (Set.range a)) :
    ¬ ∃ d : ℕ → ℕ, StrongArray d ∧ ArrayHits d (nondeficient a) := by
  rintro ⟨d,hd,hh⟩
  exact hnc (array_hits_decides a ha hc d hd hh)

end
end Lemmatheca.ComputabilityTheory.DekkerDeficiencyAndHypersimpleSets
