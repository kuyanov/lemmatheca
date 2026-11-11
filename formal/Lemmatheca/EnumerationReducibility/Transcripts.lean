import Lemmatheca.EnumerationReducibility.Composition
import Lemmatheca.OracleProgramNumberings.Parameters
import Lemmatheca.OracleComputation.Traces

namespace Lemmatheca.ComputabilityTheory.EnumerationReducibility
open UniversalComputation
open OracleProgramNumberings (encodeCode decodeCode)

/-- Positive and negative answers receive the even and odd tags respectively. -/
def tag (q b : ℕ) : ℕ := 2 * q + (1 - b)

def totalInfo (A : Set ℕ) : Set ℕ := TuringDegrees.join A Aᶜ

def traceEvidence (τ : OracleComputation.QueryRecord) : Finset ℕ :=
  (τ.map (fun p => tag p.1 p.2)).toFinset

private def recProgram (r : ℕ) : ℕ := r.unpair.1
private def recInput (r : ℕ) : ℕ := r.unpair.2.unpair.1
private def recOutput (r : ℕ) : ℕ := r.unpair.2.unpair.2.unpair.1
private def recChildren (r : ℕ) : ℕ := r.unpair.2.unpair.2.unpair.2
private def recAt (t i : ℕ) : ℕ := FiniteSequenceCoding.entry t i
private def childAt (t i j : ℕ) : ℕ :=
  recAt t (FiniteSequenceCoding.entry (recChildren (recAt t i)) j)

/-- Finite frame check for exactly the nine shared oracle-program constructors. -/
private def frameCheck (t i : ℕ) : Bool :=
  let r := recAt t i
  let p := recProgram r
  let x := recInput r
  let y := recOutput r
  let cs := recChildren r
  let k := FiniteSequenceCoding.length cs
  let c := childAt t i 0
  let d := childAt t i 1
  match p with
  | 0 => decide (k = 0 ∧ y = 0)
  | 1 => decide (k = 0 ∧ y = x + 1)
  | 2 => decide (k = 0 ∧ y = x.unpair.1)
  | 3 => decide (k = 0 ∧ y = x.unpair.2)
  | 4 => decide (k = 0 ∧ y ≤ 1)
  | p + 5 =>
    let m := p / 4
    match p % 4 with
    | 0 => decide (k = 2 ∧ recProgram c = m.unpair.1 ∧ recProgram d = m.unpair.2 ∧
        recInput c = x ∧ recInput d = x ∧ y = Nat.pair (recOutput c) (recOutput d))
    | 1 =>
      decide (k = x.unpair.2 + 1 ∧ recProgram c = m.unpair.1 ∧ recInput c = x.unpair.1 ∧
        y = recOutput (childAt t i x.unpair.2)) &&
      (List.range x.unpair.2).all (fun j =>
        decide (recProgram (childAt t i (j+1)) = m.unpair.2 ∧
          recInput (childAt t i (j+1)) = Nat.pair x.unpair.1 (Nat.pair j (recOutput (childAt t i j)))))
    | 2 => decide (k = 2 ∧ recProgram c = m.unpair.2 ∧ recProgram d = m.unpair.1 ∧
        recInput c = x ∧ recInput d = recOutput c ∧ y = recOutput d)
    | _ =>
      decide (x.unpair.2 ≤ y ∧ k = y - x.unpair.2 + 1) &&
      (List.range k).all (fun j =>
        decide (recProgram (childAt t i j) = m ∧
          recInput (childAt t i j) = Nat.pair x.unpair.1 (x.unpair.2 + j)) &&
        if j + 1 = k then decide (recOutput (childAt t i j) = 0)
        else decide (0 < recOutput (childAt t i j)))

/-- Every nonroot record is consumed exactly once, and every child is earlier. -/
def certificateCheck (e x y t : ℕ) : Bool :=
  let nodes := FiniteSequenceCoding.decode t
  let k := nodes.length
  let root := recAt t (k-1)
  let uses := nodes.flatMap (fun r => FiniteSequenceCoding.decode (recChildren r))
  decide (0 < k ∧ recProgram root = e ∧ recInput root = x ∧ recOutput root = y) &&
    (List.range k).all (fun i =>
      frameCheck t i &&
        (FiniteSequenceCoding.decode (recChildren (recAt t i))).all (fun j => decide (j < i)) &&
        decide (uses.count i = if i+1 = k then 0 else 1))

def evidenceCode (t : ℕ) : ℕ := FiniteSequenceCoding.code
  (((FiniteSequenceCoding.decode t).filter (fun r => recProgram r == 4)).map
    (fun r => tag (recInput r) (recOutput r)))

theorem tag_bits (A : Set ℕ) (q b : ℕ) (hb : b ≤ 1) :
    tag q b ∈ totalInfo A ↔ b = indicator (fun n => n ∈ A) q := by
  classical
  have he := (TuringDegrees.join_even_reduction A Aᶜ).2 q
  have ho := (TuringDegrees.join_odd_reduction A Aᶜ).2 q
  simp only [Set.mem_compl_iff] at ho
  interval_cases b <;> by_cases hq : q ∈ A <;> simp [tag, totalInfo, indicator, hq, ← he, ← ho]

theorem totalInfo_exactly_one (A : Set ℕ) (q : ℕ) :
    (2*q ∈ totalInfo A ↔ q ∈ A) ∧ (2*q+1 ∈ totalInfo A ↔ q ∉ A) ∧
      ((2*q ∈ totalInfo A) ↔ ¬ (2*q+1 ∈ totalInfo A)) := by
  have he := (TuringDegrees.join_even_reduction A Aᶜ).2 q
  have ho := (TuringDegrees.join_odd_reduction A Aᶜ).2 q
  simp only [Set.mem_compl_iff] at ho
  exact ⟨he.symm, ho.symm, by change (2*q ∈ TuringDegrees.join A Aᶜ) ↔ ¬(2*q+1 ∈ TuringDegrees.join A Aᶜ); rw [← he, ← ho]; simp⟩

theorem traceEvidence_consistent (A : Set ℕ) (τ : OracleComputation.QueryRecord)
    (hτ : OracleComputation.ValidRecord τ) :
    (traceEvidence τ : Set ℕ) ⊆ totalInfo A ↔ OracleComputation.Consistent A τ := by
  classical
  constructor
  · intro h q b hm
    apply (tag_bits A q b (by rcases hτ q b hm with rfl | rfl <;> omega)).mp
    apply h
    simp only [traceEvidence, Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨(q,b),hm,rfl⟩
  · intro h z hz
    simp only [traceEvidence, Finset.mem_coe, List.mem_toFinset, List.mem_map] at hz
    obtain ⟨⟨q,b⟩, hm, rfl⟩ := hz
    exact (tag_bits A q b (by rcases hτ q b hm with rfl | rfl <;> omega)).mpr (h q b hm)

private theorem verifier_list_all {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {g : α → β → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).all (g a)) := by
  have hs : Primrec (fun p : α × (β × Bool) => g p.1 p.2.1 && p.2.2) :=
    Primrec.and.comp (hg.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr hf (Primrec.const true) hs.to₂).of_eq (fun a => by
    induction f a with
    | nil => rfl
    | cons b bs ih => simp only [List.foldr_cons, List.all_cons, ih])

private theorem verifier_recProgram : Primrec recProgram :=
  Primrec.fst.comp Primrec.unpair
private theorem verifier_recInput : Primrec recInput :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
private theorem verifier_recOutput : Primrec recOutput :=
  Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
private theorem verifier_recChildren : Primrec recChildren :=
  Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
private theorem verifier_recAt : Primrec₂ recAt := FiniteSequenceCoding.primrec_entry
private theorem verifier_childAt : Primrec (fun p : (ℕ × ℕ) × ℕ => childAt p.1.1 p.1.2 p.2) :=
  verifier_recAt.comp (Primrec.fst.comp Primrec.fst)
    (FiniteSequenceCoding.primrec_entry.comp
      (verifier_recChildren.comp (verifier_recAt.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.fst))) Primrec.snd)

private theorem verifier_frameCheck : Primrec₂ frameCheck := by
  have ht : Primrec (fun p : ℕ × ℕ => p.1) := Primrec.fst
  have hi : Primrec (fun p : ℕ × ℕ => p.2) := Primrec.snd
  have hr := verifier_recAt.comp ht hi
  have hp := verifier_recProgram.comp hr
  have hx := verifier_recInput.comp hr
  have hy := verifier_recOutput.comp hr
  have hcs := verifier_recChildren.comp hr
  have hk := FiniteSequenceCoding.primrec_length.comp hcs
  have hc := verifier_childAt.comp (Primrec.id.pair (Primrec.const 0))
  have hd := verifier_childAt.comp (Primrec.id.pair (Primrec.const 1))
  have hm := Primrec.nat_div.comp (Primrec.nat_sub.comp hp (Primrec.const 5)) (Primrec.const 4)
  have htag := Primrec.nat_mod.comp (Primrec.nat_sub.comp hp (Primrec.const 5)) (Primrec.const 4)
  have hml := Primrec.fst.comp (Primrec.unpair.comp hm)
  have hmr := Primrec.snd.comp (Primrec.unpair.comp hm)
  have hxl := Primrec.fst.comp (Primrec.unpair.comp hx)
  have hxr := Primrec.snd.comp (Primrec.unpair.comp hx)
  have hcp := verifier_recProgram.comp hc
  have hdp := verifier_recProgram.comp hd
  have hcx := verifier_recInput.comp hc
  have hdx := verifier_recInput.comp hd
  have hcy := verifier_recOutput.comp hc
  have hdy := verifier_recOutput.comp hd
  have hz := (Primrec.eq.comp hk (Primrec.const 0)).and
    (Primrec.eq.comp hy (Primrec.const 0))
  have hs := (Primrec.eq.comp hk (Primrec.const 0)).and
    (Primrec.eq.comp hy (Primrec.succ.comp hx))
  have hl := (Primrec.eq.comp hk (Primrec.const 0)).and (Primrec.eq.comp hy hxl)
  have hrgt := (Primrec.eq.comp hk (Primrec.const 0)).and (Primrec.eq.comp hy hxr)
  have hq := (Primrec.eq.comp hk (Primrec.const 0)).and
    (Primrec.nat_le.comp hy (Primrec.const 1))
  have hpair := (Primrec.eq.comp hk (Primrec.const 2)).and
    ((Primrec.eq.comp hcp hml).and ((Primrec.eq.comp hdp hmr).and
      ((Primrec.eq.comp hcx hx).and ((Primrec.eq.comp hdx hx).and
        (Primrec.eq.comp hy (Primrec₂.natPair.comp hcy hdy))))))
  have hcomp := (Primrec.eq.comp hk (Primrec.const 2)).and
    ((Primrec.eq.comp hcp hmr).and ((Primrec.eq.comp hdp hml).and
      ((Primrec.eq.comp hcx hx).and ((Primrec.eq.comp hdx hcy).and
        (Primrec.eq.comp hy hdy)))))
  have hlast := verifier_recOutput.comp (verifier_childAt.comp (Primrec.id.pair hxr))
  have hrecHead := (Primrec.eq.comp hk (Primrec.succ.comp hxr)).and
    ((Primrec.eq.comp hcp hml).and ((Primrec.eq.comp hcx hxl).and (Primrec.eq.comp hy hlast)))
  have hchild := verifier_childAt
  have hnext := verifier_childAt.comp (Primrec.fst.pair (Primrec.succ.comp Primrec.snd))
  have hrecStep := (Primrec.eq.comp (verifier_recProgram.comp hnext) (hmr.comp Primrec.fst)).and
    (Primrec.eq.comp (verifier_recInput.comp hnext)
      (Primrec₂.natPair.comp (hxl.comp Primrec.fst)
        (Primrec₂.natPair.comp Primrec.snd (verifier_recOutput.comp hchild))))
  have hrecAll := verifier_list_all (Primrec.list_range.comp hxr) hrecStep.decide.to₂
  have hrec := Primrec.and.comp hrecHead.decide hrecAll
  have hfindHead := (Primrec.nat_le.comp hxr hy).and
    (Primrec.eq.comp hk (Primrec.succ.comp (Primrec.nat_sub.comp hy hxr)))
  have hfindStep := (Primrec.eq.comp (verifier_recProgram.comp hchild) (hm.comp Primrec.fst)).and
    (Primrec.eq.comp (verifier_recInput.comp hchild)
      (Primrec₂.natPair.comp (hxl.comp Primrec.fst)
        (Primrec.nat_add.comp (hxr.comp Primrec.fst) Primrec.snd)))
  have hfindValue := Primrec.ite
    (Primrec.eq.comp (Primrec.succ.comp Primrec.snd) (hk.comp Primrec.fst))
    (Primrec.eq.comp (verifier_recOutput.comp hchild) (Primrec.const 0)).decide
    (Primrec.nat_lt.comp (Primrec.const 0) (verifier_recOutput.comp hchild)).decide
  have hfindAll := verifier_list_all (Primrec.list_range.comp hk)
    (Primrec.and.comp hfindStep.decide hfindValue).to₂
  have hfind := Primrec.and.comp hfindHead.decide hfindAll
  have htail := Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) hpair.decide
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) hrec
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) hcomp.decide hfind))
  have hall := Primrec.ite (Primrec.eq.comp hp (Primrec.const 0)) hz.decide
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 1)) hs.decide
      (Primrec.ite (Primrec.eq.comp hp (Primrec.const 2)) hl.decide
        (Primrec.ite (Primrec.eq.comp hp (Primrec.const 3)) hrgt.decide
          (Primrec.ite (Primrec.eq.comp hp (Primrec.const 4)) hq.decide htail))))
  apply hall.of_eq
  intro v
  generalize he : recProgram (recAt v.1 v.2) = p
  iterate 5 rcases p with _ | p; · simp [frameCheck, he]
  have h2 : p + 5 ≠ 2 := by omega
  have h3 : p + 5 ≠ 3 := by omega
  have h4 : p + 5 ≠ 4 := by omega
  change recProgram (recAt v.1 v.2) = p + 5 at he
  have hb := Nat.mod_lt p (by decide : 0 < 4)
  interval_cases hmod : p % 4 <;>
    simp [frameCheck, he, h2, h3, h4, hmod]

private theorem verifier_count : Primrec (fun p : List ℕ × ℕ => p.1.count p.2) := by
  have hf := Primrec.list_length.comp (PrimrecRel.listFilter (Primrec.eq (α := ℕ)))
  exact hf.of_eq (fun p => by simp only [List.count_eq_length_filter]; rfl)

theorem certificateCheck_primitive :
    Primrec (fun p : ((ℕ × ℕ) × ℕ) × ℕ => certificateCheck p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have he : Primrec (fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hx : Primrec (fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hy : Primrec (fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.2) := Primrec.snd.comp Primrec.fst
  have ht : Primrec (fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.2) := Primrec.snd
  have hnodes := (Primrec.ofNat (List ℕ)).comp ht
  have hk := Primrec.list_length.comp hnodes
  have hroot := verifier_recAt.comp ht (Primrec.nat_sub.comp hk (Primrec.const 1))
  have hhead := (Primrec.nat_lt.comp (Primrec.const 0) hk).and
    ((Primrec.eq.comp (verifier_recProgram.comp hroot) he).and
      ((Primrec.eq.comp (verifier_recInput.comp hroot) hx).and
        (Primrec.eq.comp (verifier_recOutput.comp hroot) hy)))
  have huses := Primrec.list_flatMap hnodes
    (((Primrec.ofNat (List ℕ)).comp (verifier_recChildren.comp Primrec.snd)).to₂)
  have hti : Primrec (fun p : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => p.1.2) :=
    ht.comp Primrec.fst
  have hii : Primrec (fun p : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => p.2) := Primrec.snd
  have hframe := verifier_frameCheck.comp hti hii
  have hchildren := (Primrec.ofNat (List ℕ)).comp
    (verifier_recChildren.comp (verifier_recAt.comp hti hii))
  have hearlier := verifier_list_all hchildren
    (Primrec.nat_lt.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).decide.to₂
  have hcount := verifier_count.comp ((huses.comp Primrec.fst).pair hii)
  have hrequired := Primrec.ite
    (Primrec.eq.comp (Primrec.succ.comp hii) (hk.comp Primrec.fst))
    (Primrec.const 0) (Primrec.const 1)
  have hrow := Primrec.and.comp (Primrec.and.comp hframe hearlier)
    (Primrec.eq.comp hcount hrequired).decide
  exact (Primrec.and.comp hhead.decide
    (verifier_list_all (Primrec.list_range.comp hk) hrow.to₂)).of_eq (fun _ => rfl)

theorem evidenceCode_primitive : Primrec evidenceCode := by
  have hfilter : Primrec (fun l : List ℕ => l.filter (fun r => recProgram r == 4)) := by
    exact (Primrec.listFilter (Primrec.eq.comp verifier_recProgram (Primrec.const 4))).of_eq
      (fun _ => rfl)
  have htag : Primrec (fun r => tag (recInput r) (recOutput r)) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) verifier_recInput)
      (Primrec.nat_sub.comp (Primrec.const 1) verifier_recOutput)
  exact Primrec.encode.comp (Primrec.list_map
    (hfilter.comp (Primrec.ofNat (List ℕ))) (htag.comp Primrec.snd).to₂)

open OracleComputation (Derives QueryRecord)

private theorem certSound_entry (d j : ℕ) (hj : j < FiniteSequenceCoding.length d) :
    FiniteSequenceCoding.entry d j = (FiniteSequenceCoding.decode d)[j] := by
  rw [FiniteSequenceCoding.entry, List.getElem?_eq_getElem (show j < (FiniteSequenceCoding.decode d).length from hj)]
  rfl

private theorem certSound_entry_mem (d j : ℕ) (hj : j < FiniteSequenceCoding.length d) :
    FiniteSequenceCoding.entry d j ∈ FiniteSequenceCoding.decode d := by
  rw [certSound_entry d j hj]
  exact List.getElem_mem hj

private theorem certSound_mem_entry (d r : ℕ) (hr : r ∈ FiniteSequenceCoding.decode d) :
    ∃ j < FiniteSequenceCoding.length d, FiniteSequenceCoding.entry d j = r := by
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hr
  exact ⟨j, hj, (certSound_entry d j hj).trans he⟩

private theorem certSound_ofFn (d n : ℕ) (hn : FiniteSequenceCoding.length d = n) :
    FiniteSequenceCoding.decode d = List.ofFn (fun j : Fin n => FiniteSequenceCoding.entry d j.val) := by
  subst n
  conv_lhs => rw [← List.ofFn_getElem (xs := FiniteSequenceCoding.decode d)]
  congr 1
  funext j
  exact (certSound_entry d j.val j.isLt).symm

private theorem certSound_flatMap (d n : ℕ) (hn : FiniteSequenceCoding.length d = n)
    (τ : ℕ → QueryRecord) :
    (FiniteSequenceCoding.decode d).flatMap τ =
      (List.ofFn (fun j : Fin n => τ (FiniteSequenceCoding.entry d j.val))).flatten := by
  rw [certSound_ofFn d n hn]
  simp only [List.flatMap, List.map_ofFn]
  rfl

private theorem certSound_two (d : ℕ) (hd : FiniteSequenceCoding.length d = 2) :
    FiniteSequenceCoding.decode d =
      [FiniteSequenceCoding.entry d 0, FiniteSequenceCoding.entry d 1] := by
  rw [certSound_ofFn d 2 hd, List.ofFn_succ, List.ofFn_succ]
  simp

private theorem certSound_root (e x y t : ℕ) (h : certificateCheck e x y t = true) :
    0 < FiniteSequenceCoding.length t ∧
      recProgram (recAt t (FiniteSequenceCoding.length t - 1)) = e ∧
      recInput (recAt t (FiniteSequenceCoding.length t - 1)) = x ∧
      recOutput (recAt t (FiniteSequenceCoding.length t - 1)) = y := by
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

private theorem certSound_row (e x y t : ℕ) (h : certificateCheck e x y t = true)
    (i : ℕ) (hi : i < FiniteSequenceCoding.length t) :
    frameCheck t i = true ∧
      (∀ j ∈ FiniteSequenceCoding.decode (recChildren (recAt t i)), j < i) ∧
      ((FiniteSequenceCoding.decode t).flatMap
        (fun r => FiniteSequenceCoding.decode (recChildren r))).count i =
          if i + 1 = FiniteSequenceCoding.length t then 0 else 1 := by
  have hr := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 i (List.mem_range.mpr hi)
  obtain ⟨hleft, hcount⟩ := Bool.and_eq_true_iff.mp hr
  obtain ⟨hframe, hear⟩ := Bool.and_eq_true_iff.mp hleft
  exact ⟨hframe, fun j hj => of_decide_eq_true (List.all_eq_true.mp hear j hj),
    of_decide_eq_true hcount⟩

set_option maxHeartbeats 800000 in
private theorem certSound_frame (t i : ℕ) (τ : ℕ → QueryRecord)
    (hf : frameCheck t i = true)
    (hc : ∀ j ∈ FiniteSequenceCoding.decode (recChildren (recAt t i)),
      Derives (decodeCode (recProgram (recAt t j))) (recInput (recAt t j))
        (τ j) (recOutput (recAt t j))) :
    Derives (decodeCode (recProgram (recAt t i))) (recInput (recAt t i))
      (if recProgram (recAt t i) = 4 then [(recInput (recAt t i), recOutput (recAt t i))]
       else (FiniteSequenceCoding.decode (recChildren (recAt t i))).flatMap τ)
      (recOutput (recAt t i)) := by
  generalize he : recProgram (recAt t i) = p at hf ⊢
  rcases p with _ | p
  · have hh := hf
    simp only [frameCheck, he, decide_eq_true_eq] at hh
    obtain ⟨hk, hy⟩ := hh
    have hnil : FiniteSequenceCoding.decode (recChildren (recAt t i)) = [] := List.eq_nil_of_length_eq_zero hk
    simpa [decodeCode, hnil, hy] using Derives.zero (recInput (recAt t i))
  rcases p with _ | p
  · have hh := hf
    simp only [frameCheck, he, decide_eq_true_eq] at hh
    obtain ⟨hk, hy⟩ := hh
    have hnil : FiniteSequenceCoding.decode (recChildren (recAt t i)) = [] := List.eq_nil_of_length_eq_zero hk
    simpa [decodeCode, hnil, hy] using Derives.succ (recInput (recAt t i))
  rcases p with _ | p
  · have hh := hf
    simp only [frameCheck, he, decide_eq_true_eq] at hh
    obtain ⟨hk, hy⟩ := hh
    have hnil : FiniteSequenceCoding.decode (recChildren (recAt t i)) = [] := List.eq_nil_of_length_eq_zero hk
    simpa [decodeCode, hnil, hy] using Derives.left (recInput (recAt t i))
  rcases p with _ | p
  · have hh := hf
    simp only [frameCheck, he, decide_eq_true_eq] at hh
    obtain ⟨hk, hy⟩ := hh
    have hnil : FiniteSequenceCoding.decode (recChildren (recAt t i)) = [] := List.eq_nil_of_length_eq_zero hk
    simpa [decodeCode, hnil, hy] using Derives.right (recInput (recAt t i))
  rcases p with _ | p
  · have hh := hf
    simp only [frameCheck, he, decide_eq_true_eq] at hh
    have hb : recOutput (recAt t i) = 0 ∨ recOutput (recAt t i) = 1 := by omega
    simpa [decodeCode] using Derives.query (recInput (recAt t i)) (recOutput (recAt t i)) hb
  change recProgram (recAt t i) = p + 5 at he
  have hn4 : p + 1 + 1 + 1 + 1 + 1 ≠ 4 := by omega
  simp only [ite_eq_right hn4]
  change Derives (decodeCode (p + 5)) (recInput (recAt t i))
    ((FiniteSequenceCoding.decode (recChildren (recAt t i))).flatMap τ) (recOutput (recAt t i))
  have hb := Nat.mod_lt p (by decide : 0 < 4)
  interval_cases hmod : p % 4
  · have hh := hf
    simp only [frameCheck, he, hmod, decide_eq_true_eq] at hh
    obtain ⟨hk, hpc, hpd, hxc, hxd, hy⟩ := hh
    have ha := hc (FiniteSequenceCoding.entry (recChildren (recAt t i)) 0)
      (certSound_entry_mem _ _ (by omega))
    have hb := hc (FiniteSequenceCoding.entry (recChildren (recAt t i)) 1)
      (certSound_entry_mem _ _ (by omega))
    change Derives (decodeCode (recProgram (childAt t i 0))) (recInput (childAt t i 0))
      (τ (FiniteSequenceCoding.entry (recChildren (recAt t i)) 0)) (recOutput (childAt t i 0)) at ha
    change Derives (decodeCode (recProgram (childAt t i 1))) (recInput (childAt t i 1))
      (τ (FiniteSequenceCoding.entry (recChildren (recAt t i)) 1)) (recOutput (childAt t i 1)) at hb
    rw [hpc, hxc] at ha
    rw [hpd, hxd] at hb
    have hd := Derives.pair ha hb
    rw [decodeCode, hmod]
    simpa only [certSound_two _ hk, List.flatMap_cons, List.flatMap_nil, List.append_nil, hy] using hd
  · have hh := hf
    simp only [frameCheck, he, hmod, Bool.and_eq_true_iff, decide_eq_true_eq] at hh
    obtain ⟨⟨hk, hpc, hxc, hy⟩, hsteps⟩ := hh
    let n := (recInput (recAt t i)).unpair.2
    let a := (recInput (recAt t i)).unpair.1
    let values : Fin (n+1) → ℕ := fun j => recOutput (childAt t i j.val)
    let records : Fin (n+1) → QueryRecord :=
      fun j => τ (FiniteSequenceCoding.entry (recChildren (recAt t i)) j.val)
    have hchild (j : Fin (n+1)) := hc (FiniteSequenceCoding.entry (recChildren (recAt t i)) j.val)
      (certSound_entry_mem _ _ (by omega))
    have hbase : Derives (decodeCode (p/4).unpair.1) a (records 0) (values 0) := by
      have h := hchild 0
      change Derives (decodeCode (recProgram (childAt t i 0))) (recInput (childAt t i 0)) _ _ at h
      rw [hpc, hxc] at h
      exact h
    have hstep (j : Fin n) : Derives (decodeCode (p/4).unpair.2)
        (Nat.pair a (Nat.pair j.val (values j.castSucc))) (records j.succ) (values j.succ) := by
      have hs := of_decide_eq_true (List.all_eq_true.mp hsteps j.val (List.mem_range.mpr j.isLt))
      obtain ⟨hpj, hxj⟩ := hs
      have h := hchild j.succ
      change Derives (decodeCode (recProgram (childAt t i (j.val+1))))
        (recInput (childAt t i (j.val+1))) _ _ at h
      rw [hpj, hxj] at h
      exact h
    have hd := (OracleComputation.derives_prec_chain (decodeCode (p/4).unpair.1)
      (decodeCode (p/4).unpair.2) a n (recOutput (recAt t i))
      ((FiniteSequenceCoding.decode (recChildren (recAt t i))).flatMap τ)).mpr
      ⟨values, records, hbase, hstep, certSound_flatMap _ (n+1) hk τ, hy⟩
    rw [decodeCode, hmod]
    simpa only [a, n, Nat.pair_unpair] using hd
  · have hh := hf
    simp only [frameCheck, he, hmod, decide_eq_true_eq] at hh
    obtain ⟨hk, hpc, hpd, hxc, hxd, hy⟩ := hh
    have ha := hc (FiniteSequenceCoding.entry (recChildren (recAt t i)) 0)
      (certSound_entry_mem _ _ (by omega))
    have hb := hc (FiniteSequenceCoding.entry (recChildren (recAt t i)) 1)
      (certSound_entry_mem _ _ (by omega))
    change Derives (decodeCode (recProgram (childAt t i 0))) (recInput (childAt t i 0))
      (τ (FiniteSequenceCoding.entry (recChildren (recAt t i)) 0)) (recOutput (childAt t i 0)) at ha
    change Derives (decodeCode (recProgram (childAt t i 1))) (recInput (childAt t i 1))
      (τ (FiniteSequenceCoding.entry (recChildren (recAt t i)) 1)) (recOutput (childAt t i 1)) at hb
    rw [hpc, hxc] at ha
    rw [hpd, hxd] at hb
    have hd := Derives.comp ha hb
    rw [decodeCode, hmod]
    simpa only [certSound_two _ hk, List.flatMap_cons, List.flatMap_nil, List.append_nil, hy] using hd
  · have hh := hf
    simp only [frameCheck, he, hmod, Bool.and_eq_true_iff, decide_eq_true_eq] at hh
    obtain ⟨⟨hle, hk⟩, hsteps⟩ := hh
    let m := (recInput (recAt t i)).unpair.2
    let a := (recInput (recAt t i)).unpair.1
    let y := recOutput (recAt t i)
    let values : Fin (y-m+1) → ℕ := fun j => recOutput (childAt t i j.val)
    let records : Fin (y-m+1) → QueryRecord :=
      fun j => τ (FiniteSequenceCoding.entry (recChildren (recAt t i)) j.val)
    have hs (j : Fin (y-m+1)) := List.all_eq_true.mp hsteps j.val
      (List.mem_range.mpr (by omega))
    have hdj (j : Fin (y-m+1)) : Derives (decodeCode (p/4)) (Nat.pair a (m+j.val))
        (records j) (values j) := by
      obtain ⟨hhead, _⟩ := Bool.and_eq_true_iff.mp (hs j)
      obtain ⟨hpj, hxj⟩ := of_decide_eq_true hhead
      have h := hc (FiniteSequenceCoding.entry (recChildren (recAt t i)) j.val)
        (certSound_entry_mem _ _ (by omega))
      change Derives (decodeCode (recProgram (childAt t i j.val)))
        (recInput (childAt t i j.val)) _ _ at h
      rw [hpj, hxj] at h
      exact h
    have hpos (j : Fin (y-m)) : 0 < values j.castSucc := by
      have hj := (Bool.and_eq_true_iff.mp (hs j.castSucc)).2
      have hn : j.val + 1 ≠ FiniteSequenceCoding.length (recChildren (recAt t i)) := by omega
      simp only [Fin.val_castSucc] at hj
      rw [ite_eq_right hn] at hj
      exact of_decide_eq_true hj
    have hzero : values (Fin.last (y-m)) = 0 := by
      have hj := (Bool.and_eq_true_iff.mp (hs (Fin.last (y-m)))).2
      have hn : (Fin.last (y-m)).val + 1 = FiniteSequenceCoding.length (recChildren (recAt t i)) := by
        simp only [Fin.val_last]; omega
      rw [ite_eq_left hn] at hj
      exact of_decide_eq_true hj
    have hd := (OracleComputation.derives_find_chain (decodeCode (p/4)) a m y
      ((FiniteSequenceCoding.decode (recChildren (recAt t i))).flatMap τ)).mpr
      ⟨hle, values, records, hdj, hpos, hzero, certSound_flatMap _ (y-m+1) hk τ⟩
    rw [decodeCode, hmod]
    simpa only [a, m, y, Nat.pair_unpair] using hd

private def certSound_trace (t i : ℕ) : QueryRecord :=
  if recProgram (recAt t i) = 4 then [(recInput (recAt t i), recOutput (recAt t i))]
  else (FiniteSequenceCoding.decode (recChildren (recAt t i))).flatMap
    (fun j => if _h : j < i then certSound_trace t j else [])
termination_by i

private theorem certSound_trace_eq (t i : ℕ)
    (he : ∀ j ∈ FiniteSequenceCoding.decode (recChildren (recAt t i)), j < i) :
    certSound_trace t i =
      if recProgram (recAt t i) = 4 then [(recInput (recAt t i), recOutput (recAt t i))]
      else (FiniteSequenceCoding.decode (recChildren (recAt t i))).flatMap (certSound_trace t) := by
  rw [certSound_trace]
  split
  · rfl
  · apply List.flatMap_congr
    intro j hj
    rw [dite_eq_left (he j hj)]

private theorem certSound_native (e x y t : ℕ) (h : certificateCheck e x y t = true) :
    ∀ i < FiniteSequenceCoding.length t,
      Derives (decodeCode (recProgram (recAt t i))) (recInput (recAt t i))
        (certSound_trace t i) (recOutput (recAt t i)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have hr := certSound_row e x y t h i hi
    rw [certSound_trace_eq t i hr.2.1]
    apply certSound_frame t i (certSound_trace t) hr.1
    intro j hj
    exact ih j (hr.2.1 j hj) ((hr.2.1 j hj).trans hi)

private theorem certSound_origin (e x y t : ℕ) (h : certificateCheck e x y t = true) :
    ∀ i < FiniteSequenceCoding.length t, ∀ q b, (q,b) ∈ certSound_trace t i →
      ∃ j < FiniteSequenceCoding.length t, recProgram (recAt t j) = 4 ∧
        q = recInput (recAt t j) ∧ b = recOutput (recAt t j) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi q b hm
    have hr := certSound_row e x y t h i hi
    rw [certSound_trace_eq t i hr.2.1] at hm
    by_cases hp : recProgram (recAt t i) = 4
    · rw [ite_eq_left hp] at hm
      have he := List.mem_singleton.mp hm
      exact ⟨i, hi, hp, congrArg Prod.fst he, congrArg Prod.snd he⟩
    · rw [ite_eq_right hp] at hm
      obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp hm
      exact ih j (hr.2.1 j hj) ((hr.2.1 j hj).trans hi) q b hm

private theorem certSound_parent (e x y t : ℕ) (h : certificateCheck e x y t = true)
    (j : ℕ) (hj : j < FiniteSequenceCoding.length t)
    (hne : j+1 ≠ FiniteSequenceCoding.length t) :
    ∃ i < FiniteSequenceCoding.length t,
      j < i ∧ j ∈ FiniteSequenceCoding.decode (recChildren (recAt t i)) := by
  have hc := (certSound_row e x y t h j hj).2.2
  rw [ite_eq_right hne] at hc
  have hm : j ∈ (FiniteSequenceCoding.decode t).flatMap
      (fun r => FiniteSequenceCoding.decode (recChildren r)) := List.count_pos_iff.mp (by omega)
  obtain ⟨r, hr, hjr⟩ := List.mem_flatMap.mp hm
  obtain ⟨i, hi, he⟩ := certSound_mem_entry t r hr
  have hji : j ∈ FiniteSequenceCoding.decode (recChildren (recAt t i)) := by
    simpa only [recAt, he] using hjr
  exact ⟨i, hi, (certSound_row e x y t h i hi).2.1 j hji, hji⟩

private theorem certSound_child_subset (e x y t : ℕ) (h : certificateCheck e x y t = true)
    (i : ℕ) (hi : i < FiniteSequenceCoding.length t) (j : ℕ)
    (hj : j ∈ FiniteSequenceCoding.decode (recChildren (recAt t i))) :
    ∀ z ∈ certSound_trace t j, z ∈ certSound_trace t i := by
  have hr := certSound_row e x y t h i hi
  have hn : recProgram (recAt t i) ≠ 4 := by
    intro hp
    have hf := hr.1
    simp only [frameCheck, hp, decide_eq_true_eq] at hf
    have hnil : FiniteSequenceCoding.decode (recChildren (recAt t i)) = [] :=
      List.eq_nil_of_length_eq_zero hf.1
    rw [hnil] at hj
    exact List.not_mem_nil hj
  intro z hz
  rw [certSound_trace_eq t i hr.2.1, ite_eq_right hn]
  exact List.mem_flatMap.mpr ⟨j, hj, hz⟩

private theorem certSound_climb (e x y t : ℕ) (h : certificateCheck e x y t = true)
    (j : ℕ) (hj : j < FiniteSequenceCoding.length t) :
    ∀ z ∈ certSound_trace t j,
      z ∈ certSound_trace t (FiniteSequenceCoding.length t - 1) := by
  have go : ∀ n j, j < FiniteSequenceCoding.length t →
      FiniteSequenceCoding.length t - 1 - j = n → ∀ z ∈ certSound_trace t j,
      z ∈ certSound_trace t (FiniteSequenceCoding.length t - 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj he z hz
      by_cases hroot : j = FiniteSequenceCoding.length t - 1
      · simpa only [hroot] using hz
      · have hn : j+1 ≠ FiniteSequenceCoding.length t := by omega
        obtain ⟨i, hi, hji, hchild⟩ := certSound_parent e x y t h j hj hn
        exact ih (FiniteSequenceCoding.length t - 1 - i) (by omega) i hi rfl z
          (certSound_child_subset e x y t h i hi j hchild z hz)
  exact go (FiniteSequenceCoding.length t - 1 - j) j hj rfl

private theorem certSound_evidence (t z : ℕ) :
    z ∈ finiteSet (evidenceCode t) ↔
      ∃ j < FiniteSequenceCoding.length t, recProgram (recAt t j) = 4 ∧
        z = tag (recInput (recAt t j)) (recOutput (recAt t j)) := by
  simp only [finiteSet, evidenceCode, FiniteSequenceCoding.decode_code, List.mem_toFinset,
    List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨r, ⟨hr, hp⟩, hz⟩
    obtain ⟨j, hj, he⟩ := certSound_mem_entry t r hr
    refine ⟨j, hj, ?_, ?_⟩
    · simpa only [recAt, he] using hp
    · simpa only [recAt, he] using hz.symm
  · rintro ⟨j, hj, hp, hz⟩
    exact ⟨recAt t j, ⟨certSound_entry_mem t j hj, hp⟩, hz.symm⟩

theorem certificate_sound (e x y t : ℕ) (h : certificateCheck e x y t = true) :
    ∃ τ, OracleComputation.Derives (decodeCode e) x τ y ∧
      traceEvidence τ = finiteSet (evidenceCode t) := by
  have hr := certSound_root e x y t h
  have hlast : FiniteSequenceCoding.length t - 1 < FiniteSequenceCoding.length t := by omega
  refine ⟨certSound_trace t (FiniteSequenceCoding.length t - 1), ?_, ?_⟩
  · have hn := certSound_native e x y t h _ hlast
    simpa only [hr.2.1, hr.2.2.1, hr.2.2.2] using hn
  · apply Finset.ext
    intro z
    constructor
    · intro hz
      simp only [traceEvidence, List.mem_toFinset, List.mem_map] at hz
      obtain ⟨⟨q,b⟩, hm, rfl⟩ := hz
      obtain ⟨j, hj, hp, hq, hb⟩ := certSound_origin e x y t h _ hlast q b hm
      exact (certSound_evidence t _).mpr ⟨j, hj, hp, by rw [hq,hb]⟩
    · intro hz
      obtain ⟨j, hj, hp, rfl⟩ := (certSound_evidence t z).mp hz
      have hself : (recInput (recAt t j),recOutput (recAt t j)) ∈ certSound_trace t j := by
        rw [certSound_trace]
        simp only [hp, ↓reduceIte, List.mem_singleton]
      have hm := certSound_climb e x y t h j hj _ hself
      simp only [traceEvidence, List.mem_toFinset, List.mem_map]
      exact ⟨_, hm, rfl⟩

private def complete_record (p x y : ℕ) (children : List ℕ) : ℕ :=
  Nat.pair p (Nat.pair x (Nat.pair y (FiniteSequenceCoding.code children)))

private theorem complete_record_fields (p x y : ℕ) (children : List ℕ) :
    recProgram (complete_record p x y children) = p ∧
    recInput (complete_record p x y children) = x ∧
    recOutput (complete_record p x y children) = y ∧
    FiniteSequenceCoding.decode (recChildren (complete_record p x y children)) = children := by
  simp [complete_record, recProgram, recInput, recOutput, recChildren]

private def complete_shift (o r : ℕ) : ℕ := complete_record (recProgram r) (recInput r) (recOutput r)
  ((FiniteSequenceCoding.decode (recChildren r)).map (fun j => o+j))

private theorem complete_shift_fields (o r : ℕ) :
    recProgram (complete_shift o r) = recProgram r ∧
    recInput (complete_shift o r) = recInput r ∧
    recOutput (complete_shift o r) = recOutput r ∧
    FiniteSequenceCoding.decode (recChildren (complete_shift o r)) =
      (FiniteSequenceCoding.decode (recChildren r)).map (fun j => o+j) :=
  complete_record_fields _ _ _ _

private def complete_uses (nodes : List ℕ) : List ℕ :=
  nodes.flatMap (fun r => FiniteSequenceCoding.decode (recChildren r))

private def complete_forest (nodes roots : List ℕ) : Prop :=
  (∀ r ∈ roots, r < nodes.length) ∧
  (∀ i < nodes.length, frameCheck (FiniteSequenceCoding.code nodes) i = true ∧
    ∀ j ∈ FiniteSequenceCoding.decode (recChildren (recAt (FiniteSequenceCoding.code nodes) i)), j < i) ∧
  (∀ i < nodes.length, (complete_uses nodes).count i + roots.count i = 1)

private theorem complete_recAt (nodes : List ℕ) (i : ℕ) :
    recAt (FiniteSequenceCoding.code nodes) i = nodes[i]?.getD 0 := by
  simp [recAt, FiniteSequenceCoding.entry]

private theorem complete_childAt (nodes : List ℕ) (i j : ℕ) :
    childAt (FiniteSequenceCoding.code nodes) i j =
      nodes[(FiniteSequenceCoding.decode (recChildren (nodes[i]?.getD 0)))[j]?.getD 0]?.getD 0 := by
  simp [childAt, complete_recAt, FiniteSequenceCoding.entry]

private def complete_frameFn (p x y k : ℕ) (cp cx cy : ℕ → ℕ) : Bool :=
  match p with
  | 0 => decide (k = 0 ∧ y = 0)
  | 1 => decide (k = 0 ∧ y = x + 1)
  | 2 => decide (k = 0 ∧ y = x.unpair.1)
  | 3 => decide (k = 0 ∧ y = x.unpair.2)
  | 4 => decide (k = 0 ∧ y ≤ 1)
  | p + 5 =>
    let m := p / 4
    match p % 4 with
    | 0 => decide (k = 2 ∧ cp 0 = m.unpair.1 ∧ cp 1 = m.unpair.2 ∧
        cx 0 = x ∧ cx 1 = x ∧ y = Nat.pair (cy 0) (cy 1))
    | 1 =>
      decide (k = x.unpair.2 + 1 ∧ cp 0 = m.unpair.1 ∧ cx 0 = x.unpair.1 ∧
        y = cy (x.unpair.2)) &&
      (List.range x.unpair.2).all (fun j =>
        decide (cp ((j+1)) = m.unpair.2 ∧
          cx ((j+1)) = Nat.pair x.unpair.1 (Nat.pair j (cy (j)))))
    | 2 => decide (k = 2 ∧ cp 0 = m.unpair.2 ∧ cp 1 = m.unpair.1 ∧
        cx 0 = x ∧ cx 1 = cy 0 ∧ y = cy 1)
    | _ =>
      decide (x.unpair.2 ≤ y ∧ k = y - x.unpair.2 + 1) &&
      (List.range k).all (fun j =>
        decide (cp (j) = m ∧
          cx (j) = Nat.pair x.unpair.1 (x.unpair.2 + j)) &&
        if j + 1 = k then decide (cy (j) = 0)
        else decide (0 < cy (j)))

set_option maxHeartbeats 800000 in
private theorem complete_frameFn_ext (p x y k : ℕ) (cp cx cy dp dx dy : ℕ → ℕ)
    (hc : ∀ a < k, cp a = dp a ∧ cx a = dx a ∧ cy a = dy a) :
    complete_frameFn p x y k cp cx cy = true ↔ complete_frameFn p x y k dp dx dy = true := by
  unfold complete_frameFn
  iterate 5 rcases p with _ | p; · rfl
  have hm : p%4 < 4 := Nat.mod_lt p (by decide)
  interval_cases he : p%4
  · simp only [he, decide_eq_true_eq]
    constructor <;> intro h
    · have h0 := hc 0 (by omega)
      have h1 := hc 1 (by omega)
      simpa only [h0.1,h1.1,h0.2.1,h1.2.1,h0.2.2,h1.2.2] using h
    · have h0 := hc 0 (by omega)
      have h1 := hc 1 (by omega)
      simpa only [h0.1,h1.1,h0.2.1,h1.2.1,h0.2.2,h1.2.2] using h
  · simp only [he, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    constructor <;> intro h
    · have h0 := hc 0 (by omega)
      have hn := hc x.unpair.2 (by omega)
      refine ⟨?_,?_⟩
      · simpa only [h0.1,h0.2.1,hn.2.2] using h.1
      · intro a ha
        have hA := hc a (by omega)
        have hB := hc (a+1) (by omega)
        simpa only [hB.1,hB.2.1,hA.2.2] using h.2 a ha
    · have h0 := hc 0 (by omega)
      have hn := hc x.unpair.2 (by omega)
      refine ⟨?_,?_⟩
      · simpa only [h0.1,h0.2.1,hn.2.2] using h.1
      · intro a ha
        have hA := hc a (by omega)
        have hB := hc (a+1) (by omega)
        simpa only [hB.1,hB.2.1,hA.2.2] using h.2 a ha
  · simp only [he, decide_eq_true_eq]
    constructor <;> intro h
    · have h0 := hc 0 (by omega)
      have h1 := hc 1 (by omega)
      simpa only [h0.1,h1.1,h0.2.1,h1.2.1,h0.2.2,h1.2.2] using h
    · have h0 := hc 0 (by omega)
      have h1 := hc 1 (by omega)
      simpa only [h0.1,h1.1,h0.2.1,h1.2.1,h0.2.2,h1.2.2] using h
  · simp only [he, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    constructor <;> intro h
    · refine ⟨h.1,?_⟩
      intro a ha
      have hA := hc a ha
      simpa only [hA.1,hA.2.1,hA.2.2] using h.2 a ha
    · refine ⟨h.1,?_⟩
      intro a ha
      have hA := hc a ha
      simpa only [hA.1,hA.2.1,hA.2.2] using h.2 a ha

private theorem complete_frame_ext (t i u j : ℕ)
    (hp : recProgram (recAt t i) = recProgram (recAt u j))
    (hx : recInput (recAt t i) = recInput (recAt u j))
    (hy : recOutput (recAt t i) = recOutput (recAt u j))
    (hk : FiniteSequenceCoding.length (recChildren (recAt t i)) =
      FiniteSequenceCoding.length (recChildren (recAt u j)))
    (hc : ∀ a < FiniteSequenceCoding.length (recChildren (recAt t i)),
      recProgram (childAt t i a) = recProgram (childAt u j a) ∧
      recInput (childAt t i a) = recInput (childAt u j a) ∧
      recOutput (childAt t i a) = recOutput (childAt u j a)) :
    frameCheck t i = true ↔ frameCheck u j = true := by
  change complete_frameFn (recProgram (recAt t i)) (recInput (recAt t i)) (recOutput (recAt t i))
      (FiniteSequenceCoding.length (recChildren (recAt t i)))
      (fun a => recProgram (childAt t i a)) (fun a => recInput (childAt t i a))
      (fun a => recOutput (childAt t i a)) = true ↔
    complete_frameFn (recProgram (recAt u j)) (recInput (recAt u j)) (recOutput (recAt u j))
      (FiniteSequenceCoding.length (recChildren (recAt u j)))
      (fun a => recProgram (childAt u j a)) (fun a => recInput (childAt u j a))
      (fun a => recOutput (childAt u j a)) = true
  simp only [← hp, ← hx, ← hy, ← hk]
  exact complete_frameFn_ext _ _ _ _ _ _ _ _ _ _ hc

private theorem complete_frame_pair_iff (c d : OracleComputation.Code) (x y k : ℕ)
    (cp cx cy : ℕ → ℕ) :
    complete_frameFn (encodeCode (.pair c d)) x y k cp cx cy = true ↔
      k = 2 ∧ cp 0 = encodeCode c ∧ cp 1 = encodeCode d ∧
        cx 0 = x ∧ cx 1 = x ∧ y = Nat.pair (cy 0) (cy 1) := by
  rw [encodeCode, Nat.add_comm 5, complete_frameFn]
  simp

private theorem complete_frame_comp_iff (c d : OracleComputation.Code) (x y k : ℕ)
    (cp cx cy : ℕ → ℕ) :
    complete_frameFn (encodeCode (.comp c d)) x y k cp cx cy = true ↔
      k = 2 ∧ cp 0 = encodeCode d ∧ cp 1 = encodeCode c ∧
        cx 0 = x ∧ cx 1 = cy 0 ∧ y = cy 1 := by
  rw [encodeCode, show 7 + 4 * Nat.pair (encodeCode c) (encodeCode d) =
    (4 * Nat.pair (encodeCode c) (encodeCode d) + 2) + 5 by omega, complete_frameFn]
  simp [Nat.add_div]

private theorem complete_frame_prec_iff (c d : OracleComputation.Code) (a n y k : ℕ)
    (cp cx cy : ℕ → ℕ) :
    complete_frameFn (encodeCode (.prec c d)) (Nat.pair a n) y k cp cx cy = true ↔
      k = n + 1 ∧ cp 0 = encodeCode c ∧ cx 0 = a ∧ y = cy n ∧
        ∀ j < n, cp (j+1) = encodeCode d ∧ cx (j+1) = Nat.pair a (Nat.pair j (cy j)) := by
  rw [encodeCode, show 6 + 4 * Nat.pair (encodeCode c) (encodeCode d) =
    (4 * Nat.pair (encodeCode c) (encodeCode d) + 1) + 5 by omega, complete_frameFn]
  simp [Nat.add_div, List.all_eq_true, List.mem_range, and_assoc]

private theorem complete_frame_find_iff (c : OracleComputation.Code) (a m y k : ℕ)
    (cp cx cy : ℕ → ℕ) :
    complete_frameFn (encodeCode (.find' c)) (Nat.pair a m) y k cp cx cy = true ↔
      m ≤ y ∧ k = y - m + 1 ∧ ∀ j < k,
        cp j = encodeCode c ∧ cx j = Nat.pair a (m+j) ∧
          (if j+1 = k then cy j = 0 else 0 < cy j) := by
  rw [encodeCode, show 8 + 4 * encodeCode c = (4 * encodeCode c + 3) + 5 by omega,
    complete_frameFn]
  have hdiv : (4 * encodeCode c + 3) / 4 = encodeCode c := by omega
  simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.reduceMod, hdiv, Nat.unpair_pair,
    Bool.and_eq_true_iff, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨⟨hmy,hk⟩,hs⟩
    refine ⟨hmy,hk,?_⟩
    intro j hj
    obtain ⟨⟨hp,hx⟩,hy⟩ := hs j hj
    refine ⟨hp,hx,?_⟩
    split <;> rename_i he
    · simpa only [ite_eq_left he, decide_eq_true_eq] using hy
    · simpa only [ite_eq_right he, decide_eq_true_eq] using hy
  · rintro ⟨hmy,hk,hs⟩
    refine ⟨⟨hmy,hk⟩,?_⟩
    intro j hj
    obtain ⟨hp,hx,hy⟩ := hs j hj
    refine ⟨⟨hp,hx⟩,?_⟩
    split <;> rename_i he
    · simpa only [ite_eq_left he, decide_eq_true_eq] using hy
    · simpa only [ite_eq_right he, decide_eq_true_eq] using hy

private theorem complete_left_recAt (ns ms : List ℕ) (i : ℕ) (hi : i < ns.length) :
    recAt (FiniteSequenceCoding.code (ns ++ ms)) i = recAt (FiniteSequenceCoding.code ns) i := by
  simp [complete_recAt,List.getElem?_append,hi]

private theorem complete_right_recAt (ns ms : List ℕ) (i : ℕ) (hi : i < ms.length) :
    recAt (FiniteSequenceCoding.code (ns ++ ms.map (complete_shift ns.length))) (ns.length+i) =
      complete_shift ns.length (recAt (FiniteSequenceCoding.code ms) i) := by
  simp [complete_recAt,List.getElem?_append,List.getElem?_map,
    List.getElem?_eq_getElem hi]

private theorem complete_entry_mem (c a : ℕ) (ha : a < FiniteSequenceCoding.length c) :
    FiniteSequenceCoding.entry c a ∈ FiniteSequenceCoding.decode c := by
  change a < (FiniteSequenceCoding.decode c).length at ha
  simp only [FiniteSequenceCoding.entry,List.getElem?_eq_getElem ha,Option.getD_some]
  exact List.getElem_mem ha

private theorem complete_frame_left (ns ms : List ℕ) (i : ℕ) (hi : i < ns.length)
    (hc : ∀ j ∈ FiniteSequenceCoding.decode
      (recChildren (recAt (FiniteSequenceCoding.code ns) i)), j < ns.length) :
    frameCheck (FiniteSequenceCoding.code (ns++ms)) i = true ↔
      frameCheck (FiniteSequenceCoding.code ns) i = true := by
  have hr := complete_left_recAt ns ms i hi
  apply complete_frame_ext
  · exact congrArg recProgram hr
  · exact congrArg recInput hr
  · exact congrArg recOutput hr
  · exact congrArg (fun r => FiniteSequenceCoding.length (recChildren r)) hr
  · intro a ha
    have ha' : a < FiniteSequenceCoding.length
        (recChildren (recAt (FiniteSequenceCoding.code ns) i)) := by simpa only [hr] using ha
    have hj := hc _ (complete_entry_mem _ _ ha')
    have hchild : childAt (FiniteSequenceCoding.code (ns++ms)) i a =
        childAt (FiniteSequenceCoding.code ns) i a := by
      unfold childAt
      rw [hr]
      exact complete_left_recAt ns ms _ hj
    exact ⟨congrArg recProgram hchild,congrArg recInput hchild,congrArg recOutput hchild⟩

private theorem complete_shift_entry (o r a : ℕ)
    (ha : a < FiniteSequenceCoding.length (recChildren r)) :
    FiniteSequenceCoding.entry (recChildren (complete_shift o r)) a =
      o + FiniteSequenceCoding.entry (recChildren r) a := by
  change a < (FiniteSequenceCoding.decode (recChildren r)).length at ha
  simp only [FiniteSequenceCoding.entry,(complete_shift_fields o r).2.2.2,
    List.getElem?_map,List.getElem?_eq_getElem ha,Option.map_some,Option.getD_some]

private theorem complete_frame_right (ns ms : List ℕ) (i : ℕ) (hi : i < ms.length)
    (hc : ∀ j ∈ FiniteSequenceCoding.decode
      (recChildren (recAt (FiniteSequenceCoding.code ms) i)), j < ms.length) :
    frameCheck (FiniteSequenceCoding.code (ns++ms.map (complete_shift ns.length))) (ns.length+i) = true ↔
      frameCheck (FiniteSequenceCoding.code ms) i = true := by
  have hr := complete_right_recAt ns ms i hi
  have hs := complete_shift_fields ns.length (recAt (FiniteSequenceCoding.code ms) i)
  have hk : FiniteSequenceCoding.length
      (recChildren (recAt (FiniteSequenceCoding.code (ns++ms.map (complete_shift ns.length))) (ns.length+i))) =
        FiniteSequenceCoding.length (recChildren (recAt (FiniteSequenceCoding.code ms) i)) := by
    simp only [hr,FiniteSequenceCoding.length,hs.2.2.2,List.length_map]
  apply complete_frame_ext
  · exact (congrArg recProgram hr).trans hs.1
  · exact (congrArg recInput hr).trans hs.2.1
  · exact (congrArg recOutput hr).trans hs.2.2.1
  · exact hk
  · intro a ha
    have ha' : a < FiniteSequenceCoding.length (recChildren (recAt (FiniteSequenceCoding.code ms) i)) := hk ▸ ha
    have hj := hc _ (complete_entry_mem _ _ ha')
    have hchild : childAt (FiniteSequenceCoding.code (ns++ms.map (complete_shift ns.length))) (ns.length+i) a =
        complete_shift ns.length (childAt (FiniteSequenceCoding.code ms) i a) := by
      unfold childAt
      rw [hr,complete_shift_entry ns.length _ _ ha']
      exact complete_right_recAt ns ms _ hj
    have hschild := complete_shift_fields ns.length (childAt (FiniteSequenceCoding.code ms) i a)
    exact ⟨(congrArg recProgram hchild).trans hschild.1,
      (congrArg recInput hchild).trans hschild.2.1,
      (congrArg recOutput hchild).trans hschild.2.2.1⟩

private theorem complete_uses_append (ns ms : List ℕ) :
    complete_uses (ns++ms) = complete_uses ns ++ complete_uses ms := by
  simp [complete_uses]

private theorem complete_uses_shift (ns : List ℕ) (o : ℕ) :
    complete_uses (ns.map (complete_shift o)) = (complete_uses ns).map (fun j => o+j) := by
  unfold complete_uses
  rw [List.flatMap_map,List.map_flatMap]
  congr 1
  funext r
  exact (complete_shift_fields o r).2.2.2

private theorem complete_count_shift_lt (l : List ℕ) (o i : ℕ) (hi : i < o) :
    (l.map (fun j => o+j)).count i = 0 := by
  apply List.count_eq_zero.mpr
  intro hm
  obtain ⟨j,_,hj⟩ := List.mem_map.mp hm
  omega

private theorem complete_count_shift (l : List ℕ) (o i : ℕ) :
    (l.map (fun j => o+j)).count (o+i) = l.count i := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a = i
    · subst a
      simp [ih]
    · simp [ih,h]

private theorem complete_uses_bound (ns rs : List ℕ) (hf : complete_forest ns rs) :
    ∀ j ∈ complete_uses ns, j < ns.length := by
  intro j hj
  obtain ⟨r,hr,hjr⟩ := List.mem_flatMap.mp hj
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hr
  have hr' : recAt (FiniteSequenceCoding.code ns) i = r := by
    simpa only [complete_recAt,List.getElem?_eq_getElem hi,Option.getD_some] using he
  exact ((hf.2.1 i hi).2 j (by rwa [hr'])).trans hi

private theorem complete_count_bound (l : List ℕ) (n i : ℕ)
    (hb : ∀ j ∈ l, j < n) (hi : n ≤ i) : l.count i = 0 := by
  apply List.count_eq_zero.mpr
  intro hm
  have := hb i hm
  omega

private theorem complete_check_forest (e x y t : ℕ) (h : certificateCheck e x y t = true) :
    complete_forest (FiniteSequenceCoding.decode t) [(FiniteSequenceCoding.decode t).length-1] := by
  have ht := h
  simp only [certificateCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range] at ht
  have hk := ht.1.1
  refine ⟨?_,?_,?_⟩
  · intro r hr
    have he : r = (FiniteSequenceCoding.decode t).length-1 := by simpa using hr
    omega
  · intro i hi
    have hn := ht.2 i hi
    have hf : frameCheck t i = true := by tauto
    have hc : ∀ j ∈ FiniteSequenceCoding.decode (recChildren (recAt t i)), j < i := by tauto
    simpa only [FiniteSequenceCoding.code_decode] using And.intro hf hc
  · intro i hi
    have hn := ht.2 i hi
    have hc : (complete_uses (FiniteSequenceCoding.decode t)).count i =
        if i+1 = (FiniteSequenceCoding.decode t).length then 0 else 1 := by
      simpa only [complete_uses] using
        (by tauto : ((FiniteSequenceCoding.decode t).flatMap
          (fun r => FiniteSequenceCoding.decode (recChildren r))).count i =
            if i+1 = (FiniteSequenceCoding.decode t).length then 0 else 1)
    by_cases he : i+1 = (FiniteSequenceCoding.decode t).length
    · have hir : i = (FiniteSequenceCoding.decode t).length-1 := by omega
      simp only [he,ite_true] at hc
      rw [hir] at hc
      simp [hir,hc]
    · have hir : (FiniteSequenceCoding.decode t).length-1 ≠ i := by omega
      simp only [he,ite_false] at hc
      simp [hc,hir]

private theorem complete_attach (ns roots : List ℕ) (p x y : ℕ)
    (hf : complete_forest ns roots)
    (hframe : frameCheck (FiniteSequenceCoding.code (ns++[complete_record p x y roots])) ns.length = true) :
    certificateCheck p x y (FiniteSequenceCoding.code (ns++[complete_record p x y roots])) = true := by
  have hroot : recAt (FiniteSequenceCoding.code (ns++[complete_record p x y roots])) ns.length =
      complete_record p x y roots := by
    simp [complete_recAt]
  have huse : complete_uses [complete_record p x y roots] = roots := by
    simp [complete_uses,complete_record,recChildren]
  simp only [certificateCheck,FiniteSequenceCoding.decode_code,List.length_append,List.length_singleton,
    Nat.add_sub_cancel_right,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range]
  refine ⟨⟨by omega,?_,?_,?_⟩,?_⟩
  · rw [hroot]
    exact (complete_record_fields p x y roots).1
  · rw [hroot]
    exact (complete_record_fields p x y roots).2.1
  · rw [hroot]
    exact (complete_record_fields p x y roots).2.2.1
  · intro i hi
    by_cases hil : i < ns.length
    · have hfi := (hf.2.1 i hil).1
      have hci := (hf.2.1 i hil).2
      have hfr : frameCheck (FiniteSequenceCoding.code (ns++[complete_record p x y roots])) i = true :=
        (complete_frame_left ns _ i hil (fun j hj => (hci j hj).trans hil)).mpr hfi
      have hch : ∀ j ∈ FiniteSequenceCoding.decode
          (recChildren (recAt (FiniteSequenceCoding.code (ns++[complete_record p x y roots])) i)), j < i := by
        simpa only [complete_left_recAt ns [complete_record p x y roots] i hil] using hci
      have hcnt : (complete_uses (ns++[complete_record p x y roots])).count i =
          if i+1 = ns.length+1 then 0 else 1 := by
        rw [complete_uses_append,huse,List.count_append]
        have hh : i+1 ≠ ns.length+1 := by omega
        simpa only [hh,ite_false] using hf.2.2 i hil
      tauto
    · have he : i = ns.length := by omega
      subst i
      have hch : ∀ j ∈ FiniteSequenceCoding.decode
          (recChildren (recAt (FiniteSequenceCoding.code (ns++[complete_record p x y roots])) ns.length)),
          j < ns.length := by
        rw [hroot,(complete_record_fields p x y roots).2.2.2]
        exact hf.1
      have hcnt : (complete_uses (ns++[complete_record p x y roots])).count ns.length =
          if ns.length+1 = ns.length+1 then 0 else 1 := by
        rw [complete_uses_append,huse,List.count_append]
        have hu := complete_count_bound (complete_uses ns) ns.length ns.length
          (complete_uses_bound ns roots hf) le_rfl
        have hr := complete_count_bound roots ns.length ns.length hf.1 le_rfl
        simp [hu,hr]
      tauto

private theorem complete_forest_append (ns rs ms ss : List ℕ)
    (hns : complete_forest ns rs) (hms : complete_forest ms ss) :
    complete_forest (ns ++ ms.map (complete_shift ns.length))
      (rs ++ ss.map (fun i => ns.length+i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_append, List.mem_map] at hr
    simp only [List.length_append, List.length_map]
    rcases hr with hr | ⟨j, hj, rfl⟩
    · have hb := hns.1 r hr
      omega
    · have hb := hms.1 j hj
      omega
  · intro i hi
    by_cases hil : i < ns.length
    · have hf := hns.2.1 i hil
      refine ⟨(complete_frame_left ns (ms.map (complete_shift ns.length)) i hil
        (fun j hj => (hf.2 j hj).trans hil)).mpr hf.1, ?_⟩
      simpa only [complete_left_recAt ns (ms.map (complete_shift ns.length)) i hil] using hf.2
    · obtain ⟨j, rfl⟩ : ∃ j, i = ns.length+j := ⟨i-ns.length, by omega⟩
      have hj : j < ms.length := by
        simp only [List.length_append, List.length_map] at hi
        omega
      have hf := hms.2.1 j hj
      refine ⟨(complete_frame_right ns ms j hj
        (fun a ha => (hf.2 a ha).trans hj)).mpr hf.1, ?_⟩
      intro a ha
      rw [complete_right_recAt ns ms j hj,
        (complete_shift_fields ns.length (recAt (FiniteSequenceCoding.code ms) j)).2.2.2] at ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      have hbj := hf.2 b hb
      omega
  · intro i hi
    rw [complete_uses_append, complete_uses_shift, List.count_append, List.count_append]
    by_cases hil : i < ns.length
    · rw [complete_count_shift_lt (complete_uses ms) ns.length i hil,
        complete_count_shift_lt ss ns.length i hil]
      simpa only [Nat.add_zero] using hns.2.2 i hil
    · obtain ⟨j, rfl⟩ : ∃ j, i = ns.length+j := ⟨i-ns.length, by omega⟩
      have hj : j < ms.length := by
        simp only [List.length_append, List.length_map] at hi
        omega
      have hu := complete_count_bound (complete_uses ns) ns.length (ns.length+j)
        (complete_uses_bound ns rs hns) (Nat.le_add_right _ _)
      have hr := complete_count_bound rs ns.length (ns.length+j) hns.1 (Nat.le_add_right _ _)
      rw [hu, hr, complete_count_shift (complete_uses ms) ns.length j,
        complete_count_shift ss ns.length j]
      simpa only [Nat.zero_add] using hms.2.2 j hj

private def complete_evidence (nodes : List ℕ) : Finset ℕ :=
  finiteSet (evidenceCode (FiniteSequenceCoding.code nodes))

private theorem complete_evidence_mem (nodes : List ℕ) (z : ℕ) :
    z ∈ complete_evidence nodes ↔ ∃ r ∈ nodes,
      recProgram r = 4 ∧ tag (recInput r) (recOutput r) = z := by
  simp only [complete_evidence, finiteSet, evidenceCode, FiniteSequenceCoding.decode_code,
    List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq]
  aesop

private theorem complete_evidence_append (ns ms : List ℕ) :
    complete_evidence (ns++ms) = complete_evidence ns ∪ complete_evidence ms := by
  ext z
  simp only [complete_evidence_mem, List.mem_append, Finset.mem_union]
  aesop

private theorem complete_evidence_shift (ns : List ℕ) (o : ℕ) :
    complete_evidence (ns.map (complete_shift o)) = complete_evidence ns := by
  ext z
  simp only [complete_evidence_mem, List.mem_map]
  constructor
  · rintro ⟨r,⟨s,hs,rfl⟩,hp,hz⟩
    exact ⟨s,hs,(complete_shift_fields o s).1 ▸ hp,
      by simpa only [(complete_shift_fields o s).2.1,(complete_shift_fields o s).2.2.1] using hz⟩
  · rintro ⟨r,hr,hp,hz⟩
    exact ⟨complete_shift o r,⟨r,hr,rfl⟩,(complete_shift_fields o r).1.symm ▸ hp,
      by simpa only [(complete_shift_fields o r).2.1,(complete_shift_fields o r).2.2.1] using hz⟩

private theorem complete_evidence_record (p x y : ℕ) (rs : List ℕ) :
    complete_evidence [complete_record p x y rs] = if p=4 then {tag x y} else ∅ := by
  ext z
  simp only [complete_evidence_mem, List.mem_singleton]
  simp only [exists_eq_left, (complete_record_fields p x y rs).1,
    (complete_record_fields p x y rs).2.1, (complete_record_fields p x y rs).2.2.1]
  split <;> simp_all [eq_comm]

private theorem complete_trace_append (σ τ : OracleComputation.QueryRecord) :
    traceEvidence (σ++τ) = traceEvidence σ ∪ traceEvidence τ := by
  ext z
  simp [traceEvidence, List.map_append, List.toFinset_append]

private structure CompleteSpec where
  program : ℕ
  input : ℕ
  output : ℕ
  trace : OracleComputation.QueryRecord

private def complete_matches (nodes roots : List ℕ) (ss : List CompleteSpec) : Prop :=
  List.Forall₂ (fun r s => r < nodes.length ∧
    recProgram (recAt (FiniteSequenceCoding.code nodes) r) = s.program ∧
    recInput (recAt (FiniteSequenceCoding.code nodes) r) = s.input ∧
    recOutput (recAt (FiniteSequenceCoding.code nodes) r) = s.output) roots ss

private def complete_specAt (ss : List CompleteSpec) (i : ℕ) : CompleteSpec :=
  ss[i]?.getD ⟨0,0,0,[]⟩

private theorem complete_matches_at (nodes roots : List ℕ) (ss : List CompleteSpec)
    (h : complete_matches nodes roots ss) (i : ℕ) (hi : i < ss.length) :
    let r := roots[i]?.getD 0
    r < nodes.length ∧
      recProgram (recAt (FiniteSequenceCoding.code nodes) r) = (complete_specAt ss i).program ∧
      recInput (recAt (FiniteSequenceCoding.code nodes) r) = (complete_specAt ss i).input ∧
      recOutput (recAt (FiniteSequenceCoding.code nodes) r) = (complete_specAt ss i).output := by
  have hl := List.Forall₂.length_eq h
  have hr : i < roots.length := by omega
  simpa only [complete_specAt, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hr, Option.getD_some, List.get_eq_getElem] using
      List.Forall₂.get h hr hi

private theorem complete_matches_left (ns ms roots : List ℕ) (ss : List CompleteSpec)
    (h : complete_matches ns roots ss) : complete_matches (ns++ms) roots ss := by
  apply List.Forall₂.imp _ h
  intro r s hr
  refine ⟨by simpa only [List.length_append] using hr.1.trans_le (Nat.le_add_right _ _), ?_⟩
  simpa only [complete_left_recAt ns ms r hr.1] using hr.2

private theorem complete_matches_right (ns ms roots : List ℕ) (ss : List CompleteSpec)
    (h : complete_matches ms roots ss) :
    complete_matches (ns ++ ms.map (complete_shift ns.length))
      (roots.map (fun r => ns.length+r)) ss := by
  rw [complete_matches, List.forall₂_map_left_iff]
  apply List.Forall₂.imp _ h
  intro r s hr
  refine ⟨by simpa only [List.length_append,List.length_map] using Nat.add_lt_add_left hr.1 ns.length, ?_⟩
  rw [complete_right_recAt ns ms r hr.1]
  have hf := complete_shift_fields ns.length (recAt (FiniteSequenceCoding.code ms) r)
  simpa only [hf.1,hf.2.1,hf.2.2.1] using hr.2


private theorem complete_package (ss : List CompleteSpec)
    (hs : ∀ s ∈ ss, ∃ t, certificateCheck s.program s.input s.output t = true ∧
      traceEvidence s.trace = finiteSet (evidenceCode t)) :
    ∃ ns roots, complete_forest ns roots ∧ complete_matches ns roots ss ∧
      complete_evidence ns = traceEvidence (ss.flatMap CompleteSpec.trace) := by
  induction ss with
  | nil =>
    exact ⟨[],[],by simp [complete_forest,complete_uses],.nil,by ext z; simp [complete_evidence_mem,traceEvidence]⟩
  | cons s ss ih =>
    obtain ⟨t,ht,he⟩ := hs s (by simp)
    obtain ⟨ms,rs,hf,hm,hev⟩ := ih (fun u hu => hs u (by simp [hu]))
    let ns := FiniteSequenceCoding.decode t
    let r := ns.length-1
    have htforest : complete_forest ns [r] := complete_check_forest _ _ _ _ ht
    have hh : 0 < ns.length ∧ recProgram (recAt t r) = s.program ∧
        recInput (recAt t r) = s.input ∧ recOutput (recAt t r) = s.output := by
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp ht).1
    have hmatch : complete_matches ns [r] [s] := by
      refine .cons ⟨by dsimp [r]; omega, ?_⟩ .nil
      simpa only [ns,FiniteSequenceCoding.code_decode] using hh.2
    refine ⟨ns ++ ms.map (complete_shift ns.length), [r] ++ rs.map (fun j => ns.length+j),
      complete_forest_append ns [r] ms rs htforest hf, ?_, ?_⟩
    · exact List.rel_append (complete_matches_left ns _ [r] [s] hmatch)
        (complete_matches_right ns ms rs ss hm)
    · rw [complete_evidence_append,complete_evidence_shift,hev]
      have he' : complete_evidence ns = traceEvidence s.trace := by
        simpa only [complete_evidence,ns,FiniteSequenceCoding.code_decode] using he.symm
      rw [he']
      simpa only [List.flatMap_cons] using (complete_trace_append s.trace (ss.flatMap CompleteSpec.trace)).symm

private theorem complete_frameFn_eq (t i : ℕ) :
    frameCheck t i = complete_frameFn (recProgram (recAt t i)) (recInput (recAt t i))
      (recOutput (recAt t i)) (FiniteSequenceCoding.length (recChildren (recAt t i)))
      (fun a => recProgram (childAt t i a)) (fun a => recInput (childAt t i a))
      (fun a => recOutput (childAt t i a)) := rfl

private theorem complete_graft (e x y : ℕ) (ss : List CompleteSpec)
    (hs : ∀ s ∈ ss, ∃ t, certificateCheck s.program s.input s.output t = true ∧
      traceEvidence s.trace = finiteSet (evidenceCode t))
    (hframe : complete_frameFn e x y ss.length
      (fun a => (complete_specAt ss a).program) (fun a => (complete_specAt ss a).input)
      (fun a => (complete_specAt ss a).output) = true) :
    ∃ t, certificateCheck e x y t = true ∧
      (if e=4 then {tag x y} else ∅) ∪ traceEvidence (ss.flatMap CompleteSpec.trace) =
        finiteSet (evidenceCode t) := by
  obtain ⟨ns,roots,hf,hm,hev⟩ := complete_package ss hs
  let node := complete_record e x y roots
  let t := FiniteSequenceCoding.code (ns++[node])
  have hr : recAt t ns.length = node := by
    simp [t,complete_recAt]
  have hlen : roots.length = ss.length := List.Forall₂.length_eq hm
  have hfr : frameCheck t ns.length = true := by
    rw [complete_frameFn_eq,hr]
    simp only [node,complete_record,recProgram,recInput,recOutput,recChildren,Nat.unpair_pair,
      FiniteSequenceCoding.length,FiniteSequenceCoding.decode_code,hlen]
    apply (complete_frameFn_ext _ _ _ _ _ _ _ _ _ _ ?_).mpr hframe
    intro a ha
    have hma := complete_matches_at ns roots ss hm a ha
    have hca : childAt t ns.length a = recAt (FiniteSequenceCoding.code ns) (roots[a]?.getD 0) := by
      unfold childAt
      rw [hr]
      simp only [node,complete_record,recChildren,Nat.unpair_pair,FiniteSequenceCoding.entry,
        FiniteSequenceCoding.decode_code]
      exact complete_left_recAt ns [node] _ hma.1
    simpa only [hca,recProgram,recInput,recOutput] using hma.2
  refine ⟨t,complete_attach ns roots e x y hf hfr,?_⟩
  change _ = complete_evidence (ns++[node])
  rw [complete_evidence_append,complete_evidence_record,hev]
  exact Finset.union_comm _ _

private theorem complete_specAt_ofFn {n : ℕ} (f : Fin n → CompleteSpec) (i : ℕ) (hi : i < n) :
    complete_specAt (List.ofFn f) i = f ⟨i,hi⟩ := by
  simp [complete_specAt,hi]

private theorem complete_specs_trace {n : ℕ} (f : Fin n → CompleteSpec)
    (rs : Fin n → OracleComputation.QueryRecord) (hf : ∀ i, (f i).trace = rs i) :
    (List.ofFn f).flatMap CompleteSpec.trace = (List.ofFn rs).flatten := by
  simp only [List.flatMap,List.map_ofFn,Function.comp_def,hf]

private theorem complete_native (c : OracleComputation.Code) (x y : ℕ)
    (τ : OracleComputation.QueryRecord) (h : OracleComputation.Derives c x τ y) :
    ∃ t, certificateCheck (encodeCode c) x y t = true ∧
      traceEvidence τ = finiteSet (evidenceCode t) := by
  induction c generalizing x y τ with
  | zero =>
    cases h
    obtain ⟨t,ht,he⟩ := complete_graft 0 x 0 [] (by simp) (by simp [complete_frameFn])
    exact ⟨t,ht,by simpa [traceEvidence] using he⟩
  | succ =>
    cases h
    obtain ⟨t,ht,he⟩ := complete_graft 1 x (x+1) [] (by simp) (by simp [complete_frameFn])
    exact ⟨t,ht,by simpa [traceEvidence] using he⟩
  | left =>
    cases h
    obtain ⟨t,ht,he⟩ := complete_graft 2 x x.unpair.1 [] (by simp) (by simp [complete_frameFn])
    exact ⟨t,ht,by simpa [traceEvidence] using he⟩
  | right =>
    cases h
    obtain ⟨t,ht,he⟩ := complete_graft 3 x x.unpair.2 [] (by simp) (by simp [complete_frameFn])
    exact ⟨t,ht,by simpa [traceEvidence] using he⟩
  | query =>
    cases h with
    | query _ _ hb =>
      have hb' : y ≤ 1 := by rcases hb with rfl | rfl <;> omega
      obtain ⟨t,ht,he⟩ := complete_graft 4 x y [] (by simp) (by simp [complete_frameFn,hb'])
      exact ⟨t,ht,by simpa [traceEvidence] using he⟩
  | pair c d ihc ihd =>
    cases h with
    | @pair _ _ x u v σ τ hc hd =>
      let ss : List CompleteSpec := [⟨encodeCode c,x,u,σ⟩,⟨encodeCode d,x,v,τ⟩]
      obtain ⟨t,ht,he⟩ := complete_graft (encodeCode (.pair c d)) x (Nat.pair u v) ss
        (by
          intro s hs
          simp only [ss,List.mem_cons,List.not_mem_nil,or_false] at hs
          rcases hs with rfl | rfl
          · exact ihc x u σ hc
          · exact ihd x v τ hd)
        (by rw [complete_frame_pair_iff]; simp [ss,complete_specAt])
      have hn : encodeCode (.pair c d) ≠ 4 := by rw [encodeCode]; omega
      exact ⟨t,ht,by simpa [hn,ss,complete_trace_append] using he⟩
  | comp c d ihc ihd =>
    cases h with
    | @comp _ _ x v y σ τ hd hc =>
      let ss : List CompleteSpec := [⟨encodeCode d,x,v,σ⟩,⟨encodeCode c,v,y,τ⟩]
      obtain ⟨t,ht,he⟩ := complete_graft (encodeCode (.comp c d)) x y ss
        (by
          intro s hs
          simp only [ss,List.mem_cons,List.not_mem_nil,or_false] at hs
          rcases hs with rfl | rfl
          · exact ihd x v σ hd
          · exact ihc v y τ hc)
        (by rw [complete_frame_comp_iff]; simp [ss,complete_specAt])
      have hn : encodeCode (.comp c d) ≠ 4 := by rw [encodeCode]; omega
      exact ⟨t,ht,by simpa [hn,ss,complete_trace_append] using he⟩
  | prec c d ihc ihd =>
    obtain ⟨⟨a,n⟩,rfl⟩ := Nat.pairEquiv.surjective x
    obtain ⟨values,records,h0,hs,hτ,hy⟩ := (OracleComputation.derives_prec_chain c d a n y τ).mp h
    let f : Fin (n+1) → CompleteSpec := Fin.cases
      ⟨encodeCode c,a,values 0,records 0⟩
      (fun i => ⟨encodeCode d,Nat.pair a (Nat.pair i.val (values i.castSucc)),values i.succ,records i.succ⟩)
    have hfo : ∀ i, (f i).output = values i := by
      intro i; refine Fin.cases rfl (fun _ => rfl) i
    have hft : ∀ i, (f i).trace = records i := by
      intro i; refine Fin.cases rfl (fun _ => rfl) i
    obtain ⟨t,ht,he⟩ := complete_graft (encodeCode (.prec c d)) (Nat.pair a n) y (List.ofFn f)
      (by
        intro s hs'
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs'
        refine Fin.cases ?_ (fun i => ?_) i
        · exact ihc a (values 0) (records 0) h0
        · exact ihd _ _ _ (hs i))
      (by
        rw [complete_frame_prec_iff]
        refine ⟨List.length_ofFn,?_,?_,?_,?_⟩
        · rw [complete_specAt_ofFn f 0 (by omega)]; rfl
        · rw [complete_specAt_ofFn f 0 (by omega)]; rfl
        · rw [complete_specAt_ofFn f n (by omega),hfo]; exact hy
        · intro j hj
          rw [complete_specAt_ofFn f (j+1) (by omega),complete_specAt_ofFn f j (by omega),hfo]
          exact ⟨rfl,rfl⟩)
    have hn : encodeCode (.prec c d) ≠ 4 := by rw [encodeCode]; omega
    exact ⟨t,ht,by simpa only [hn,↓reduceIte,Finset.empty_union,complete_specs_trace f records hft,← hτ] using he⟩
  | find' c ih =>
    obtain ⟨⟨a,m⟩,rfl⟩ := Nat.pairEquiv.surjective x
    obtain ⟨hmy,values,records,hs,hpos,hzero,hτ⟩ := (OracleComputation.derives_find_chain c a m y τ).mp h
    let f : Fin (y-m+1) → CompleteSpec := fun i =>
      ⟨encodeCode c,Nat.pair a (m+i.val),values i,records i⟩
    obtain ⟨t,ht,he⟩ := complete_graft (encodeCode (.find' c)) (Nat.pair a m) y (List.ofFn f)
      (by
        intro s hs'
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs'
        exact ih _ _ _ (hs i))
      (by
        rw [complete_frame_find_iff]
        refine ⟨hmy,List.length_ofFn,?_⟩
        intro j hj
        rw [List.length_ofFn] at hj
        rw [complete_specAt_ofFn f j hj]
        refine ⟨rfl,rfl,?_⟩
        split <;> rename_i hjlast
        · simp only [List.length_ofFn] at hjlast
          have hj' : (⟨j,hj⟩ : Fin (y-m+1)) = Fin.last (y-m) := Fin.ext (by simp only [Fin.val_last]; omega)
          simpa only [f,hj'] using hzero
        · simp only [List.length_ofFn] at hjlast
          have hj' : j < y-m := by omega
          exact hpos ⟨j,hj'⟩)
    have hn : encodeCode (.find' c) ≠ 4 := by rw [encodeCode]; omega
    exact ⟨t,ht,by simpa only [hn,↓reduceIte,Finset.empty_union,
      complete_specs_trace f records (fun _ => rfl),← hτ] using he⟩

theorem certificate_complete (c : OracleComputation.Code) (x y : ℕ)
    (τ : OracleComputation.QueryRecord) (h : OracleComputation.Derives c x τ y) :
    ∃ t, certificateCheck (encodeCode c) x y t = true ∧
      traceEvidence τ = finiteSet (evidenceCode t) := by
  exact complete_native c x y τ h

/-- On input z=(n,d), accept exactly finite bit-output certificates with that evidence code. -/
def transcriptOffer (e z t : ℕ) : Option ℕ :=
  if certificateCheck e (z.unpair.1 / 2) (1 - z.unpair.1 % 2) t &&
      decide (z.unpair.2 = evidenceCode t) then some 0 else none

def transcriptSearch (e z : ℕ) : Part ℕ := Nat.rfindOpt (transcriptOffer e z)

def TranscriptRules (e n d : ℕ) : Prop :=
  ∃ t, certificateCheck e (n/2) (1-n%2) t = true ∧ d = evidenceCode t

theorem transcript_offer_primitive :
    Primrec (fun p : (ℕ × ℕ) × ℕ => transcriptOffer p.1.1 p.1.2 p.2) := by
  have he : Primrec (fun p : (ℕ × ℕ) × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hz := Primrec.unpair.comp (Primrec.snd.comp (Primrec.fst (α := ℕ × ℕ) (β := ℕ)))
  have hn := Primrec.fst.comp hz
  have hd := Primrec.snd.comp hz
  have hc := certificateCheck_primitive.comp
    (((he.pair (Primrec.nat_div.comp hn (Primrec.const 2))).pair
      (Primrec.nat_sub.comp (Primrec.const 1) (Primrec.nat_mod.comp hn (Primrec.const 2)))).pair Primrec.snd)
  exact (Primrec.cond (Primrec.and.comp hc
    ((Primrec.eq.comp hd (evidenceCode_primitive.comp Primrec.snd)).decide))
    (Primrec.const (some 0)) (Primrec.const none)).of_eq (fun _ => by simp only [Bool.cond_eq_ite]; rfl)

theorem transcript_search_partial : Partrec₂ transcriptSearch := by
  exact Partrec.rfindOpt transcript_offer_primitive.to_comp.to₂

theorem transcript_has_program :
    ∃ v, ∀ e z, phi v (Nat.pair e z) = transcriptSearch e z := by
  obtain ⟨v,hv⟩ := phi_complete (Partrec₂.unpaired'.mpr transcript_search_partial)
  exact ⟨v,fun e z => by simpa only [Nat.unpaired, Nat.unpair_pair] using congrFun hv (Nat.pair e z)⟩

noncomputable def transcriptMaster : ℕ := Classical.choose transcript_has_program

noncomputable def transcriptIndex (e : ℕ) : ℕ := specialize transcriptMaster e

theorem transcriptMaster_eval (e z : ℕ) :
    phi transcriptMaster (Nat.pair e z) = transcriptSearch e z := by
  exact Classical.choose_spec transcript_has_program e z

theorem transcriptIndex_primitive : Primrec transcriptIndex := by
  exact specialize_primitive.comp (Primrec.const transcriptMaster) Primrec.id

theorem transcriptIndex_rules (e n d : ℕ) :
    indexedRule (transcriptIndex e) n d ↔ TranscriptRules e n d := by
  rw [indexedRule, transcriptIndex, specialize_eval, transcriptMaster_eval, transcriptSearch,
    Nat.rfindOpt_dom]
  simp only [TranscriptRules, transcriptOffer, Nat.unpair_pair]
  constructor
  · rintro ⟨t,a,ha⟩
    split_ifs at ha with h
    · exact ⟨t, (Bool.and_eq_true_iff.mp h).1, of_decide_eq_true (Bool.and_eq_true_iff.mp h).2⟩
    · simp at ha
  · rintro ⟨t,ht,hd⟩
    exact ⟨t,0,by simp [ht,hd]⟩

theorem transcript_operator_native (e : ℕ) (B : Set ℕ) (n : ℕ) :
    n ∈ operator (transcriptIndex e) B ↔
      ∃ τ, OracleComputation.Derives (decodeCode e) (n/2) τ (1-n%2) ∧
        (traceEvidence τ : Set ℕ) ⊆ B := by
  change (∃ d, indexedRule (transcriptIndex e) n d ∧ (finiteSet d : Set ℕ) ⊆ B) ↔ _
  simp only [transcriptIndex_rules, TranscriptRules]
  constructor
  · rintro ⟨d,⟨t,ht,rfl⟩,hB⟩
    obtain ⟨τ,hτ,he⟩ := certificate_sound e _ _ t ht
    exact ⟨τ,hτ,by simpa only [he] using hB⟩
  · rintro ⟨τ,hτ,hB⟩
    obtain ⟨t,ht,he⟩ := certificate_complete (decodeCode e) _ _ τ hτ
    rw [OracleProgramNumberings.encode_decode] at ht
    exact ⟨evidenceCode t,⟨t,ht,rfl⟩,by simpa only [← he] using hB⟩

theorem turing_to_enumeration (A B : Set ℕ) (c : OracleComputation.Code)
    (hc : TuringDegrees.Reduces c A B) :
    operator (transcriptIndex (encodeCode c)) (totalInfo B) = totalInfo A := by
  ext n
  rw [transcript_operator_native]
  have hn : tag (n/2) (1-n%2) = n := by dsimp [tag]; omega
  have hb : 1-n%2 ≤ 1 := Nat.sub_le _ _
  rw [← hn, tag_bits A _ _ hb]
  rw [hn]
  constructor
  · rintro ⟨τ,hτ,hB⟩
    have hv := OracleComputation.derives_valid hτ
    have hcon := (traceEvidence_consistent B τ hv).mp hB
    have hy := OracleComputation.trace_sound hτ hcon
    rw [OracleProgramNumberings.decode_encode, hc] at hy
    exact Part.mem_some_iff.mp hy
  · intro hbit
    have hy : 1-n%2 ∈ OracleComputation.eval B c (n/2) := by rw [hc]; exact Part.mem_some_iff.mpr hbit
    obtain ⟨τ,hτ,hcon⟩ := (OracleComputation.trace_complete B c _ _).mp hy
    exact ⟨τ,by simpa only [OracleProgramNumberings.decode_encode] using hτ,
      (traceEvidence_consistent B τ (OracleComputation.derives_valid hτ)).mpr hcon⟩

end Lemmatheca.ComputabilityTheory.EnumerationReducibility
