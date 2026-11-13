import Lemmatheca.HypersimplicityAndTruthTableCompleteness.ConsequenceCompiler
import Lemmatheca.DekkerDeficiencyAndHypersimpleSets.Basic
import Lemmatheca.TruthTableAndWeakTruthTableReductions.Closure

namespace Lemmatheca.ComputabilityTheory.HypersimplicityAndTruthTableCompleteness
open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.MathematicalLogic.PropositionalCompactness
open UniversalComputation EffectiveEnumerations StrongReductions HyperimmuneDegrees
open DekkerDeficiencyAndHypersimpleSets

def TruthTableComplete (A : Set ℕ) : Prop :=
  REPred A ∧ ∀ B : Set ℕ, REPred B → TruthTableReducible B A

theorem truth_table_complete_iff (A : Set ℕ) (hA : REPred A) :
    TruthTableComplete A ↔ TruthTableReducible haltingDiagonal A := by
  constructor
  · intro h
    exact h.2 haltingDiagonal haltingDiagonal_enumerable
  · intro hK
    refine ⟨hA,fun B hB => ?_⟩
    exact tt_transitive (manyOne_imp_tt (ProductiveAndCreativeSets.diagonal_complete hB)) hK

def formulaHistory (theta : ℕ → ℕ) (v : ℕ) : ℕ → ℕ :=
  Nat.rec 0 (fun _ prefixCodeInput => FiniteSequenceCoding.append prefixCodeInput
    (FiniteSequenceCoding.code [theta (consequenceCompiler v prefixCodeInput)]))

def rhoCode (theta : ℕ → ℕ) (v n : ℕ) : ℕ :=
  theta (consequenceCompiler v (formulaHistory theta v n))

def rhoFormula (theta : ℕ → ℕ) (v n : ℕ) : PropFormula ℕ :=
  readFormula (rhoCode theta v n)

theorem formula_history_spec (theta : ℕ → ℕ) (v n : ℕ) :
    FiniteSequenceCoding.decode (formulaHistory theta v n) = (List.range n).map (rhoCode theta v) := by
  induction n with
  | zero => simp [formulaHistory]
  | succ n ih =>
    change FiniteSequenceCoding.decode (FiniteSequenceCoding.append (formulaHistory theta v n)
      (FiniteSequenceCoding.code [rhoCode theta v n])) = _
    simp only [FiniteSequenceCoding.append,FiniteSequenceCoding.decode_code,ih,
      List.range_succ,List.map_append,List.map_singleton]

theorem formula_history_computable (theta : ℕ → ℕ) (htheta : Computable theta) (v : ℕ) :
    Computable (formulaHistory theta v) ∧ Computable (rhoCode theta v) := by
  have hprev : Computable (fun p : ℕ × (ℕ × ℕ) => p.2.2) :=
    Computable.snd.comp Computable.snd
  have he : Computable (fun p : ℕ × (ℕ × ℕ) =>
      theta (consequenceCompiler v p.2.2)) :=
    htheta.comp ((consequence_compiler_primitive v).to_comp.comp hprev)
  have hsuffix : Computable (fun p : ℕ × (ℕ × ℕ) =>
      FiniteSequenceCoding.code [theta (consequenceCompiler v p.2.2)]) :=
    (FiniteSequenceCoding.primrec_cons.to_comp.comp he (Computable.const 0)).of_eq
      (fun p => by simp [FiniteSequenceCoding.code,
        FiniteSequenceCoding.cons,Nat.add_comm])
  have hstep : Computable₂ (fun (_ : ℕ) (p : ℕ × ℕ) =>
      FiniteSequenceCoding.append p.2 (FiniteSequenceCoding.code [theta (consequenceCompiler v p.2)])) :=
    (FiniteSequenceCoding.primrec_append.to_comp.comp hprev hsuffix).to₂
  have hh : Computable (formulaHistory theta v) :=
    Computable.nat_rec Computable.id (Computable.const 0) hstep
  exact ⟨hh,htheta.comp ((consequence_compiler_primitive v).to_comp.comp hh)⟩

theorem true_not_forced (theta : ℕ → ℕ) (a v : ℕ)
    (hvalid : ∀ e, validCode (theta e) = true) (hv : ConsequenceRecognizerIndex theta a v)
    (hred : ∀ e, e ∉ haltingDiagonal ↔ Satisfies (setValuation (indexSet a)) (readFormula (theta e))) :
    ∀ n, validCode (rhoCode theta v n) = true ∧
      Satisfies (setValuation (indexSet a)) (rhoFormula theta v n) ∧
      ¬TheoryEntails (positiveTheory (indexSet a) ∪
        codeTheory (FiniteSequenceCoding.decode (formulaHistory theta v n))) (rhoFormula theta v n) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let premises := FiniteSequenceCoding.decode (formulaHistory theta v n)
    let e := consequenceCompiler v (formulaHistory theta v n)
    have hp : ∀ c ∈ premises, validCode c = true := by
      intro c hc
      change c ∈ FiniteSequenceCoding.decode (formulaHistory theta v n) at hc
      rw [formula_history_spec] at hc
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
      exact hvalid _
    have hdom : indexSet e = {j | positiveConsequence (indexSet a) premises (theta j)} := by
      simpa only [premises,FiniteSequenceCoding.code_decode,e] using
        consequence_compiler_domain theta hvalid a v hv premises hp
    have hmodel : ModelsTheory (setValuation (indexSet a))
        (positiveTheory (indexSet a) ∪ codeTheory premises) := by
      intro φ hφ
      rcases hφ with hpos | hcode
      · obtain ⟨i,hi,rfl⟩ := hpos
        simp [Satisfies,eval,setValuation,hi]
      · obtain ⟨c,hc,rfl⟩ := hcode
        change c ∈ FiniteSequenceCoding.decode (formulaHistory theta v n) at hc
        rw [formula_history_spec] at hc
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
        exact (ih j (List.mem_range.mp hj)).2.1
    have hsub : indexSet e ⊆ haltingDiagonalᶜ := by
      intro j hj
      rw [hdom] at hj
      exact (hred j).mpr (hj (setValuation (indexSet a)) hmodel)
    have escape := ProductiveAndCreativeSets.diagonal_complement_identity.2 e hsub
    refine ⟨hvalid _, (hred e).mp escape.1, ?_⟩
    intro hn
    apply escape.2
    rw [hdom]
    exact hn

def truthFunctionCount (n : ℕ) : ℕ := 2 ^ (2 ^ n)

def supportBound (theta : ℕ → ℕ) (v n : ℕ) : ℕ :=
  1 + (((List.range (truthFunctionCount n + 1)).flatMap
    (fun k => supportList (rhoCode theta v k))).foldl max n)

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

private theorem support_bound_spec (theta : ℕ → ℕ)
    (hvalid : ∀ e, validCode (theta e) = true) (v : ℕ) :
    ∀ n, n < supportBound theta v n ∧ ∀ k ≤ truthFunctionCount n,
      atoms (rhoFormula theta v k) ⊆ Finset.range (supportBound theta v n) := by
  intro n
  let xs := (List.range (truthFunctionCount n + 1)).flatMap
    (fun k => supportList (rhoCode theta v k))
  have hb := fold_max_bounds xs n
  refine ⟨by change n < 1 + xs.foldl max n; omega, ?_⟩
  intro k hk i hi
  have hs := (coded_formula_correct (rhoCode theta v k) (hvalid _) 0).1
  have him : i ∈ supportList (rhoCode theta v k) := by
    apply List.mem_toFinset.mp
    rw [hs]
    exact hi
  have hix : i ∈ xs := List.mem_flatMap.mpr
    ⟨k,List.mem_range.mpr (by omega),him⟩
  have hib := hb.2 i hix
  apply Finset.mem_range.mpr
  change i < 1 + xs.foldl max n
  omega

theorem support_bound (theta : ℕ → ℕ) (htheta : Computable theta)
    (hvalid : ∀ e, validCode (theta e) = true) (v : ℕ) :
    Computable (supportBound theta v) ∧
      ∀ n, n < supportBound theta v n ∧ ∀ k ≤ truthFunctionCount n,
        atoms (rhoFormula theta v k) ⊆ Finset.range (supportBound theta v n) := by
  have hpow : Primrec₂ (fun x y : ℕ => x ^ y) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hn : Computable (fun n => truthFunctionCount n + 1) :=
    Computable.succ.comp (hpow.to_comp.comp (Computable.const 2)
      (hpow.to_comp.comp (Computable.const 2) Computable.id))
  have hrho := (formula_history_computable theta htheta v).2
  have hp : Computable (fun n => (List.range (truthFunctionCount n + 1)).map (rhoCode theta v)) :=
    computable_list_map (Primrec.list_range.to_comp.comp hn) (hrho.comp Computable.snd).to₂
  have hf : Primrec (fun l : List ℕ => l.flatMap supportList) :=
    Primrec.list_flatMap Primrec.id ((syntax_algorithms.2.1.comp Primrec.snd).to₂)
  have hl : Computable (fun n => (List.range (truthFunctionCount n + 1)).flatMap
      (fun k => supportList (rhoCode theta v k))) :=
    (hf.to_comp.comp hp).of_eq (fun _ => by simp only [List.flatMap_map])
  have hm : Primrec (fun p : List ℕ × ℕ => p.1.foldl max p.2) :=
    Primrec.list_foldl Primrec.fst Primrec.snd
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  refine ⟨Primrec.nat_add.to_comp.comp (Computable.const 1)
    (hm.to_comp.comp (hl.pair Computable.id)), ?_⟩
  exact support_bound_spec theta hvalid v

theorem interval_hits_complement (theta : ℕ → ℕ) (a v : ℕ)
    (hvalid : ∀ e, validCode (theta e) = true) (hv : ConsequenceRecognizerIndex theta a v)
    (hred : ∀ e, e ∉ haltingDiagonal ↔ Satisfies (setValuation (indexSet a)) (readFormula (theta e))) :
    ∀ n, ∃ x, n ≤ x ∧ x < supportBound theta v n ∧ x ∉ indexSet a := by
  classical
  intro n
  by_contra hno
  push Not at hno
  let truth (k : ℕ) (word : Fin n → Bool) : Bool :=
    eval (fun x => if h : x < n then word ⟨x,h⟩ else true) (rhoFormula theta v k)
  have hbound := support_bound_spec theta hvalid v n
  have heval (k : ℕ) (hk : k ≤ truthFunctionCount n) (val : Valuation ℕ)
      (hval : ModelsTheory val (positiveTheory (indexSet a))) :
      eval val (rhoFormula theta v k) = truth k (fun i => val i.val) := by
    apply eval_congr
    intro x hx
    by_cases hxn : x < n
    · simp only [hxn, dite_true]
    · have hxupper := Finset.mem_range.mp (hbound.2 k hk hx)
      have hxa := hno x (by omega) hxupper
      have hvx := hval (.atom x) ⟨x,hxa,rfl⟩
      change val x = true at hvx
      simp only [hxn,dite_false,hvx]
  have separated (i j : ℕ) (hi : i ≤ truthFunctionCount n) (hj : j ≤ truthFunctionCount n)
      (hij : i < j) : truth i ≠ truth j := by
    intro heq
    apply (true_not_forced theta a v hvalid hv hred j).2.2
    intro val hval
    have hpos : ModelsTheory val (positiveTheory (indexSet a)) :=
      fun φ hφ => hval φ (Or.inl hφ)
    have hold : Satisfies val (rhoFormula theta v i) := by
      apply hval
      apply Or.inr
      refine ⟨rhoCode theta v i,?_,rfl⟩
      change rhoCode theta v i ∈ FiniteSequenceCoding.decode (formulaHistory theta v j)
      rw [formula_history_spec]
      exact List.mem_map.mpr ⟨i,List.mem_range.mpr hij,rfl⟩
    have he : eval val (rhoFormula theta v j) = eval val (rhoFormula theta v i) :=
      (heval j hj val hpos).trans ((congrFun heq (fun q : Fin n => val q.val)).symm.trans (heval i hi val hpos).symm)
    exact he.trans hold
  let f : Fin (truthFunctionCount n+1) → ((Fin n → Bool) → Bool) := fun i => truth i.val
  have hinj : Function.Injective f := by
    intro i j heq
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact separated i.val j.val (by omega) (by omega) hlt heq
    · exact separated j.val i.val (by omega) (by omega) hgt heq.symm
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin,Fintype.card_fun,Fintype.card_bool] at hc
  change truthFunctionCount n+1 ≤ truthFunctionCount n at hc
  omega

def hittingEndpoints (theta : ℕ → ℕ) (v : ℕ) : ℕ → ℕ :=
  Nat.rec 0 (fun _ b => supportBound theta v b)

def hittingArray (theta : ℕ → ℕ) (v k : ℕ) : ℕ :=
  FiniteSequenceCoding.code (List.range' (hittingEndpoints theta v k)
    (hittingEndpoints theta v (k + 1) - hittingEndpoints theta v k))

theorem hitting_array_correct (theta : ℕ → ℕ) (htheta : Computable theta) (a v : ℕ)
    (hvalid : ∀ e, validCode (theta e) = true) (hv : ConsequenceRecognizerIndex theta a v)
    (hred : ∀ e, e ∉ haltingDiagonal ↔ Satisfies (setValuation (indexSet a)) (readFormula (theta e))) :
    StrongArray (hittingArray theta v) ∧ ArrayHits (hittingArray theta v) (indexSet a)ᶜ ∧
      StrictMono (hittingEndpoints theta v) ∧ ∀ k x,
        x ∈ arraySet (hittingArray theta v) k ↔
          hittingEndpoints theta v k ≤ x ∧ x < hittingEndpoints theta v (k + 1) := by
  have hm := support_bound theta htheta hvalid v
  have hb : StrictMono (hittingEndpoints theta v) := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact (hm.2 (hittingEndpoints theta v k)).1
  have hs : Computable₂ (fun (_ : ℕ) (p : ℕ × ℕ) => supportBound theta v p.2) :=
    (hm.1.comp (Computable.snd.comp Computable.snd)).to₂
  have hc : Computable (hittingEndpoints theta v) :=
    Computable.nat_rec Computable.id (Computable.const 0) hs
  have hr : Primrec (fun p : ℕ × ℕ => List.range' p.1 p.2) := by
    simpa only [List.range'_eq_map_range] using
      (Primrec.list_map (Primrec.list_range.comp Primrec.snd)
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)
  have hlen : Computable (fun k => hittingEndpoints theta v (k+1) - hittingEndpoints theta v k) :=
    Primrec.nat_sub.to_comp.comp (hc.comp Computable.succ) hc
  have hd : Computable (hittingArray theta v) :=
    Primrec.encode.to_comp.comp (hr.to_comp.comp (hc.pair hlen))
  have hmem (k x : ℕ) : x ∈ arraySet (hittingArray theta v) k ↔
      hittingEndpoints theta v k ≤ x ∧ x < hittingEndpoints theta v (k+1) := by
    simp only [arraySet,hittingArray,FiniteSequenceCoding.decode_code,List.mem_toFinset,
      List.mem_range'_1,Nat.add_sub_of_le (hb.monotone (Nat.le_succ k))]
  refine ⟨⟨hd,?_⟩,?_,hb,hmem⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hi := (hmem i x).mp hxi
    have hj := (hmem j x).mp hxj
    rcases lt_or_gt_of_ne hij with hij | hji
    · have := hb.monotone (show i+1 ≤ j by omega)
      omega
    · have := hb.monotone (show j+1 ≤ i by omega)
      omega
  · intro k
    obtain ⟨x,hlo,hhi,hout⟩ := interval_hits_complement theta a v hvalid hv hred
      (hittingEndpoints theta v k)
    exact ⟨x,(hmem k x).mpr ⟨hlo,hhi⟩,hout⟩

theorem halting_tt_gives_array (A : Set ℕ) (hA : REPred A)
    (hK : TruthTableReducible haltingDiagonal A) :
    ∃ d, StrongArray d ∧ ArrayHits d Aᶜ := by
  obtain ⟨a,ha⟩ := (enumerable_iff_index A).mp hA
  have hset : indexSet a = A := Set.ext (fun x => (ha x).symm)
  obtain ⟨scheme,hs⟩ := hK
  obtain ⟨hc,hvalid,hred⟩ := nonhalting_formula scheme A hs
  obtain ⟨v,hv⟩ := consequence_recognizer_index (tableFormulaCode scheme) hc a
  have hr : ∀ e, e ∉ haltingDiagonal ↔
      Satisfies (setValuation (indexSet a)) (readFormula (tableFormulaCode scheme e)) := by
    simpa only [hset] using hred
  obtain ⟨hd,hh,_⟩ := hitting_array_correct (tableFormulaCode scheme) hc a v hvalid hv hr
  exact ⟨hittingArray (tableFormulaCode scheme) v,hd,by simpa only [hset] using hh⟩

theorem hypersimple_incomplete (A : Set ℕ) (hA : Hypersimple A) :
    TruthTableReducible A haltingDiagonal ∧ ¬TruthTableReducible haltingDiagonal A := by
  refine ⟨manyOne_imp_tt (ProductiveAndCreativeSets.diagonal_complete hA.1), ?_⟩
  intro hK
  exact ((hyperimmune_iff_no_array Aᶜ).mp hA.2).2 (halting_tt_gives_array A hA.1 hK)
end Lemmatheca.ComputabilityTheory.HypersimplicityAndTruthTableCompleteness
