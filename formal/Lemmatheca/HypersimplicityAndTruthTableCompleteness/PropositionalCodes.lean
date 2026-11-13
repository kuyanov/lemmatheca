import Lemmatheca.PropositionalNormalForms.PropositionalNormalForms
import Lemmatheca.PropositionalCompactness.PropositionalCompactness
import Lemmatheca.TruthTableAndWeakTruthTableReductions.Definitions

/-! Effective finite propositional codes, with bridges to the existing formula syntax.
The numerical algorithms are defined by finite histories; their correctness targets
identify supports and satisfaction in the original `PropFormula ℕ` semantics. -/
namespace Lemmatheca.ComputabilityTheory.HypersimplicityAndTruthTableCompleteness

open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.MathematicalLogic.PropositionalCompactness
open UniversalComputation StrongReductions

abbrev atomCode (i : ℕ) := 4 * i
abbrev falsumCode : ℕ := 1
abbrev negCode (c : ℕ) := 4 * c + 2
abbrev conjCode (c d : ℕ) := 4 * Nat.pair c d + 3
abbrev verumCode : ℕ := negCode falsumCode
abbrev disjCode (c d : ℕ) := negCode (conjCode (negCode c) (negCode d))
abbrev implCode (c d : ℕ) := negCode (conjCode c (negCode d))

def normalizeFormula : PropFormula ℕ → PropFormula ℕ
  | .atom i => .atom i
  | .falsum => .falsum
  | .neg φ => .neg (normalizeFormula φ)
  | .conj φ ψ => .conj (normalizeFormula φ) (normalizeFormula ψ)
  | .disj φ ψ => .neg (.conj (.neg (normalizeFormula φ)) (.neg (normalizeFormula ψ)))
  | .impl φ ψ => .neg (.conj (normalizeFormula φ) (.neg (normalizeFormula ψ)))

def formulaCode : PropFormula ℕ → ℕ
  | .atom i => atomCode i
  | .falsum => falsumCode
  | .neg φ => negCode (formulaCode φ)
  | .conj φ ψ => conjCode (formulaCode φ) (formulaCode ψ)
  | .disj φ ψ => disjCode (formulaCode φ) (formulaCode ψ)
  | .impl φ ψ => implCode (formulaCode φ) (formulaCode ψ)

/-- Total parsing, with falsity as the default at malformed constructor tags. -/
def readFormula (c : ℕ) : PropFormula ℕ :=
  if c % 4 = 0 then .atom (c / 4)
  else if c = 1 then .falsum
  else if c % 4 = 2 then .neg (readFormula (c / 4))
  else if c % 4 = 3 then
    .conj (readFormula (c / 4).unpair.1) (readFormula (c / 4).unpair.2)
  else .falsum
termination_by c
decreasing_by
  all_goals
    have hc : 0 < c := by omega
    have hq : c / 4 < c := Nat.div_lt_self hc (by decide)
    first
    | exact hq
    | exact lt_of_le_of_lt (Nat.unpair_left_le _) hq
    | exact lt_of_le_of_lt (Nat.unpair_right_le _) hq

/-- Validity, support list code, and truth bit are packed in one numerical state. -/
def packData (valid support truth : ℕ) : ℕ := Nat.pair valid (Nat.pair support truth)
abbrev dataValid (d : ℕ) := d.unpair.1
abbrev dataSupport (d : ℕ) := d.unpair.2.unpair.1
abbrev dataTruth (d : ℕ) := d.unpair.2.unpair.2

def dataStep (word c history : ℕ) : ℕ :=
  if c % 4 = 0 then packData 1 (FiniteSequenceCoding.code [c / 4]) (PostsTheorem.beta word (c / 4))
  else if c = 1 then packData 1 0 0
  else if c % 4 = 2 then
    let d := FiniteSequenceCoding.entry history (c / 4)
    packData (dataValid d) (dataSupport d) (1 - dataTruth d)
  else if c % 4 = 3 then
    let d := FiniteSequenceCoding.entry history (c / 4).unpair.1
    let e := FiniteSequenceCoding.entry history (c / 4).unpair.2
    packData (dataValid d * dataValid e)
      (FiniteSequenceCoding.append (dataSupport d) (dataSupport e)) (dataTruth d * dataTruth e)
  else packData 0 0 0

def syntaxData (word c : ℕ) : ℕ :=
  FiniteSequenceCoding.historyValue (dataStep word) c

def validCode (c : ℕ) : Bool := dataValid (syntaxData 0 c) == 1
def supportList (c : ℕ) : List ℕ := FiniteSequenceCoding.decode (dataSupport (syntaxData 0 c))
def valueCode (word c : ℕ) : ℕ := dataTruth (syntaxData word c)
def wordValuation (word : ℕ) : Valuation ℕ := fun i => PostsTheorem.beta word i == 1

noncomputable def setValuation (A : Set ℕ) : Valuation ℕ := by
  classical
  exact fun i => decide (i ∈ A)

theorem read_atom (i : ℕ) : readFormula (atomCode i) = .atom i := by
  have hm : atomCode i % 4 = 0 := by dsimp only [atomCode, negCode, conjCode]; omega
  have hd : atomCode i / 4 = i := by dsimp only [atomCode, negCode, conjCode]; omega
  rw [readFormula]
  simp only [hm, ↓reduceIte, hd]

theorem read_falsum : readFormula falsumCode = .falsum := by
  rw [readFormula]
  simp only [falsumCode, Nat.reduceMod, Nat.one_ne_zero, ↓reduceIte]

theorem read_neg (c : ℕ) : readFormula (negCode c) = .neg (readFormula c) := by
  have hm : negCode c % 4 = 2 := by dsimp only [atomCode, negCode, conjCode]; omega
  have hd : negCode c / 4 = c := by dsimp only [atomCode, negCode, conjCode]; omega
  have hn : negCode c ≠ 1 := by dsimp only [atomCode, negCode, conjCode]; omega
  rw [readFormula]
  simp only [hm, hd, hn, Nat.reduceEqDiff, ↓reduceIte]

theorem read_conj (c d : ℕ) :
    readFormula (conjCode c d) = .conj (readFormula c) (readFormula d) := by
  have hm : conjCode c d % 4 = 3 := by dsimp only [atomCode, negCode, conjCode]; omega
  have hd : conjCode c d / 4 = Nat.pair c d := by dsimp only [atomCode, negCode, conjCode]; omega
  have hn : conjCode c d ≠ 1 := by dsimp only [atomCode, negCode, conjCode]; omega
  rw [readFormula]
  simp only [hm, hd, hn, Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair]

private theorem data_history_entry (word n k : ℕ) (hk : k < n) :
    FiniteSequenceCoding.entry (FiniteSequenceCoding.historyCode (dataStep word) n) k =
      syntaxData word k := by
  simp only [FiniteSequenceCoding.entry, FiniteSequenceCoding.history_identity,
    List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]
  rfl

private theorem data_atom (word i : ℕ) :
    syntaxData word (atomCode i) =
      packData 1 (FiniteSequenceCoding.code [i]) (PostsTheorem.beta word i) := by
  have hm : atomCode i % 4 = 0 := by dsimp only [atomCode, negCode, conjCode]; omega
  have hd : atomCode i / 4 = i := by dsimp only [atomCode, negCode, conjCode]; omega
  change dataStep word (atomCode i) (FiniteSequenceCoding.historyCode (dataStep word) (atomCode i)) = _
  simp only [dataStep, hm, ↓reduceIte, hd]

private theorem data_falsum (word : ℕ) : syntaxData word falsumCode = packData 1 0 0 := by
  change dataStep word falsumCode (FiniteSequenceCoding.historyCode (dataStep word) falsumCode) = _
  simp only [dataStep, falsumCode, Nat.reduceMod, Nat.one_ne_zero, ↓reduceIte]

private theorem data_neg (word c : ℕ) :
    syntaxData word (negCode c) = packData (dataValid (syntaxData word c))
      (dataSupport (syntaxData word c)) (1 - dataTruth (syntaxData word c)) := by
  have hm : negCode c % 4 = 2 := by dsimp only [atomCode, negCode, conjCode]; omega
  have hd : negCode c / 4 = c := by dsimp only [atomCode, negCode, conjCode]; omega
  have hn : negCode c ≠ 1 := by dsimp only [atomCode, negCode, conjCode]; omega
  have hc : c < negCode c := by dsimp only [atomCode, negCode, conjCode]; omega
  change dataStep word (negCode c) (FiniteSequenceCoding.historyCode (dataStep word) (negCode c)) = _
  simp only [dataStep, hm, hd, hn, Nat.reduceEqDiff, ↓reduceIte, data_history_entry _ _ _ hc]

private theorem data_conj (word c d : ℕ) :
    syntaxData word (conjCode c d) =
      packData (dataValid (syntaxData word c) * dataValid (syntaxData word d))
        (FiniteSequenceCoding.append (dataSupport (syntaxData word c))
          (dataSupport (syntaxData word d)))
        (dataTruth (syntaxData word c) * dataTruth (syntaxData word d)) := by
  have hm : conjCode c d % 4 = 3 := by dsimp only [atomCode, negCode, conjCode]; omega
  have hd : conjCode c d / 4 = Nat.pair c d := by dsimp only [atomCode, negCode, conjCode]; omega
  have hn : conjCode c d ≠ 1 := by dsimp only [atomCode, negCode, conjCode]; omega
  have hc : c < conjCode c d := by
    have := Nat.left_le_pair c d
    dsimp only [conjCode]
    omega
  have hd' : d < conjCode c d := by
    have := Nat.right_le_pair c d
    dsimp only [conjCode]
    omega
  change dataStep word (conjCode c d) (FiniteSequenceCoding.historyCode (dataStep word) (conjCode c d)) = _
  simp only [dataStep, hm, hd, hn, Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair,
    data_history_entry _ _ _ hc, data_history_entry _ _ _ hd']

theorem valid_atom (i : ℕ) : validCode (atomCode i) = true := by
  simp only [validCode, data_atom, dataValid, packData, Nat.unpair_pair, BEq.rfl]

theorem valid_falsum : validCode falsumCode = true := by
  simp only [validCode, data_falsum, dataValid, packData, Nat.unpair_pair, BEq.rfl]

theorem valid_neg (c : ℕ) (hc : validCode c = true) : validCode (negCode c) = true := by
  unfold validCode at hc ⊢
  rw [data_neg]
  simpa only [dataValid, packData, Nat.unpair_pair] using hc

theorem valid_conj (c d : ℕ) (hc : validCode c = true) (hd : validCode d = true) :
    validCode (conjCode c d) = true := by
  unfold validCode at hc hd ⊢
  rw [data_conj]
  simp only [dataValid, packData, Nat.unpair_pair, beq_iff_eq] at hc hd ⊢
  rw [hc, hd]

private theorem normalization_eval (φ : PropFormula ℕ) (v : Valuation ℕ) :
    eval v (normalizeFormula φ) = eval v φ := by
  induction φ with
  | atom i => rfl
  | falsum => rfl
  | neg φ ih => simp only [normalizeFormula, eval, ih]
  | conj φ ψ ihφ ihψ => simp only [normalizeFormula, eval, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [normalizeFormula, eval, ihφ, ihψ, Bool.not_and]
  | impl φ ψ ihφ ihψ => simp [normalizeFormula, eval, ihφ, ihψ, Bool.not_and]

private theorem normalization_atoms (φ : PropFormula ℕ) :
    atoms (normalizeFormula φ) = atoms φ := by
  induction φ <;> simp_all [normalizeFormula, atoms]

private theorem read_encode (φ : PropFormula ℕ) :
    readFormula (formulaCode φ) = normalizeFormula φ := by
  induction φ with
  | atom i => exact read_atom i
  | falsum => exact read_falsum
  | neg φ ih => simp only [formulaCode, read_neg, ih, normalizeFormula]
  | conj φ ψ ihφ ihψ => simp only [formulaCode, read_conj, ihφ, ihψ, normalizeFormula]
  | disj φ ψ ihφ ihψ =>
    simp only [formulaCode, disjCode, read_neg, read_conj, ihφ, ihψ, normalizeFormula]
  | impl φ ψ ihφ ihψ =>
    simp only [formulaCode, implCode, read_neg, read_conj, ihφ, ihψ, normalizeFormula]

private theorem encode_valid (φ : PropFormula ℕ) : validCode (formulaCode φ) = true := by
  induction φ with
  | atom i => exact valid_atom i
  | falsum => exact valid_falsum
  | neg φ ih => exact valid_neg _ ih
  | conj φ ψ ihφ ihψ => exact valid_conj _ _ ihφ ihψ
  | disj φ ψ ihφ ihψ =>
    exact valid_neg _ (valid_conj _ _ (valid_neg _ ihφ) (valid_neg _ ihψ))
  | impl φ ψ ihφ ihψ => exact valid_neg _ (valid_conj _ _ ihφ (valid_neg _ ihψ))

theorem code_semantics (φ : PropFormula ℕ) :
    validCode (formulaCode φ) = true ∧
      readFormula (formulaCode φ) = normalizeFormula φ ∧
      (∀ v, eval v (normalizeFormula φ) = eval v φ) ∧
      atoms (normalizeFormula φ) = atoms φ := by
  exact ⟨encode_valid φ, read_encode φ, normalization_eval φ, normalization_atoms φ⟩

private theorem packData_primitive {α : Type*} [Primcodable α]
    {f g h : α → ℕ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun x => packData (f x) (g x) (h x)) :=
  Primrec₂.natPair.comp hf (Primrec₂.natPair.comp hg hh)

private theorem dataValid_primitive {α : Type*} [Primcodable α]
    {f : α → ℕ} (hf : Primrec f) : Primrec (fun x => dataValid (f x)) :=
  (Primrec.fst.comp Primrec.unpair).comp hf

private theorem dataSupport_primitive {α : Type*} [Primcodable α]
    {f : α → ℕ} (hf : Primrec f) : Primrec (fun x => dataSupport (f x)) :=
  (Primrec.fst.comp Primrec.unpair).comp ((Primrec.snd.comp Primrec.unpair).comp hf)

private theorem dataTruth_primitive {α : Type*} [Primcodable α]
    {f : α → ℕ} (hf : Primrec f) : Primrec (fun x => dataTruth (f x)) :=
  (Primrec.snd.comp Primrec.unpair).comp ((Primrec.snd.comp Primrec.unpair).comp hf)

private theorem dataStep_primitive :
    Primrec (fun p : ℕ × ℕ × ℕ => dataStep p.1 p.2.1 p.2.2) := by
  have hw : Primrec (fun p : ℕ × ℕ × ℕ => p.1) := Primrec.fst
  have hc : Primrec (fun p : ℕ × ℕ × ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hh : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  have hq := Primrec.nat_div.comp hc (Primrec.const 4)
  have hm := Primrec.nat_mod.comp hc (Primrec.const 4)
  have hzero := Primrec.eq.comp hm (Primrec.const 0)
  have hone := Primrec.eq.comp hc (Primrec.const 1)
  have htwo := Primrec.eq.comp hm (Primrec.const 2)
  have hthree := Primrec.eq.comp hm (Primrec.const 3)
  have hsingle := Primrec.encode.comp (Primrec.list_cons.comp hq (Primrec.const ([] : List ℕ)))
  have hatom := packData_primitive (Primrec.const 1) hsingle (PostsTheorem.beta_primitive.comp hw hq)
  have hnegchild := FiniteSequenceCoding.primrec_entry.comp hh hq
  have hneg := packData_primitive (dataValid_primitive hnegchild) (dataSupport_primitive hnegchild)
    (Primrec.nat_sub.comp (Primrec.const 1) (dataTruth_primitive hnegchild))
  have hleft := FiniteSequenceCoding.primrec_entry.comp hh ((Primrec.fst.comp Primrec.unpair).comp hq)
  have hright := FiniteSequenceCoding.primrec_entry.comp hh ((Primrec.snd.comp Primrec.unpair).comp hq)
  have hconj := packData_primitive
    (Primrec.nat_mul.comp (dataValid_primitive hleft) (dataValid_primitive hright))
    (FiniteSequenceCoding.primrec_append.comp (dataSupport_primitive hleft) (dataSupport_primitive hright))
    (Primrec.nat_mul.comp (dataTruth_primitive hleft) (dataTruth_primitive hright))
  exact (Primrec.ite hzero hatom (Primrec.ite hone (Primrec.const (packData 1 0 0))
    (Primrec.ite htwo hneg (Primrec.ite hthree hconj (Primrec.const (packData 0 0 0)))))).of_eq
      (fun _ => rfl)

theorem syntax_algorithms :
    Primrec validCode ∧ Primrec supportList ∧
      Primrec (fun p : ℕ × ℕ => valueCode p.1 p.2) := by
  have hdata : Primrec₂ syntaxData := FiniteSequenceCoding.primrec_historyValue_param dataStep_primitive
  have hzero := hdata.comp (Primrec.const 0) Primrec.id
  exact ⟨Primrec.beq.comp (dataValid_primitive hzero) (Primrec.const 1),
    (Primrec.ofNat (List ℕ)).comp (dataSupport_primitive hzero), dataTruth_primitive hdata⟩

private theorem support_neg (c : ℕ) : supportList (negCode c) = supportList c := by
  unfold supportList
  rw [data_neg]
  simp only [dataSupport, packData, Nat.unpair_pair]

private theorem support_conj (c d : ℕ) : supportList (conjCode c d) = supportList c ++ supportList d := by
  unfold supportList
  rw [data_conj]
  simp only [dataSupport, packData, Nat.unpair_pair, FiniteSequenceCoding.append,
    FiniteSequenceCoding.decode_code]

private theorem value_neg (word c : ℕ) : valueCode word (negCode c) = 1 - valueCode word c := by
  unfold valueCode
  rw [data_neg]
  simp only [dataTruth, packData, Nat.unpair_pair]

private theorem value_conj (word c d : ℕ) :
    valueCode word (conjCode c d) = valueCode word c * valueCode word d := by
  unfold valueCode
  rw [data_conj]
  simp only [dataTruth, packData, Nat.unpair_pair]

private theorem valid_neg_iff (c : ℕ) : validCode (negCode c) = true ↔ validCode c = true := by
  unfold validCode
  rw [data_neg]
  simp only [dataValid, packData, Nat.unpair_pair]

private theorem valid_conj_iff (c d : ℕ) :
    validCode (conjCode c d) = true ↔ validCode c = true ∧ validCode d = true := by
  unfold validCode
  rw [data_conj]
  simp only [dataValid, packData, Nat.unpair_pair, beq_iff_eq, mul_eq_one]

private theorem code_cases (c : ℕ) :
    (∃ i, c = atomCode i) ∨ c = falsumCode ∨
      (∃ d, c = negCode d ∧ d < c) ∨
      (∃ d e, c = conjCode d e ∧ d < c ∧ e < c) ∨ validCode c = false := by
  by_cases hzero : c % 4 = 0
  · exact Or.inl ⟨c / 4, by dsimp only [atomCode]; omega⟩
  by_cases hone : c = 1
  · exact Or.inr (Or.inl hone)
  by_cases htwo : c % 4 = 2
  · exact Or.inr (Or.inr (Or.inl ⟨c / 4,
      by dsimp only [negCode]; omega,
      Nat.div_lt_self (by omega) (by decide)⟩))
  by_cases hthree : c % 4 = 3
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨(c / 4).unpair.1, (c / 4).unpair.2, ?_, ?_, ?_⟩)))
    · dsimp only [conjCode]
      rw [Nat.pair_unpair]
      omega
    · exact lt_of_le_of_lt (Nat.unpair_left_le _) (Nat.div_lt_self (by omega) (by decide))
    · exact lt_of_le_of_lt (Nat.unpair_right_le _) (Nat.div_lt_self (by omega) (by decide))
  · right; right; right; right
    have hd : syntaxData 0 c = packData 0 0 0 := by
      change dataStep 0 c (FiniteSequenceCoding.historyCode (dataStep 0) c) = _
      simp only [dataStep, hzero, hone, htwo, hthree, ↓reduceIte]
    simp only [validCode, hd, dataValid, packData, Nat.unpair_pair, Nat.reduceBEq]

private theorem indicator_neg (b : Bool) :
    1 - (if b then 1 else 0) = (if !b then 1 else 0) := by
  cases b <;> rfl

private theorem indicator_conj (b c : Bool) :
    (if b then 1 else 0) * (if c then 1 else 0) = (if b && c then 1 else 0) := by
  cases b <;> cases c <;> rfl

private theorem indicator_properties (b : Bool) :
    ((if b then 1 else 0) = (0 : ℕ) ∨ (if b then 1 else 0) = 1) ∧
      ((if b then 1 else 0) = (1 : ℕ) ↔ b = true) := by
  cases b <;> decide

private theorem coded_indicator (c : ℕ) (hc : validCode c = true) (word : ℕ) :
    (supportList c).toFinset = atoms (readFormula c) ∧
      valueCode word c = if eval (wordValuation word) (readFormula c) then 1 else 0 := by
  induction c using Nat.strong_induction_on generalizing word with
  | h c ih =>
    rcases code_cases c with ⟨i, rfl⟩ | rfl | ⟨d, rfl, hd⟩ | ⟨d, e, rfl, hd, he⟩ | hbad
    · rcases PostsTheorem.beta_bits word i with hbit | hbit <;>
        simp only [supportList, data_atom, dataSupport, dataTruth, packData, Nat.unpair_pair,
          FiniteSequenceCoding.decode_code, List.toFinset_cons, List.toFinset_nil, Finset.insert_empty,
          read_atom, atoms, eval, wordValuation, valueCode, hbit, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, and_self]
    · simp only [supportList, data_falsum, dataSupport, dataTruth, packData, Nat.unpair_pair,
        FiniteSequenceCoding.decode_zero, List.toFinset_nil, read_falsum, atoms, eval, valueCode,
        Bool.false_eq_true, ↓reduceIte, and_self]
    · obtain ⟨hs, hv⟩ := ih d hd ((valid_neg_iff d).mp hc) word
      refine ⟨by simpa only [support_neg, read_neg, atoms] using hs, ?_⟩
      rw [value_neg, hv, read_neg]
      simp only [eval]
      exact indicator_neg _
    · obtain ⟨hvd, hve⟩ := (valid_conj_iff d e).mp hc
      obtain ⟨hsd, htd⟩ := ih d hd hvd word
      obtain ⟨hse, hte⟩ := ih e he hve word
      refine ⟨by simp only [support_conj, List.toFinset_append, read_conj, atoms, hsd, hse], ?_⟩
      rw [value_conj, htd, hte, read_conj]
      simp only [eval]
      exact indicator_conj _ _
    · rw [hbad] at hc
      contradiction

theorem coded_formula_correct (c : ℕ) (hc : validCode c = true) (word : ℕ) :
    (supportList c).toFinset = atoms (readFormula c) ∧
      (valueCode word c = 0 ∨ valueCode word c = 1) ∧
      (valueCode word c = 1 ↔ Satisfies (wordValuation word) (readFormula c)) := by
  obtain ⟨hs, hv⟩ := coded_indicator c hc word
  have hprops := indicator_properties (eval (wordValuation word) (readFormula c))
  refine ⟨hs, ?_, ?_⟩
  · rw [hv]
    exact hprops.1
  · rw [hv]
    exact hprops.2

def finiteAtomBound (facts premises : List ℕ) (conclusion : ℕ) : ℕ :=
  (facts.map Nat.succ ++
    (premises.flatMap supportList ++ supportList conclusion).map Nat.succ).foldl max 0

/-- The concrete finite Boolean test, including a validity check for every supplied formula. -/
def finiteConsequenceTest (facts premises : List ℕ) (conclusion : ℕ) : Bool :=
  premises.all validCode && validCode conclusion &&
    (binaryRows (finiteAtomBound facts premises conclusion)).all (fun row =>
      let word := FiniteSequenceCoding.code row
      !(facts.all (fun i => PostsTheorem.beta word i == 1) &&
        premises.all (fun c => valueCode word c == 1)) || valueCode word conclusion == 1)

private theorem list_all_primitive {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {g : α → β → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).all (g a)) := by
  have hfold := Primrec.list_foldr hf (Primrec.const true)
    (Primrec.and.comp
      (hg.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  apply hfold.of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b l ih => simp only [List.foldr_cons, List.all_cons, ih]

private theorem positive_word_primitive :
    Primrec (fun p : List ℕ × ℕ => p.1.all (fun i => PostsTheorem.beta p.2 i == 1)) := by
  exact list_all_primitive Primrec.fst
    (Primrec.beq.comp (PostsTheorem.beta_primitive.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd) (Primrec.const 1)).to₂

private theorem formula_word_primitive :
    Primrec (fun p : List ℕ × ℕ => p.1.all (fun c => valueCode p.2 c == 1)) := by
  exact list_all_primitive Primrec.fst
    (Primrec.beq.comp (syntax_algorithms.2.2.comp
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)) (Primrec.const 1)).to₂

private theorem finite_atom_bound_primitive :
    Primrec (fun p : (List ℕ × List ℕ) × ℕ => finiteAtomBound p.1.1 p.1.2 p.2) := by
  have hf : Primrec (fun p : (List ℕ × List ℕ) × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hp : Primrec (fun p : (List ℕ × List ℕ) × ℕ => p.1.2) := Primrec.snd.comp Primrec.fst
  have hc : Primrec (fun p : (List ℕ × List ℕ) × ℕ => p.2) := Primrec.snd
  have hfs := Primrec.list_map hf (Primrec.succ.comp Primrec.snd).to₂
  have hps := Primrec.list_flatMap hp (syntax_algorithms.2.1.comp Primrec.snd).to₂
  have hcs := syntax_algorithms.2.1.comp hc
  have hs := Primrec.list_map (Primrec.list_append.comp hps hcs) (Primrec.succ.comp Primrec.snd).to₂
  exact Primrec.list_foldl (Primrec.list_append.comp hfs hs) (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem finite_consequence_primitive :
    Primrec (fun p : (List ℕ × List ℕ) × ℕ => finiteConsequenceTest p.1.1 p.1.2 p.2) := by
  let α := (List ℕ × List ℕ) × ℕ
  have hf : Primrec (fun p : α => p.1.1) := Primrec.fst.comp Primrec.fst
  have hp : Primrec (fun p : α => p.1.2) := Primrec.snd.comp Primrec.fst
  have hc : Primrec (fun p : α => p.2) := Primrec.snd
  have hvalidp := list_all_primitive hp (syntax_algorithms.1.comp Primrec.snd).to₂
  have hvalidc := syntax_algorithms.1.comp hc
  have hrows := binaryRows_primrec.comp finite_atom_bound_primitive
  have hw : Primrec (fun p : α × List ℕ => FiniteSequenceCoding.code p.2) :=
    Primrec.encode.comp Primrec.snd
  have hpositive := positive_word_primitive.comp ((hf.comp Primrec.fst).pair hw)
  have hpremises := formula_word_primitive.comp ((hp.comp Primrec.fst).pair hw)
  have hconclusion := Primrec.beq.comp
    (syntax_algorithms.2.2.comp (hw.pair (hc.comp Primrec.fst))) (Primrec.const 1)
  have hrow := Primrec.or.comp (Primrec.not.comp (Primrec.and.comp hpositive hpremises)) hconclusion
  exact Primrec.and.comp (Primrec.and.comp hvalidp hvalidc)
    (list_all_primitive hrows hrow.to₂)

private theorem fold_max_le (xs : List ℕ) (a b : ℕ) :
    xs.foldl max a ≤ b ↔ a ≤ b ∧ ∀ x ∈ xs, x ≤ b := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, and_assoc]

private theorem finite_atom_bound_spec (facts premises : List ℕ) (conclusion : ℕ) :
    (∀ i ∈ facts, i < finiteAtomBound facts premises conclusion) ∧
      (∀ c ∈ premises, ∀ i ∈ supportList c, i < finiteAtomBound facts premises conclusion) ∧
      ∀ i ∈ supportList conclusion, i < finiteAtomBound facts premises conclusion := by
  let all := facts.map Nat.succ ++
    (premises.flatMap supportList ++ supportList conclusion).map Nat.succ
  have hb : ∀ j ∈ all, j ≤ finiteAtomBound facts premises conclusion :=
    ((fold_max_le all 0 _).mp le_rfl).2
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    apply Nat.lt_of_succ_le
    apply hb
    exact List.mem_append_left _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · intro c hc i hi
    apply Nat.lt_of_succ_le
    apply hb
    exact List.mem_append_right _ (List.mem_map.mpr ⟨i,
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, hc, hi⟩), rfl⟩)
  · intro i hi
    apply Nat.lt_of_succ_le
    apply hb
    exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_append_right _ hi, rfl⟩)

private theorem valuation_row (v : Valuation ℕ) (n : ℕ) :
    ∃ row ∈ binaryRows n, ∀ i < n,
      wordValuation (FiniteSequenceCoding.code row) i = v i := by
  classical
  let A : Set ℕ := {i | v i = true}
  let word := PostsTheorem.prefixCode A n
  refine ⟨FiniteSequenceCoding.decode word, ?_, ?_⟩
  · apply (binaryRows_spec n).1 _ |>.mpr
    exact ⟨ComputableTreesAndPaths.prefix_code_valid A n, (PostsTheorem.prefixCode_spec A n).1⟩
  · intro i hi
    rw [FiniteSequenceCoding.code_decode]
    apply Bool.eq_iff_iff.mpr
    simp only [wordValuation, beq_iff_eq]
    rw [(PostsTheorem.prefixCode_spec A n).2 i hi]
    simp only [indicator, A, Set.mem_ofPred_eq, ite_eq_left_iff, Nat.zero_ne_one, imp_false, not_not]

private theorem coded_eval_agree (c : ℕ) (hc : validCode c = true) (word : ℕ)
    (v : Valuation ℕ) (n : ℕ) (hbound : ∀ i ∈ supportList c, i < n)
    (hagree : ∀ i < n, wordValuation word i = v i) :
    eval (wordValuation word) (readFormula c) = eval v (readFormula c) := by
  apply eval_congr
  intro i hi
  apply hagree
  apply hbound
  apply List.mem_toFinset.mp
  rw [(coded_formula_correct c hc word).1]
  exact hi

private theorem bool_imp_true (a b : Bool) : (!a || b) = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem finite_consequence_correct (facts premises : List ℕ) (conclusion : ℕ)
    (hp : ∀ c ∈ premises, validCode c = true) (hc : validCode conclusion = true) :
    finiteConsequenceTest facts premises conclusion = true ↔
      ∀ v : Valuation ℕ, (∀ i ∈ facts, v i = true) →
        (∀ c ∈ premises, Satisfies v (readFormula c)) → Satisfies v (readFormula conclusion) := by
  have hvalid : premises.all validCode = true := List.all_eq_true.mpr hp
  have htest : finiteConsequenceTest facts premises conclusion = true ↔
      ∀ row ∈ binaryRows (finiteAtomBound facts premises conclusion),
        ((∀ i ∈ facts, PostsTheorem.beta (FiniteSequenceCoding.code row) i = 1) ∧
          ∀ c ∈ premises, valueCode (FiniteSequenceCoding.code row) c = 1) →
            valueCode (FiniteSequenceCoding.code row) conclusion = 1 := by
    simp only [finiteConsequenceTest, hvalid, hc, Bool.true_and, List.all_eq_true,
      bool_imp_true, Bool.and_eq_true, beq_iff_eq]
  rw [htest]
  constructor
  · intro h v hfact hprem
    obtain ⟨row, hrow, hagree⟩ := valuation_row v (finiteAtomBound facts premises conclusion)
    obtain ⟨hbf, hbp, hbc⟩ := finite_atom_bound_spec facts premises conclusion
    have hrowfacts : ∀ i ∈ facts, PostsTheorem.beta (FiniteSequenceCoding.code row) i = 1 := by
      intro i hi
      have hh : wordValuation (FiniteSequenceCoding.code row) i = true :=
        (hagree i (hbf i hi)).trans (hfact i hi)
      exact beq_iff_eq.mp hh
    have hrowprem : ∀ c ∈ premises, valueCode (FiniteSequenceCoding.code row) c = 1 := by
      intro c hcmem
      apply (coded_formula_correct c (hp c hcmem) _).2.2.mpr
      unfold Satisfies
      rw [coded_eval_agree c (hp c hcmem) _ v _ (hbp c hcmem) hagree]
      exact hprem c hcmem
    have hh := (coded_formula_correct conclusion hc _).2.2.mp (h row hrow ⟨hrowfacts, hrowprem⟩)
    unfold Satisfies at hh ⊢
    rw [coded_eval_agree conclusion hc _ v _ hbc hagree] at hh
    exact hh
  · intro h row _ hrow
    apply (coded_formula_correct conclusion hc _).2.2.mpr
    apply h (wordValuation (FiniteSequenceCoding.code row))
    · intro i hi
      exact beq_iff_eq.mpr (hrow.1 i hi)
    · intro c hcmem
      exact (coded_formula_correct c (hp c hcmem) _).2.2.mp (hrow.2 c hcmem)

end Lemmatheca.ComputabilityTheory.HypersimplicityAndTruthTableCompleteness
