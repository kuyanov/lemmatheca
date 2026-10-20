import Lemmatheca.MathematicalLogic.CodingFormalProofsEffective
import Lemmatheca.MathematicalLogic.CodingFormalProofsRelabel

/-! Explicit finite certificates for the actual Robinson axioms and PA's
induction schema. Bound-variable order is the canonical order used by
`ArithmeticTheories.close`, not a choice of a finite equivalence. -/
namespace Lemmatheca.MathematicalLogic.ArithmeticProofPredicates
open FirstOrder FirstOrder.Language
open ArithmeticTheories CodingFormalProofs
noncomputable section

/-- Rename auxiliary names to bound slots. In single-variable mode only name
`k` is bound; in simultaneous mode all parameter names become their numbered
slots. Old bound slots shift to make room for the newly introduced slots. -/
def bindStep (single : Bool) (k e hist : ℕ) : ℕ :=
  if e = 0 then 0 else
  if tag e = 8 then
    if single then (if arg e 0 = k then boundName 0 else e)
    else boundName (arg e 0)
  else if tag e = 1 then boundName (arg e 0 + if single then 1 else k)
  else node (tag e)
    (if tag e = 2 ∨ tag e = 5 then
      arg e 0 :: (args e).tail.map (Seq.entry hist)
     else (args e).map (Seq.entry hist))

def bindCode (single : Bool) (k e : ℕ) : ℕ := earlierFold (bindStep single k) e

def closeCode (k e : ℕ) : ℕ := (allCode^[k]) (bindCode false k e)

def allAuxCode (k e : ℕ) : ℕ := allCode (bindCode true k e)

def arithmeticZeroCode : ℕ := termCode arithmeticSignature auxName
  (zeroTerm : language.Term ℕ)

def arithmeticSuccCode (t : ℕ) : ℕ := node 2 [arithFunctionCode .succ, t]

/-- The matrix code has parameter names `0, …, k-1` and induction name `k`. -/
def inductionCode (k e : ℕ) : ℕ :=
  closeCode k (impCode
    (andCode (rewrite 1 k arithmeticZeroCode e)
      (allAuxCode k (impCode e (rewrite 1 k (arithmeticSuccCode (auxName k)) e))))
    (allAuxCode k e))

def robinsonAxiom : Fin 7 → language.Sentence :=
  ![qSuccNeZero, qSuccInjective, qPredecessor, qAddZero, qAddSucc, qMulZero, qMulSucc]

def robinsonCodes : List ℕ := List.ofFn (fun i =>
  sentenceCode arithmeticSignature (robinsonAxiom i))

/-- A certificate is precisely `[i]`, `i < 7`, or `[7,k,e]` where `e` is an
arithmetic formula with no auxiliary names beyond the displayed parameters
and induction variable. Every malformed certificate is rejected. -/
def paAxiomCertificate (n s : ℕ) : Bool :=
  let aa := Seq.decode s
  if aa.length = 1 then
    decide (aa[0]?.getD 0 < 7) && decide (n = robinsonCodes[aa[0]?.getD 0]?.getD 0)
  else if aa.length = 3 ∧ aa[0]?.getD 0 = 7 then
    let k := aa[1]?.getD 0
    let e := aa[2]?.getD 0
    namedForm arithmeticSignature 0 e &&
      decide ((stats arithmeticSignature e).2.2.2 ≤ k + 1) &&
      decide (n = inductionCode k e)
  else false

variable {α : Type*} [Primcodable α]

@[fun_prop] private theorem succ_comp {f : α → ℕ} (hf : Primrec f) :
    Primrec (fun x => Nat.succ (f x)) := Primrec.succ.comp hf

@[fun_prop] private theorem node_comp {t : α → ℕ} {aa : α → List ℕ}
    (ht : Primrec t) (ha : Primrec aa) : Primrec (fun x => node (t x) (aa x)) :=
  primrec_node.comp ht ha

@[fun_prop] private theorem entry_comp {h i : α → ℕ}
    (hh : Primrec h) (hi : Primrec i) : Primrec (fun x => Seq.entry (h x) (i x)) :=
  FiniteSequenceCoding.primrec_entry.comp hh hi

private theorem bindStep_primitive (single : Bool) :
    Primrec (fun p : ℕ × ℕ × ℕ => bindStep single p.1 p.2.1 p.2.2) := by
  unfold bindStep boundName
  simp only [← Bool.cond_decide, Bool.decide_or]
  fun_prop

theorem bindCode_primitive (single : Bool) : Primrec₂ (bindCode single) := by
  exact FiniteSequenceCoding.primrec_historyValue_param (bindStep_primitive single)

@[fun_prop] private theorem bindCode_comp (single : Bool) {k e : α → ℕ}
    (hk : Primrec k) (he : Primrec e) :
    Primrec (fun x => bindCode single (k x) (e x)) :=
  (bindCode_primitive single).comp hk he

@[fun_prop] private theorem allCode_comp {e : α → ℕ} (he : Primrec e) :
    Primrec (fun x => allCode (e x)) := by unfold allCode; fun_prop

theorem closeCode_primitive : Primrec₂ closeCode := by
  unfold Primrec₂ closeCode
  exact Primrec.nat_iterate Primrec.fst
    (bindCode_primitive false)
    (by unfold Primrec₂; fun_prop)

@[fun_prop] private theorem closeCode_comp {k e : α → ℕ}
    (hk : Primrec k) (he : Primrec e) :
    Primrec (fun x => closeCode (k x) (e x)) := closeCode_primitive.comp hk he

@[fun_prop] private theorem rewrite_comp {m i t e : α → ℕ}
    (hm : Primrec m) (hi : Primrec i) (ht : Primrec t) (he : Primrec e) :
    Primrec (fun x => rewrite (m x) (i x) (t x) (e x)) :=
  primrec_rewrite.comp (hm.pair (hi.pair (ht.pair he)))

theorem inductionCode_primitive : Primrec₂ inductionCode := by
  unfold Primrec₂ inductionCode allAuxCode andCode negCode impCode
    arithmeticSuccCode auxName botCode
  fun_prop

@[fun_prop] private theorem inductionCode_comp {k e : α → ℕ}
    (hk : Primrec k) (he : Primrec e) :
    Primrec (fun x => inductionCode (k x) (e x)) := inductionCode_primitive.comp hk he

@[fun_prop] private theorem namedForm_comp {n e : α → ℕ}
    (hn : Primrec n) (he : Primrec e) :
    Primrec (fun x => namedForm arithmeticSignature (n x) (e x)) :=
  (primrec_namedForm arithmeticSignature).comp hn he

@[fun_prop] private theorem stats_comp {e : α → ℕ} (he : Primrec e) :
    Primrec (fun x => stats arithmeticSignature (e x)) :=
  (primrec_stats arithmeticSignature).comp he

attribute [local irreducible] stats namedForm inductionCode robinsonCodes

set_option maxHeartbeats 1200000 in
/-- Primitive recursiveness is for this explicit certificate algorithm. -/
theorem paAxiomCertificate_primitive : Primrec₂ paAxiomCertificate := by
  unfold Primrec₂ paAxiomCertificate Seq.decode
  simp only [← Bool.cond_decide, Bool.decide_and]
  fun_prop

private theorem bind_node (single : Bool) (k t : ℕ) (aa : List ℕ)
    (h1 : t ≠ 1) (h8 : t ≠ 8) :
    bindCode single k (node t aa) = node t
      (if t = 2 ∨ t = 5 then aa[0]?.getD 0 :: aa.tail.map (bindCode single k)
       else aa.map (bindCode single k)) := by
  let e := node t aa
  let h := bindStep single k
  have he : e ≠ 0 := by simp [e, node]
  have hm : aa.map (Seq.entry (FiniteSequenceCoding.historyCode h e)) =
      aa.map (bindCode single k) := by
    apply List.map_congr_left
    intro c hc
    exact earlier_history_entry h e c (child_lt hc)
  have ht : aa.tail.map (Seq.entry (FiniteSequenceCoding.historyCode h e)) =
      aa.tail.map (bindCode single k) := by
    apply List.map_congr_left
    intro c hc
    exact earlier_history_entry h e c (child_lt (List.mem_of_mem_tail hc))
  change bindStep single k e (FiniteSequenceCoding.historyCode h e) = _
  simp only [bindStep, he, ↓reduceIte, e, node_tag, h1, h8, node_args, arg]
  split
  · rw [ht]
  · rw [hm]

@[simp] private theorem bind_aux (single : Bool) (k j : ℕ) :
    bindCode single k (auxName j) =
      if single then (if j = k then boundName 0 else auxName j) else boundName j := by
  change bindStep single k (auxName j) _ = _
  have he : auxName j ≠ 0 := by simp [auxName, node]
  simp only [bindStep, ite_eq_right he]
  simp [auxName, node_tag, arg, node_args]

@[simp] private theorem bind_bound (single : Bool) (k j : ℕ) :
    bindCode single k (boundName j) = boundName (j + if single then 1 else k) := by
  change bindStep single k (boundName j) _ = _
  have he : boundName j ≠ 0 := by simp [boundName, node]
  simp only [bindStep, ite_eq_right he]
  simp [boundName, node_tag, arg, node_args]

attribute [local irreducible] bindCode

private theorem bind_term {β : Type*} (name out : β → ℕ) (single : Bool) (k : ℕ)
    (hv : ∀ x, bindCode single k (name x) = out x) (t : language.Term β) :
    bindCode single k (termCode arithmeticSignature name t) =
      termCode arithmeticSignature out t := by
  induction t with
  | var x => exact hv x
  | func f ts ih =>
    simp only [termCode]
    rw [bind_node single k 2 _ (by decide) (by decide)]
    simp only [true_or, ↓reduceIte, List.getElem?_cons_zero, Option.getD_some,
      List.tail_cons, List.map_ofFn, Function.comp_def, ih]

private theorem bind_codeAt {β : Type*} (name out : β → ℕ) (single : Bool) (k o : ℕ)
    (hv : ∀ x, bindCode single k (name x) = out x) {n : ℕ}
    (a : language.BoundedFormula β n) :
    bindCode single k (codeAt arithmeticSignature name o a) =
      codeAt arithmeticSignature out (o + if single then 1 else k) a := by
  have ht (n : ℕ) (t : language.Term (β ⊕ Fin n)) :
      bindCode single k
        (termCode arithmeticSignature (Sum.elim name (fun j => boundName (o + j.val))) t) =
      termCode arithmeticSignature
        (Sum.elim out (fun j => boundName ((o + if single then 1 else k) + j.val))) t := by
    apply bind_term
    intro x
    cases x with
    | inl x => exact hv x
    | inr j => simp only [Sum.elim_inr, bind_bound]; congr 1; omega
  induction a with
  | falsum =>
    change bindCode single k (node 3 []) = node 3 []
    simp [bind_node]
  | equal s t =>
    simp only [codeAt, equalCode]
    rw [bind_node single k 4 _ (by decide) (by decide)]
    simp [ht]
  | rel r ts => exact r.elim
  | imp a b iha ihb =>
    simp only [codeAt, impCode]
    rw [bind_node single k 6 _ (by decide) (by decide)]
    simp [iha, ihb]
  | all a ih =>
    simp only [codeAt, allCode]
    rw [bind_node single k 7 _ (by decide) (by decide)]
    simp [ih]

private theorem formulaCode_alls {β : Type*} (name : β → ℕ) {n : ℕ}
    (a : language.BoundedFormula β n) :
    formulaCode arithmeticSignature name a.alls =
      (allCode^[n]) (formulaCode arithmeticSignature name a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [BoundedFormula.alls, ih]
    change (allCode^[n]) (allCode (formulaCode arithmeticSignature name a)) = _
    exact (Function.iterate_succ_apply _ _ _).symm

private theorem close_code {k : ℕ} (a : language.Formula (Fin k)) :
    sentenceCode arithmeticSignature (close a) =
      closeCode k (formulaCode arithmeticSignature (fun i : Fin k => auxName i.val) a) := by
  unfold close sentenceCode closeCode
  rw [formulaCode_alls]
  congr 1
  rw [← codeAt_zero arithmeticSignature Empty.elim,
    codeAt_relabel arithmeticSignature Empty.elim 0]
  simp only [Sum.elim_inr, Nat.zero_add]
  simpa only [codeAt_zero, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] using
    (bind_codeAt (fun i : Fin k => auxName i.val) (fun i => boundName i.val)
      false k 0 (fun i => by simp) a).symm

private def inductionName (k : ℕ) : Fin k ⊕ Unit → ℕ :=
  Sum.elim Fin.val (fun _ => k)

private theorem allUnit_code {k : ℕ} (a : language.Formula (Fin k ⊕ Unit)) :
    formulaCode arithmeticSignature (fun i : Fin k => auxName i.val) (allUnit a) =
      allAuxCode k (formulaCode arithmeticSignature (fun i => auxName (inductionName k i)) a) := by
  unfold allUnit allAuxCode
  change allCode (formulaCode arithmeticSignature _ _) = _
  congr 1
  rw [← codeAt_zero arithmeticSignature (fun i : Fin k => auxName i.val),
    codeAt_relabel arithmeticSignature (fun i : Fin k => auxName i.val) 0]
  simp only [Nat.zero_add]
  have h := bind_codeAt (fun i => auxName (inductionName k i))
    (Sum.elim (fun i : Fin k => auxName i.val) (fun _ : Unit => boundName 0)) true k 0
    (fun x => by
      cases x with
      | inl i => simp [inductionName, ne_of_lt i.isLt]
      | inr i => simp [inductionName]) a
  have hn : (fun x : Fin k ⊕ Unit =>
      Sum.elim (fun i : Fin k => auxName i.val) (fun j : Fin 1 => boundName j.val)
        (Sum.elim Sum.inl (fun _ : Unit => Sum.inr (0 : Fin 1)) x)) =
      Sum.elim (fun i : Fin k => auxName i.val) (fun _ : Unit => boundName 0) := by
    funext x
    cases x <;> rfl
  rw [hn]
  simpa only [codeAt_zero, ↓reduceIte, Nat.zero_add] using h.symm

private theorem formulaCode_and {β : Type*} (name : β → ℕ) {n : ℕ}
    (a b : language.BoundedFormula β n) :
    formulaCode arithmeticSignature name (a ⊓ b) =
      andCode (formulaCode arithmeticSignature name a) (formulaCode arithmeticSignature name b) := rfl

private theorem induction_code {k : ℕ} (a : language.Formula (Fin k ⊕ Unit)) :
    sentenceCode arithmeticSignature (inductionAxiom a) =
      inductionCode k (formulaCode arithmeticSignature (fun i => auxName (inductionName k i)) a) := by
  unfold inductionAxiom inductionCode
  rw [close_code]
  apply congrArg (closeCode k)
  have hbase := rewrite_subst_formula arithmeticSignature
    (fun i => auxName (inductionName k i)) (fun i : Fin k => auxName i.val)
    1 k arithmeticZeroCode (Sum.elim Term.var (fun _ => zeroTerm))
    (by decide) (fun i => by
      cases i with
      | inl i => simp [inductionName, ne_of_lt i.isLt, termCode]
      | inr i => simp [inductionName, arithmeticZeroCode, zeroTerm, termCode]) a
  have hstep := rewrite_subst_formula arithmeticSignature
    (fun i => auxName (inductionName k i)) (fun i => auxName (inductionName k i))
    1 k (arithmeticSuccCode (auxName k))
    (Sum.elim (fun i => .var (.inl i)) (fun _ => succTerm (.var (.inr ()))))
    (by decide) (fun i => by
      cases i with
      | inl i => simp [inductionName, ne_of_lt i.isLt, termCode]
      | inr i => simp [inductionName, arithmeticSuccCode, termCode, succTerm,
          arithmeticSignature, arithFunctionCode]) a
  rw [formulaCode, formulaCode_and, allUnit_code, allUnit_code, ← hbase]
  simp only [formulaCode]
  rw [← hstep]

private theorem fold_aux_bound (xs : List Stats) (b z : ℕ) (hz : z ≤ b)
    (h : ∀ s ∈ xs, s.2.2.2 ≤ b) :
    xs.foldl (fun n s => max n s.2.2.2) z ≤ b := by
  induction xs generalizing z with
  | nil => exact hz
  | cons s xs ih =>
    apply ih (max z s.2.2.2) (max_le hz (h s (by simp)))
    intro t ht
    exact h t (by simp [ht])

private theorem term_aux_bound {β : Type*} (name : β → ℕ) (b : ℕ)
    (hv : ∀ x, (stats arithmeticSignature (name x)).2.2.2 ≤ b)
    (t : language.Term β) :
    (stats arithmeticSignature (termCode arithmeticSignature name t)).2.2.2 ≤ b := by
  induction t with
  | var x => exact hv x
  | @func n f ts ih =>
    have hm := fold_aux_bound
      ((List.ofFn (fun i : Fin n => termCode arithmeticSignature name (ts i))).map
        (stats arithmeticSignature)) b 0 (Nat.zero_le _) (by
          intro s hs
          rcases List.mem_map.mp hs with ⟨e, he, rfl⟩
          rcases List.mem_ofFn.mp he with ⟨i, rfl⟩
          exact ih i)
    simp only [termCode, stats_node, summaryValue, List.length_cons,
      List.length_ofFn, List.getElem?_cons_zero, Option.getD_some,
      Nat.add_sub_cancel, List.tail_cons, Nat.reduceEqDiff,
      or_false, ↓reduceIte]
    split
    · exact hm
    · exact Nat.zero_le _

private theorem formula_aux_bound {β : Type*} (name : β → ℕ) (b : ℕ)
    (hv : ∀ x, (stats arithmeticSignature (name x)).2.2.2 ≤ b)
    {n : ℕ} (a : language.BoundedFormula β n) :
    (stats arithmeticSignature (formulaCode arithmeticSignature name a)).2.2.2 ≤ b := by
  have ht (n : ℕ) (t : language.Term (β ⊕ Fin n)) :
      (stats arithmeticSignature
        (termCode arithmeticSignature (Sum.elim name (fun j => boundName j.val)) t)).2.2.2 ≤ b := by
    apply term_aux_bound
    intro x
    cases x with
    | inl x => exact hv x
    | inr i => simp
  induction a with
  | falsum => simp [formulaCode]
  | equal s t =>
    have hs := ht _ s
    have ht' := ht _ t
    simp only [formulaCode, equalCode, stats_node, summaryValue, List.length_cons,
      List.length_nil, List.map_cons, List.map_nil, Nat.reduceEqDiff, or_self,
      ↓reduceIte, List.foldl_cons, List.foldl_nil, max_eq_right (Nat.zero_le _)]
    split <;> simp_all only [max_le_iff, Nat.zero_le, and_self]
  | rel r ts => exact r.elim
  | imp a c iha ihc =>
    simp only [formulaCode, impCode, stats_node, summaryValue, List.length_cons,
      List.length_nil, List.map_cons, List.map_nil, Nat.reduceEqDiff, or_self,
      ↓reduceIte, List.foldl_cons, List.foldl_nil, max_eq_right (Nat.zero_le _)]
    split <;> simp_all only [max_le_iff, Nat.zero_le, and_self]
  | all a ih =>
    simp only [formulaCode, allCode, stats_node, summaryValue, List.length_cons,
      List.length_nil, List.map_cons, List.map_nil, Nat.reduceEqDiff, or_self,
      ↓reduceIte, List.foldl_cons, List.foldl_nil, max_eq_right (Nat.zero_le _)]
    split <;> simp_all

private theorem induction_input_valid {k : ℕ} (a : language.Formula (Fin k ⊕ Unit)) :
    namedForm arithmeticSignature 0
      (formulaCode arithmeticSignature (fun i => auxName (inductionName k i)) a) = true ∧
    (stats arithmeticSignature
      (formulaCode arithmeticSignature (fun i => auxName (inductionName k i)) a)).2.2.2 ≤ k + 1 := by
  constructor
  · apply (named_recognition_iff arithmeticSignature 0 _).mpr
    refine ⟨a.relabel (inductionName k), ?_⟩
    exact formulaCode_relabel arithmeticSignature auxName _ a
  · apply formula_aux_bound
    intro i
    cases i with
    | inl i => simp [inductionName]
    | inr i => simp [inductionName]

private theorem induction_input_decode {k e : ℕ}
    (he : namedForm arithmeticSignature 0 e = true)
    (hb : (stats arithmeticSignature e).2.2.2 ≤ k + 1) :
    ∃ a : language.Formula (Fin k ⊕ Unit),
      formulaCode arithmeticSignature (fun i => auxName (inductionName k i)) a = e := by
  obtain ⟨a, ha⟩ := (named_recognition_iff arithmeticSignature 0 e).mp he
  have hx (x : a.freeVarFinset) : x.val ≤ k := by
    have h := named_aux_mem_bound arithmeticSignature a x.property
    rw [ha] at h
    omega
  let f : a.freeVarFinset → Fin k ⊕ Unit := fun x =>
    if h : x.val < k then .inl ⟨x.val, h⟩ else .inr ()
  refine ⟨a.restrictFreeVar f, ?_⟩
  apply (formulaCode_restrictFreeVar arithmeticSignature auxName
    (fun i => auxName (inductionName k i)) a f ?_).trans ha
  intro x
  dsimp [f]
  split
  · rfl
  · have hxeq : x.val = k := by have := hx x; omega
    simp [inductionName, hxeq]

/-- The generated sentence codes are exactly the actual PA axiom set. -/
theorem paAxiomCertificate_theory :
    theory arithmeticSignature paAxiomCertificate = PA := by
  have hrob (i : Fin 7) : robinsonAxiom i ∈ Q := by
    fin_cases i <;> simp [robinsonAxiom, Q]
  have hget (i : Fin 7) : robinsonCodes[i.val]?.getD 0 =
      sentenceCode arithmeticSignature (robinsonAxiom i) := by
    simp only [robinsonCodes, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]
  have hrobcode (i : Fin 7) :
      paAxiomCertificate (sentenceCode arithmeticSignature (robinsonAxiom i))
        (Seq.code [i.val]) = true := by
    simp [paAxiomCertificate, Seq.decode, Seq.code, robinsonCodes, i.isLt]
    fin_cases i <;> rfl
  have hind {k : ℕ} (a : language.Formula (Fin k ⊕ Unit)) :
      paAxiomCertificate (sentenceCode arithmeticSignature (inductionAxiom a))
        (Seq.code [7, k,
          formulaCode arithmeticSignature (fun i => auxName (inductionName k i)) a]) = true := by
    obtain ⟨hv, hb⟩ := induction_input_valid a
    simp [paAxiomCertificate, Seq.decode, Seq.code, hv, hb, induction_code]
  ext A
  constructor
  · rintro ⟨s, hs⟩
    unfold paAxiomCertificate at hs
    dsimp only at hs
    split at hs
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      let i : Fin 7 := ⟨(Seq.decode s)[0]?.getD 0, hs.1⟩
      have hc : sentenceCode arithmeticSignature A =
          sentenceCode arithmeticSignature (robinsonAxiom i) := by
        exact hs.2.trans (hget i)
      have hA := sentence_code_injective arithmeticSignature hc
      exact Or.inl (hA.symm ▸ hrob i)
    · split at hs
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨a, ha⟩ := induction_input_decode hs.1.1 hs.1.2
        have hc : sentenceCode arithmeticSignature A =
            sentenceCode arithmeticSignature (inductionAxiom a) := by
          rw [induction_code, ha]
          exact hs.2
        exact Or.inr ⟨_, a, sentence_code_injective arithmeticSignature hc⟩
      · simp at hs
  · intro hA
    rcases hA with hA | ⟨k, a, rfl⟩
    · have hi : ∃ i : Fin 7, A = robinsonAxiom i := by
        simp only [Q, Set.mem_insert_iff, Set.mem_singleton_iff] at hA
        rcases hA with h | h | h | h | h | h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
        · exact ⟨2, h⟩
        · exact ⟨3, h⟩
        · exact ⟨4, h⟩
        · exact ⟨5, h⟩
        · exact ⟨6, h⟩
      obtain ⟨i, rfl⟩ := hi
      exact ⟨Seq.code [i.val], hrobcode i⟩
    · exact ⟨Seq.code [7, k,
        formulaCode arithmeticSignature (fun i => auxName (inductionName k i)) a], hind a⟩

theorem pa_proof_checker_primitive :
    Primrec₂ (certificateCheck arithmeticSignature paAxiomCertificate) := by
  exact primrec_certificateCheck arithmeticSignature _ paAxiomCertificate_primitive

theorem pa_proof_checker_correct (A : language.Sentence) :
    (∃ p, certificateCheck arithmeticSignature paAxiomCertificate p
      (sentenceCode arithmeticSignature A) = true) ↔ FirstOrderProofs.Derives PA A := by
  rw [certificate_iff_derives, paAxiomCertificate_theory]

end
end Lemmatheca.MathematicalLogic.ArithmeticProofPredicates
