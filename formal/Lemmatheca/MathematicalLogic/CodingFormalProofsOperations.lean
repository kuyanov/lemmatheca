import Lemmatheca.MathematicalLogic.CodingFormalProofsSyntax
import Lemmatheca.MathematicalLogic.CodingFormalProofsRelabel
import Lemmatheca.MathematicalLogic.CodingFormalProofsOffsets

namespace Lemmatheca.MathematicalLogic.CodingFormalProofs
open FirstOrder FirstOrder.Language
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

theorem earlier_history_entry (h : ℕ → ℕ → ℕ) (e c : ℕ) (hc : c < e) :
    Seq.entry (FiniteSequenceCoding.historyCode h e) c = earlierFold h c := by
  simp only [FiniteSequenceCoding.entry,FiniteSequenceCoding.history_identity,
    List.getElem?_map,List.getElem?_range hc,Option.map_some,Option.getD_some]
  rfl

theorem rewrite_node (m i t k : ℕ) (aa : List ℕ)
    (h0 : k ≠ 0) (h1 : k ≠ 1) (h8 : k ≠ 8) :
    rewrite m i t (node k aa) = node k
      (if k = 2 ∨ k = 5 then aa[0]?.getD 0 :: aa.tail.map (rewrite m i t)
       else aa.map (rewrite m i t)) := by
  let e := node k aa
  let h := rewriteStep m i t
  have he : e ≠ 0 := by simp [e,node]
  have hm : aa.map (Seq.entry (FiniteSequenceCoding.historyCode h e)) =
      aa.map (rewrite m i t) := by
    apply List.map_congr_left
    intro c hc
    exact earlier_history_entry h e c (child_lt hc)
  have ht : aa.tail.map (Seq.entry (FiniteSequenceCoding.historyCode h e)) =
      aa.tail.map (rewrite m i t) := by
    apply List.map_congr_left
    intro c hc
    exact earlier_history_entry h e c (child_lt (List.mem_of_mem_tail hc))
  change rewriteStep m i t e (FiniteSequenceCoding.historyCode h e) = _
  simp only [rewriteStep,he,↓reduceIte]
  simp only [e,node_tag,h0,h1,h8,↓reduceIte,node_args,arg]
  change node k (if k = 2 ∨ k = 5 then _ :: aa.tail.map (Seq.entry (FiniteSequenceCoding.historyCode h e)) else aa.map (Seq.entry (FiniteSequenceCoding.historyCode h e))) = _
  split
  · rw [ht]
  · rw [hm]

@[simp] theorem rewrite_free (m i t j : ℕ) :
    rewrite m i t (freeName j) = if m = 0 ∧ j = i then t else freeName j := by
  change rewriteStep m i t (freeName j) _ = _
  have he : freeName j ≠ 0 := by simp [freeName,node]
  simp only [rewriteStep,ite_eq_right he]
  simp only [freeName,node_tag,arg,node_args,List.getElem?_cons_zero,Option.getD_some,↓reduceIte]

@[simp] theorem rewrite_aux (m i t j : ℕ) :
    rewrite m i t (auxName j) = if m = 1 ∧ j = i then t else auxName j := by
  change rewriteStep m i t (auxName j) _ = _
  have he : auxName j ≠ 0 := by simp [auxName,node]
  simp only [rewriteStep,ite_eq_right he]
  simp only [auxName,node_tag,arg,node_args,List.getElem?_cons_zero,Option.getD_some,↓reduceIte]
  simp

@[simp] theorem rewrite_bound (m i t j : ℕ) :
    rewrite m i t (boundName j) =
      if m = 2 then (if j = 0 then t else boundName (j-1)) else boundName j := by
  change rewriteStep m i t (boundName j) _ = _
  have he : boundName j ≠ 0 := by simp [boundName,node]
  simp only [rewriteStep,ite_eq_right he]
  simp only [boundName,node_tag,arg,node_args,List.getElem?_cons_zero,Option.getD_some,↓reduceIte]
  simp

attribute [local irreducible] rewrite stats

theorem rewrite_term {α β : Type*} (name : α → ℕ) (out : β → ℕ)
    (m i t : ℕ) (σ : α → L.Term β)
    (hv : ∀ x, rewrite m i t (name x) = termCode S out (σ x)) (s : L.Term α) :
    rewrite m i t (termCode S name s) = termCode S out (s.subst σ) := by
  induction s with
  | var x => exact hv x
  | @func n f ss ih =>
    simp only [termCode,Term.subst]
    rw [rewrite_node m i t 2 _ (by decide) (by decide) (by decide)]
    simp only [true_or,↓reduceIte,List.getElem?_cons_zero,Option.getD_some,List.tail_cons,
      List.map_ofFn,Function.comp_def,ih]

theorem rewrite_subst_formula {α β : Type*} (name : α → ℕ) (out : β → ℕ)
    (m i t : ℕ) (σ : α → L.Term β) (hm : m ≠ 2)
    (hv : ∀ x, rewrite m i t (name x) = termCode S out (σ x))
    {n : ℕ} (a : L.BoundedFormula α n) :
    rewrite m i t (formulaCode S name a) = formulaCode S out (a.subst σ) := by
  have ht (n : ℕ) (s : L.Term (α ⊕ Fin n)) :
      rewrite m i t (termCode S (Sum.elim name (fun j => boundName j.val)) s) =
      termCode S (Sum.elim out (fun j => boundName j.val))
        (s.subst (Sum.elim (Term.relabel Sum.inl ∘ σ) (Term.var ∘ Sum.inr))) := by
    apply rewrite_term
    intro x
    cases x with
    | inl x => simpa [termCode_relabel,Function.comp_def] using hv x
    | inr j => simp [rewrite_bound,hm,termCode]
  induction a with
  | falsum =>
    change rewrite m i t (node 3 []) = node 3 []
    simp [rewrite_node]
  | equal s u =>
    simp only [BoundedFormula.subst,BoundedFormula.mapTermRel,formulaCode,equalCode]
    rw [rewrite_node m i t 4 _ (by decide) (by decide) (by decide)]
    simp [ht]
  | rel r ss =>
    simp only [BoundedFormula.subst,BoundedFormula.mapTermRel,formulaCode,id_eq]
    rw [rewrite_node m i t 5 _ (by decide) (by decide) (by decide)]
    simp [ht,List.map_ofFn,Function.comp_def]
  | imp a b iha ihb =>
    simp only [BoundedFormula.subst,BoundedFormula.mapTermRel,formulaCode,impCode] at *
    rw [rewrite_node m i t 6 _ (by decide) (by decide) (by decide)]
    simp [iha,ihb]
  | all a ih =>
    simp only [BoundedFormula.subst,BoundedFormula.mapTermRel,formulaCode,allCode] at *
    rw [rewrite_node m i t 7 _ (by decide) (by decide) (by decide)]
    simp [ih]

theorem rewrite_open_formula {α β : Type*} (name : α → ℕ) (out : β → ℕ)
    (o i t : ℕ) (σ : α → L.Term β)
    (hv : ∀ x, rewrite 2 i t (name x) = termCode S out (σ x))
    {n : ℕ} (a : L.BoundedFormula α n) :
    rewrite 2 i t (codeAt S name (o+1) a) = codeAt S out o (a.subst σ) := by
  have ht (n : ℕ) (s : L.Term (α ⊕ Fin n)) :
      rewrite 2 i t (termCode S (Sum.elim name (fun j => boundName (o+1+j.val))) s) =
      termCode S (Sum.elim out (fun j => boundName (o+j.val)))
        (s.subst (Sum.elim (Term.relabel Sum.inl ∘ σ) (Term.var ∘ Sum.inr))) := by
    apply rewrite_term
    intro x
    cases x with
    | inl x => simpa [termCode_relabel,Function.comp_def] using hv x
    | inr j =>
      have hs : o+1+j.val-1 = o+j.val := by omega
      simp [rewrite_bound,hs,termCode]
  induction a with
  | falsum =>
    change rewrite 2 i t (node 3 []) = node 3 []
    simp [rewrite_node]
  | equal s u =>
    simp only [BoundedFormula.subst,BoundedFormula.mapTermRel,codeAt,equalCode]
    rw [rewrite_node 2 i t 4 _ (by decide) (by decide) (by decide)]
    simp [ht]
  | rel r ss =>
    simp only [BoundedFormula.subst,BoundedFormula.mapTermRel,codeAt,id_eq]
    rw [rewrite_node 2 i t 5 _ (by decide) (by decide) (by decide)]
    simp [ht,List.map_ofFn,Function.comp_def]
  | imp a b iha ihb =>
    simp only [BoundedFormula.subst,BoundedFormula.mapTermRel,codeAt,impCode] at *
    rw [rewrite_node 2 i t 6 _ (by decide) (by decide) (by decide)]
    simp [iha,ihb]
  | all a ih =>
    simp only [BoundedFormula.subst,BoundedFormula.mapTermRel,codeAt,allCode] at *
    rw [rewrite_node 2 i t 7 _ (by decide) (by decide) (by decide)]
    simp [ih]

theorem occurs_node (j k : ℕ) (aa : List ℕ)
    (h0 : k ≠ 0) (h1 : k ≠ 1) (h8 : k ≠ 8) :
    occursAux j (node k aa) =
      (if k = 2 ∨ k = 5 then aa.tail else aa).any (occursAux j) := by
  let e := node k aa
  let hist := FiniteSequenceCoding.historyCode (occursStep j) e
  have hm : (children e).any (fun c => decide (Seq.entry hist c > 0)) =
      (children e).any (occursAux j) := by
    have hh : (children e).map (fun c => decide (Seq.entry hist c > 0)) =
        (children e).map (occursAux j) := by
      apply List.map_congr_left
      intro c hc
      rw [earlier_history_entry (occursStep j) e c
        (raw_child_lt e c (by simp [e,node]) (child_mem_args e c hc))]
      rfl
    have hh' := congrArg (fun xs : List Bool => xs.any id) hh
    simpa only [List.any_map,Function.comp_def,id_eq] using hh'

  change decide (0 < occursStep j e hist) = _
  simp only [occursStep,e,node_tag,h0,h1,h8,↓reduceIte,false_or,hm]
  change decide (0 < if (children e).any (occursAux j) then 1 else 0) = _
  have hchildren : children e = if k = 2 ∨ k = 5 then aa.tail else aa := by
    simp only [children,e,node_tag,node_args]
  rw [← hchildren]
  cases (children e).any (occursAux j) <;> rfl

@[simp] theorem occurs_aux (j i : ℕ) : occursAux j (auxName i) = decide (i=j) := by
  change decide (0 < occursStep j (auxName i) _) = _
  simp only [occursStep,auxName,node_tag,arg,node_args,List.getElem?_cons_zero,Option.getD_some,↓reduceIte]
  by_cases hi : i=j <;> simp [hi]

@[simp] theorem occurs_free (j i : ℕ) : occursAux j (freeName i) = false := by
  change decide (0 < occursStep j (freeName i) _) = _
  simp [occursStep,freeName,node_tag]

@[simp] theorem occurs_bound (j i : ℕ) : occursAux j (boundName i) = false := by
  change decide (0 < occursStep j (boundName i) _) = _
  simp [occursStep,boundName,node_tag]

attribute [local irreducible] occursAux

 theorem occurs_term {n : ℕ} (t : L.Term (ℕ ⊕ Fin n)) (j : ℕ) :
    occursAux j (termCode S (Sum.elim auxName (fun x => boundName x.val)) t) = true ↔
      j ∈ t.varFinsetLeft := by
  induction t with
  | var x => cases x <;> simp [termCode,Term.varFinsetLeft,eq_comm]
  | @func n f ts ih =>
    simp only [termCode]
    rw [occurs_node j 2 _ (by decide) (by decide) (by decide)]
    simp [List.any_eq_true,List.mem_ofFn,ih,Term.varFinsetLeft]

theorem occurs_mixed_term {n : ℕ} (t : L.Term ((ℕ ⊕ ℕ) ⊕ Fin n)) (j : ℕ) :
    occursAux j (termCode S (Sum.elim (Sum.elim freeName auxName) (fun x => boundName x.val)) t) = true ↔
      Sum.inr j ∈ t.varFinsetLeft := by
  induction t with
  | var x =>
    cases x with
    | inl x => cases x <;> simp [termCode,Term.varFinsetLeft,eq_comm]
    | inr x => simp [termCode,Term.varFinsetLeft]
  | @func n f ts ih =>
    simp only [termCode]
    rw [occurs_node j 2 _ (by decide) (by decide) (by decide)]
    simp [List.any_eq_true,List.mem_ofFn,ih,Term.varFinsetLeft]

theorem occurs_mixed_formula {n : ℕ} (a : L.BoundedFormula (ℕ ⊕ ℕ) n) (j : ℕ) :
    occursAux j (mixedCode S a) = true ↔ Sum.inr j ∈ a.freeVarFinset := by
  unfold mixedCode
  induction a with
  | falsum =>
    change occursAux j (node 3 []) = true ↔ _
    rw [occurs_node j 3 [] (by decide) (by decide) (by decide)]
    simp
  | equal s t =>
    simp only [formulaCode,equalCode]
    rw [occurs_node j 4 _ (by decide) (by decide) (by decide)]
    simp [occurs_mixed_term,BoundedFormula.freeVarFinset]
  | rel r ts =>
    simp only [formulaCode]
    rw [occurs_node j 5 _ (by decide) (by decide) (by decide)]
    simp [List.any_eq_true,List.mem_ofFn,occurs_mixed_term,BoundedFormula.freeVarFinset]
  | imp a b iha ihb =>
    simp only [formulaCode,impCode]
    rw [occurs_node j 6 _ (by decide) (by decide) (by decide)]
    simp [iha,ihb,BoundedFormula.freeVarFinset]
  | all a ih =>
    simp only [formulaCode,allCode]
    rw [occurs_node j 7 _ (by decide) (by decide) (by decide)]
    simpa using ih

theorem freshAux_absent (es : List ℕ) (a : ℕ) (ha : a ∈ es) (hv : ∃ n, isForm S n a = true) :
    occursAux (freshAux S es) a = false := by
  have hs (xs : List ℕ) (z : ℕ) : z ≤ xs.foldl (fun m e => max m (stats S e).2.2.2) z := by
    induction xs generalizing z with
    | nil => exact le_rfl
    | cons x xs ih => exact le_trans (le_max_left _ _) (ih _)
  have hb (xs : List ℕ) (z : ℕ) (ha : a ∈ xs) :
      (stats S a).2.2.2 ≤ xs.foldl (fun m e => max m (stats S e).2.2.2) z := by
    induction xs generalizing z with
    | nil => simp at ha
    | cons x xs ih =>
      rcases List.mem_cons.mp ha with h | h
      · subst x
        exact le_trans (le_max_right _ _) (hs xs _)
      · exact ih _ h
  apply Bool.eq_false_iff.mpr
  intro ho
  obtain ⟨n,hn⟩ := hv
  obtain ⟨φ,hφ⟩ := (mixed_recognition_iff S n a).mp hn
  have ho' : occursAux (freshAux S es) (mixedCode S φ) = true := by simpa only [hφ] using ho
  have hmem := (occurs_mixed_formula S φ _).mp ho'
  have hlt := mixed_aux_mem_bound S φ hmem
  rw [hφ] at hlt
  exact Nat.not_lt_of_ge (hb es 0 ha) hlt



theorem named_instantiate (a : L.BoundedFormula ℕ 1) (t : L.Term ℕ) :
    instantiate S (namedCode S a) (termCode S auxName t) = namedCode S (FirstOrderProofs.instantiate a t) := by
  have ha := (named_recognition_iff S 1 (namedCode S a)).mpr ⟨a,rfl⟩
  have ht := (named_term_recognition_iff S (termCode S auxName t)).mpr ⟨t,rfl⟩
  unfold instantiate
  rw [ha,ht]
  simp only [Bool.true_and,↓reduceIte]
  have hc := codeAt_toFormula S auxName 0 a
  simp only [Nat.zero_add,codeAt_zero] at hc
  change codeAt S (Sum.elim auxName (fun j : Fin 1 => boundName j.val)) 1 a.toFormula = namedCode S a at hc
  rw [← hc]
  change rewrite 2 0 (termCode S auxName t) (codeAt S _ (0+1) a.toFormula) = _
  rw [rewrite_open_formula S _ auxName 0 0 (termCode S auxName t)
    (Sum.elim Term.var (fun _ : Fin 1 => t))]
  · rw [codeAt_zero]
    rfl
  · intro x
    cases x with
    | inl j => simp [termCode]
    | inr j => simp [Fin.eq_zero j]




theorem substitution_correct {n : ℕ} (a : L.BoundedFormula ℕ n) (i : ℕ) (t : L.Term ℕ) :
    substitute S n (formulaCode S freeName a) i (termCode S freeName t) =
      formulaCode S freeName (a.subst (fun j => if j = i then t else .var j)) := by
  have ht : isTerm S 0 (termCode S freeName t) = true := by
    have h := term_code_recognition S (n := 0) (t.relabel Sum.inl)
    simpa only [termCode_relabel,Function.comp_def,Sum.elim_inl] using h
  unfold substitute
  rw [formula_code_recognition S a,ht]
  simp only [Bool.true_and,↓reduceIte]
  apply rewrite_subst_formula S freeName freeName 0 i _ _ (by decide)
  intro j
  by_cases hj : j = i <;> simp [hj,termCode]




theorem replaceAux_correct {n : ℕ} (a : L.BoundedFormula ℕ n) (i : ℕ) (t : L.Term ℕ) :
    replaceAux S n (namedCode S a) i (termCode S auxName t) =
      namedCode S (a.subst (fun j => if j = i then t else .var j)) := by
  have ha := (named_recognition_iff S n (namedCode S a)).mpr ⟨a,rfl⟩
  have ht := (named_term_recognition_iff S (termCode S auxName t)).mpr ⟨t,rfl⟩
  unfold replaceAux
  rw [ha,ht]
  simp only [Bool.true_and,↓reduceIte]
  apply rewrite_subst_formula S auxName auxName 1 i _ _ (by decide)
  intro j
  by_cases hj : j = i <;> simp [hj,termCode]




theorem occursAux_correct {n : ℕ} (a : L.BoundedFormula ℕ n) (j : ℕ) :
    occursAux j (namedCode S a) = true ↔ j ∈ a.freeVarFinset := by
  unfold namedCode
  induction a with
  | falsum =>
    change occursAux j (node 3 []) = true ↔ _
    rw [occurs_node j 3 [] (by decide) (by decide) (by decide)]
    simp
  | equal s t =>
    simp only [formulaCode,equalCode]
    rw [occurs_node j 4 _ (by decide) (by decide) (by decide)]
    simp [occurs_term,BoundedFormula.freeVarFinset]
  | rel r ts =>
    simp only [formulaCode]
    rw [occurs_node j 5 _ (by decide) (by decide) (by decide)]
    simp [List.any_eq_true,List.mem_ofFn,occurs_term,BoundedFormula.freeVarFinset]
  | imp a b iha ihb =>
    simp only [formulaCode,impCode]
    rw [occurs_node j 6 _ (by decide) (by decide) (by decide)]
    simp [iha,ihb,BoundedFormula.freeVarFinset]
  | all a ih =>
    simp only [formulaCode,allCode]
    rw [occurs_node j 7 _ (by decide) (by decide) (by decide)]
    simpa using ih




theorem negation_code (a : L.Sentence) : negCode (sentenceCode S a) = sentenceCode S a.not := by rfl






theorem arithmetic_numeral_code (m : ℕ) : numeralCode 0 1 m =
    termCode arithmeticSignature Empty.elim (ArithmeticTheories.numeral m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change node 2 [1,numeralCode 0 1 m] =
      node 2 [1,termCode arithmeticSignature Empty.elim (ArithmeticTheories.numeral m)]
    exact congrArg (fun e => node 2 [1,e]) ih



theorem mixed_substitution_correct {n : ℕ} (a : L.BoundedFormula (ℕ ⊕ ℕ) n)
    (i : ℕ) (t : L.Term (ℕ ⊕ ℕ)) :
    substitute S n (mixedCode S a) i (termCode S (Sum.elim freeName auxName) t) =
      mixedCode S (a.subst (fun j => if j = Sum.inl i then t else .var j)) := by
  have ha := (mixed_recognition_iff S n (mixedCode S a)).mpr ⟨a,rfl⟩
  have ht : isTerm S 0 (termCode S (Sum.elim freeName auxName) t) = true := by
    apply (mixed_term_recognition_iff S 0 _).mpr
    refine ⟨t.relabel Sum.inl,?_⟩
    simp only [termCode_relabel,Function.comp_def,Sum.elim_inl]
  unfold substitute
  rw [ha,ht]
  simp only [Bool.true_and,↓reduceIte]
  apply rewrite_subst_formula S (Sum.elim freeName auxName) (Sum.elim freeName auxName)
    0 i _ _ (by decide)
  intro j
  cases j with
  | inl j => by_cases hj : j = i <;> simp [hj,termCode]
  | inr j => simp [termCode]


end Lemmatheca.MathematicalLogic.CodingFormalProofs
