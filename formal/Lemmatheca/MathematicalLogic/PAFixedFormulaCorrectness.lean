import Lemmatheca.MathematicalLogic.PAFixedSyntaxCorrectness

/-! Exact native syntax summaries for the shared formula compiler, with the
number of available bound slots tracked through every quantifier. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.FixedSyntaxPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

def PureFormula (a : M) : Prop :=
  stats.value ![a] = modelSummary (zeroValue M) (numeralValue M 1) (zeroValue M) (zeroValue M)

def TermBound (k : ℕ) (a : M) : Prop :=
  ∃ d : M, leValue M (numeralValue M 1) d ∧ leValue M d (numeralValue M (k + 1)) ∧
    stats.value ![a] = modelSummary d (zeroValue M) (zeroValue M) (zeroValue M)

def FormulaBound (k : ℕ) (a : M) : Prop :=
  ∃ d : M, leValue M (numeralValue M 1) d ∧ leValue M d (numeralValue M (k + 1)) ∧
    stats.value ![a] = modelSummary (zeroValue M) d (zeroValue M) (zeroValue M)

private theorem numeral_le_model (m n : ℕ) (hmn : m ≤ n) :
    leValue M (numeralValue M m) (numeralValue M n) := by
  let := PA_models_Q M
  exact (finite_bound _ n).mpr ⟨m, hmn, rfl⟩

private theorem depth_ne_zero {d : M} (hd : leValue M (numeralValue M 1) d) :
    d ≠ zeroValue M := by
  intro hz
  rw [hz, numeral_value_succ, numeral_value_zero] at hd
  exact ((successor_le_iff_lt _ _).mp hd).2 (le_refl_value _)

private theorem bounded_join (k : ℕ) {a b : M}
    (ha : leValue M (numeralValue M 1) a ∧ leValue M a (numeralValue M (k + 1)))
    (hb : leValue M (numeralValue M 1) b ∧ leValue M b (numeralValue M (k + 1))) :
    leValue M (numeralValue M 1) (maximum.value ![maximum.value ![numeralValue M 1, a], b]) ∧
    leValue M (maximum.value ![maximum.value ![numeralValue M 1, a], b])
      (numeralValue M (k + 1)) := by
  let := modelLinearOrder M
  simp only [maximum_value]
  change numeralValue M 1 ≤ max (max (numeralValue M 1) a) b ∧
    max (max (numeralValue M 1) a) b ≤ numeralValue M (k + 1)
  exact ⟨le_trans (le_max_left _ _) (le_max_left _ _),
    max_le (max_le (numeral_le_model 1 (k + 1) (by omega)) ha.2) hb.2⟩

private theorem term_statsPart {a d : M}
    (ha : stats.value ![a] = modelSummary d (zeroValue M) (zeroValue M) (zeroValue M))
    (i : Fin 4) : statsPart i a = ![d, zeroValue M, zeroValue M, zeroValue M] i := by
  simp only [statsPart, ha, modelSummary_part_value]

private theorem formula_statsPart {a d : M}
    (ha : stats.value ![a] = modelSummary (zeroValue M) d (zeroValue M) (zeroValue M))
    (i : Fin 4) : statsPart i a = ![zeroValue M, d, zeroValue M, zeroValue M] i := by
  simp only [statsPart, ha, modelSummary_part_value]

 theorem PureTerm.termBound {a : M} (ha : PureTerm a) (k : ℕ) : TermBound k a :=
  ⟨numeralValue M 1, le_refl_value _, numeral_le_model 1 (k + 1) (by omega), ha.1⟩

 theorem TermBound.bound (k : ℕ) (i : Fin k) :
    TermBound k (modelNode 1 [numeralValue M i.val]) := by
  let := PA_models_Q M
  refine ⟨numeralValue M (i.val + 2), numeral_le_model 1 _ (by omega),
    numeral_le_model _ _ (by omega), ?_⟩
  rw [stats_bound_modelNode_value, numeral_add]

 theorem TermBound.succ {k : ℕ} {a : M} (ha : TermBound k a) :
    TermBound k (modelNode 2 [numeralValue M 1, a]) := by
  let := modelLinearOrder M
  obtain ⟨d, hd, hdk, hs⟩ := ha
  refine ⟨d, hd, hdk, ?_⟩
  rw [stats_succ_modelNode_value]
  simp only [term_statsPart hs, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.cons_val_three, depth_ne_zero hd, ↓reduceIte, Matrix.head_cons,
    Matrix.tail_cons, maximum_value, max_eq_right (show numeralValue M 1 ≤ d from hd), max_self]

 theorem TermBound.binary {k : ℕ} (f : ℕ) (hf : f = 2 ∨ f = 3)
    {a b : M} (ha : TermBound k a) (hb : TermBound k b) :
    TermBound k (modelNode 2 [numeralValue M f, a, b]) := by
  let := modelLinearOrder M
  obtain ⟨d, hd, hdk, hs⟩ := ha
  obtain ⟨e, he, hek, ht⟩ := hb
  obtain ⟨hp, hq⟩ := bounded_join k ⟨hd, hdk⟩ ⟨he, hek⟩
  refine ⟨_, hp, hq, ?_⟩
  rw [stats_binary_modelNode_value f hf]
  simp only [term_statsPart hs, term_statsPart ht, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.cons_val_three, depth_ne_zero hd, depth_ne_zero he,
    false_or, ↓reduceIte, Matrix.head_cons, Matrix.tail_cons, maximum_value, max_self]

 theorem FormulaBound.bottom (k : ℕ) : FormulaBound k (modelNode 3 ([] : List M)) :=
  ⟨numeralValue M 1, le_refl_value _, numeral_le_model 1 (k + 1) (by omega),
    stats_bot_modelNode_value⟩

 theorem FormulaBound.equal {k : ℕ} {a b : M} (ha : TermBound k a) (hb : TermBound k b) :
    FormulaBound k (modelNode 4 [a, b]) := by
  let := modelLinearOrder M
  obtain ⟨d, hd, hdk, hs⟩ := ha
  obtain ⟨e, he, hek, ht⟩ := hb
  obtain ⟨hp, hq⟩ := bounded_join k ⟨hd, hdk⟩ ⟨he, hek⟩
  refine ⟨_, hp, hq, ?_⟩
  rw [stats_equal_modelNode_value]
  simp only [term_statsPart hs, term_statsPart ht, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.cons_val_three, depth_ne_zero hd, depth_ne_zero he,
    false_or, ↓reduceIte, Matrix.head_cons, Matrix.tail_cons, maximum_value, max_self]

 theorem FormulaBound.imp {k : ℕ} {a b : M} (ha : FormulaBound k a) (hb : FormulaBound k b) :
    FormulaBound k (modelNode 6 [a, b]) := by
  let := modelLinearOrder M
  obtain ⟨d, hd, hdk, hs⟩ := ha
  obtain ⟨e, he, hek, ht⟩ := hb
  obtain ⟨hp, hq⟩ := bounded_join k ⟨hd, hdk⟩ ⟨he, hek⟩
  refine ⟨_, hp, hq, ?_⟩
  rw [stats_imp_modelNode_value]
  simp only [formula_statsPart hs, formula_statsPart ht, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, depth_ne_zero hd, depth_ne_zero he,
    false_or, ↓reduceIte, Matrix.head_cons, Matrix.tail_cons, maximum_value, max_self]

 theorem FormulaBound.all {k : ℕ} {a : M} (ha : FormulaBound (k + 1) a) :
    FormulaBound k (modelNode 7 [a]) := by
  let := modelLinearOrder M
  obtain ⟨d, hd, hdk, hs⟩ := ha
  obtain ⟨b, hdb⟩ := PAComputations.predecessor d (depth_ne_zero hd)
  have hb : leValue M b (numeralValue M (k + 1)) := by
    rw [hdb, show k + 1 + 1 = (k + 1) + 1 from rfl, numeral_value_succ] at hdk
    exact (successor_le_successor_value_iff _ _).mp hdk
  refine ⟨maximum.value ![numeralValue M 1, b], ?_, ?_, ?_⟩
  · rw [maximum_value]
    change numeralValue M 1 ≤ max (numeralValue M 1) b
    exact le_max_left _ _
  · rw [maximum_value]
    change max (numeralValue M 1) b ≤ numeralValue M (k + 1)
    exact max_le (numeral_le_model 1 _ (by omega)) hb
  · rw [stats_all_modelNode_value]
    simp only [formula_statsPart hs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [ite_eq_right (depth_ne_zero hd)]
    simp only [maximum_value, max_eq_right (show numeralValue M 1 ≤ d from hd), max_self]
    rw [hdb, predecessor_successor]

 theorem FormulaBound.pure {a : M} (ha : FormulaBound 0 a) : PureFormula a := by
  obtain ⟨d, hd, hd', hs⟩ := ha
  have he : d = numeralValue M 1 := le_antisymm_value hd' hd
  change stats.value ![a] = _
  simpa only [he] using hs

theorem FormulaBound.namedForm {k : ℕ} {a : M} (ha : FormulaBound k a) :
    CheckerPrograms.namedForm.value ![numeralValue M k, a] = numeralValue M 1 := by
  obtain ⟨d, hd, hdk, hs⟩ := ha
  apply CheckerPrograms.namedForm_of_stats (numeralValue M k) a d (zeroValue M) hs
    (depth_ne_zero hd)
  simpa only [numeral_value_succ] using hdk

 theorem PureFormula.formulaBound {a : M} (ha : PureFormula a) (k : ℕ) : FormulaBound k a :=
  ⟨numeralValue M 1, le_refl_value _, numeral_le_model 1 _ (by omega), ha⟩

 theorem PureFormula.sentence {a : M} (ha : PureFormula a) :
    CheckerPrograms.isSentence.value ![a] = numeralValue M 1 :=
  CheckerPrograms.isSentence_of_stats a ha

 theorem PureFormula.bottom : PureFormula (modelNode 3 ([] : List M)) :=
  stats_bot_modelNode_value

 theorem PureFormula.equal {a b : M} (ha : PureTerm a) (hb : PureTerm b) :
    PureFormula (modelNode 4 [a, b]) :=
  (FormulaBound.equal (ha.termBound 0) (hb.termBound 0)).pure

 theorem PureFormula.imp {a b : M} (ha : PureFormula a) (hb : PureFormula b) :
    PureFormula (modelNode 6 [a, b]) :=
  (FormulaBound.imp (ha.formulaBound 0) (hb.formulaBound 0)).pure

 theorem PureFormula.neg {a : M} (ha : PureFormula a) :
    PureFormula (modelNode 6 [a, modelNode 3 [] ]) := ha.imp PureFormula.bottom

 theorem termCode_bound {α : Type*} {r k : ℕ} (name : α → Program r)
    (hn : ∀ i (x : Fin r → M), TermBound k ((name i).value x))
    (t : language.Term α) (x : Fin r → M) : TermBound k ((termCode name t).value x) := by
  induction t with
  | var i => exact hn i x
  | func f ts ih =>
    rw [termCode_value]
    cases f with
    | zero => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_zero,
        numeral_value_zero] using (PureTerm.zero (M := M)).termBound k
    | succ => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_succ,
        List.ofFn_zero] using (TermBound.succ (ih 0))
    | add => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_succ,
        List.ofFn_zero, Fin.succ_zero_eq_one] using (TermBound.binary 2 (Or.inl rfl) (ih 0) (ih 1))
    | mul => simpa only [CodingFormalProofs.arithFunctionCode, List.ofFn_succ,
        List.ofFn_zero, Fin.succ_zero_eq_one] using (TermBound.binary 3 (Or.inr rfl) (ih 0) (ih 1))

 theorem formulaCode_bound {α : Type*} {r k : ℕ} (name : α → Program r)
    (hn : ∀ i (x : Fin r → M), PureTerm ((name i).value x))
    (A : language.BoundedFormula α k) (x : Fin r → M) :
    FormulaBound k ((formulaCode name A).value x) := by
  have hname (k : ℕ) (i : α ⊕ Fin k) (x : Fin r → M) :
      TermBound k ((Sum.elim name (fun i => syntaxNode 1 [constant i.val]) i).value x) := by
    cases i with
    | inl i => exact (hn i x).termBound k
    | inr i =>
      simpa only [Sum.elim_inr, syntaxNode_value, list_value, List.map_cons,
        List.map_nil, constant_value, modelNode] using (TermBound.bound (M := M) k i)
  induction A with
  | falsum =>
    simpa only [formulaCode, syntaxNode_value, list_nil_value, modelNode,
      modelList_nil] using FormulaBound.bottom (M := M) _
  | equal s t =>
    simpa only [formulaCode, syntaxNode_value, list_value, List.map_cons, List.map_nil, modelNode]
      using FormulaBound.equal (termCode_bound _ (hname _) s x) (termCode_bound _ (hname _) t x)
  | rel e _ => exact e.elim
  | imp a b iha ihb =>
    simpa only [formulaCode, syntaxNode_value, list_value, List.map_cons, List.map_nil, modelNode]
      using FormulaBound.imp iha ihb
  | all a ih =>
    simpa only [formulaCode, syntaxNode_value, list_value, List.map_cons, List.map_nil, modelNode]
      using FormulaBound.all ih

 theorem formulaCode_pure {α : Type*} {r : ℕ} (name : α → Program r)
    (hn : ∀ i (x : Fin r → M), PureTerm ((name i).value x))
    (A : language.Formula α) (x : Fin r → M) : PureFormula ((formulaCode name A).value x) :=
  (formulaCode_bound name hn A x).pure

 theorem substitution_pure {r : ℕ} (A : language.Formula (Fin r)) (x : Fin r → M) :
    PureFormula ((substitution A).value x) := by
  apply formulaCode_pure numeralName
  intro i x
  simp only [numeralName, unary_value, Program.value_proj]
  exact PureTerm.numeral _

/-- The same slot bound, allowing the auxiliary names used by proof rules. -/
def NamedTermBound (k : ℕ) (a : M) : Prop :=
  ∃ d av : M, leValue M (numeralValue M 1) d ∧ leValue M d (numeralValue M (k + 1)) ∧
    stats.value ![a] = modelSummary d (zeroValue M) (zeroValue M) av

def NamedFormulaBound (k : ℕ) (a : M) : Prop :=
  ∃ d av : M, leValue M (numeralValue M 1) d ∧ leValue M d (numeralValue M (k + 1)) ∧
    stats.value ![a] = modelSummary (zeroValue M) d (zeroValue M) av

private theorem named_term_part {a d av : M}
    (ha : stats.value ![a] = modelSummary d (zeroValue M) (zeroValue M) av)
    (i : Fin 4) : statsPart i a = ![d, zeroValue M, zeroValue M, av] i := by
  simp only [statsPart, ha, modelSummary_part_value]

private theorem named_formula_part {a d av : M}
    (ha : stats.value ![a] = modelSummary (zeroValue M) d (zeroValue M) av)
    (i : Fin 4) : statsPart i a = ![zeroValue M, d, zeroValue M, av] i := by
  simp only [statsPart, ha, modelSummary_part_value]

theorem TermBound.named {k : ℕ} {a : M} (ha : TermBound k a) : NamedTermBound k a := by
  obtain ⟨d, hd, hdk, hs⟩ := ha
  exact ⟨d, zeroValue M, hd, hdk, hs⟩

theorem NamedTermBound.aux (k : ℕ) (a : M) : NamedTermBound k (modelNode 8 [a]) :=
  ⟨numeralValue M 1, addValue M a (numeralValue M 1), le_refl_value _,
    numeral_le_model 1 _ (by omega), stats_aux_modelNode_value a⟩

theorem NamedTermBound.mono {k l : ℕ} {a : M} (ha : NamedTermBound k a) (hkl : k ≤ l) :
    NamedTermBound l a := by
  obtain ⟨d, av, hd, hdk, hs⟩ := ha
  exact ⟨d, av, hd, le_trans_value hdk (numeral_le_model _ _ (by omega)), hs⟩

theorem NamedTermBound.succ {k : ℕ} {a : M} (ha : NamedTermBound k a) :
    NamedTermBound k (modelNode 2 [numeralValue M 1, a]) := by
  let := modelLinearOrder M
  obtain ⟨d, av, hd, hdk, hs⟩ := ha
  refine ⟨d, maximum.value ![zeroValue M, av], hd, hdk, ?_⟩
  rw [stats_succ_modelNode_value]
  simp only [named_term_part hs, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, depth_ne_zero hd, ↓reduceIte,
    maximum_value, max_eq_right (show numeralValue M 1 ≤ d from hd), max_self]

theorem NamedTermBound.binary {k : ℕ} (f : ℕ) (hf : f = 2 ∨ f = 3)
    {a b : M} (ha : NamedTermBound k a) (hb : NamedTermBound k b) :
    NamedTermBound k (modelNode 2 [numeralValue M f, a, b]) := by
  let := modelLinearOrder M
  obtain ⟨d, av, hd, hdk, hs⟩ := ha
  obtain ⟨e, bv, he, hek, ht⟩ := hb
  obtain ⟨hp, hq⟩ := bounded_join k ⟨hd, hdk⟩ ⟨he, hek⟩
  refine ⟨_, maximum.value ![maximum.value ![zeroValue M, av], bv], hp, hq, ?_⟩
  rw [stats_binary_modelNode_value f hf]
  simp only [named_term_part hs, named_term_part ht, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    depth_ne_zero hd, depth_ne_zero he, false_or, ↓reduceIte, maximum_value, max_self]

theorem NamedFormulaBound.bottom (k : ℕ) : NamedFormulaBound k (modelNode 3 ([] : List M)) :=
  ⟨numeralValue M 1, zeroValue M, le_refl_value _, numeral_le_model 1 _ (by omega),
    stats_bot_modelNode_value⟩

theorem NamedFormulaBound.equal {k : ℕ} {a b : M}
    (ha : NamedTermBound k a) (hb : NamedTermBound k b) :
    NamedFormulaBound k (modelNode 4 [a, b]) := by
  let := modelLinearOrder M
  obtain ⟨d, av, hd, hdk, hs⟩ := ha
  obtain ⟨e, bv, he, hek, ht⟩ := hb
  obtain ⟨hp, hq⟩ := bounded_join k ⟨hd, hdk⟩ ⟨he, hek⟩
  refine ⟨_, maximum.value ![maximum.value ![zeroValue M, av], bv], hp, hq, ?_⟩
  rw [stats_equal_modelNode_value]
  simp only [named_term_part hs, named_term_part ht, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    depth_ne_zero hd, depth_ne_zero he, false_or, ↓reduceIte, maximum_value, max_self]

theorem NamedFormulaBound.imp {k : ℕ} {a b : M}
    (ha : NamedFormulaBound k a) (hb : NamedFormulaBound k b) :
    NamedFormulaBound k (modelNode 6 [a, b]) := by
  let := modelLinearOrder M
  obtain ⟨d, av, hd, hdk, hs⟩ := ha
  obtain ⟨e, bv, he, hek, ht⟩ := hb
  obtain ⟨hp, hq⟩ := bounded_join k ⟨hd, hdk⟩ ⟨he, hek⟩
  refine ⟨_, maximum.value ![maximum.value ![zeroValue M, av], bv], hp, hq, ?_⟩
  rw [stats_imp_modelNode_value]
  simp only [named_formula_part hs, named_formula_part ht, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    depth_ne_zero hd, depth_ne_zero he, false_or, ↓reduceIte, maximum_value, max_self]

theorem NamedFormulaBound.all {k : ℕ} {a : M} (ha : NamedFormulaBound (k + 1) a) :
    NamedFormulaBound k (modelNode 7 [a]) := by
  let := modelLinearOrder M
  obtain ⟨d, av, hd, hdk, hs⟩ := ha
  obtain ⟨b, hdb⟩ := PAComputations.predecessor d (depth_ne_zero hd)
  have hb : leValue M b (numeralValue M (k + 1)) := by
    rw [hdb, numeral_value_succ] at hdk
    exact (successor_le_successor_value_iff _ _).mp hdk
  refine ⟨maximum.value ![numeralValue M 1, b], maximum.value ![zeroValue M, av], ?_, ?_, ?_⟩
  · rw [maximum_value]
    change numeralValue M 1 ≤ max (numeralValue M 1) b
    exact le_max_left _ _
  · rw [maximum_value]
    change max (numeralValue M 1) b ≤ numeralValue M (k + 1)
    exact max_le (numeral_le_model 1 _ (by omega)) hb
  · rw [stats_all_modelNode_value]
    simp only [named_formula_part hs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [ite_eq_right (depth_ne_zero hd)]
    simp only [maximum_value, max_eq_right (show numeralValue M 1 ≤ d from hd), max_self]
    rw [hdb, predecessor_successor]

theorem NamedFormulaBound.namedForm {k : ℕ} {a : M} (ha : NamedFormulaBound k a) :
    CheckerPrograms.namedForm.value ![numeralValue M k, a] = numeralValue M 1 := by
  obtain ⟨d, av, hd, hdk, hs⟩ := ha
  apply CheckerPrograms.namedForm_of_stats (numeralValue M k) a d av hs (depth_ne_zero hd)
  simpa only [numeral_value_succ] using hdk

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.FixedSyntaxPrograms
