import Lemmatheca.QuantifierFreeValidity.Formulas

/-! Naming the finitely many free variables and the actual quantified-sentence bridge. -/
namespace Lemmatheca.MathematicalLogic.QuantifierFreeValidity

open FirstOrder FirstOrder.Language

universe u v w a
variable {L : Language.{u, v}} {α : Type a}

/-- The library's actual free-variable-to-fresh-constant equivalence. -/
abbrev nameFormula (A : L.Formula α) : L[[α]].Sentence := Formula.equivSentence A

/-- A free-variable term becomes a ground term with fresh named constants. -/
def nameTerm (t : L.Term α) : L[[α]].Term Empty :=
  Term.varsToConstants (t.relabel Sum.inl)

theorem nameFormula_qf (A : L.Formula α) (hA : A.IsQF) : (nameFormula A).IsQF := by
  induction hA with
  | falsum => exact BoundedFormula.isQF_bot
  | of_isAtomic h =>
    cases h with
    | equal => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ihB ihC => exact ihB.imp ihC

theorem nameTerm_truth (t : L.Term α) (M : Type w) [L.Structure M] (a : α → M) :
    letI : (Language.constantsOn α).Structure M := Language.constantsOn.structure a
    (nameTerm t).realize Empty.elim = t.realize a := by
  let : (Language.constantsOn α).Structure M := Language.constantsOn.structure a
  have he : (fun i : α => (L.con i : M)) = a := rfl
  simp only [nameTerm, Term.realize_varsToConstants, Term.realize_relabel,
    Function.comp_def, Sum.elim_inl, he]

theorem nameFormula_reduct_truth (A : L.Formula α) (N : Type w) [L[[α]].Structure N] :
    letI : L.Structure N := (L.lhomWithConstants α).reduct N
    (nameFormula A).Realize N ↔ A.Realize (fun i => (L.con i : N)) := by
  let : L.Structure N := (L.lhomWithConstants α).reduct N
  exact Formula.realize_equivSentence N A

variable [DecidableEq α]

/-- Retain exactly the finite free-variable support before adding names. -/
def finiteRestriction (A : L.Formula α) : L.Formula A.freeVarFinset := A.restrictFreeVar id

def finiteNamed (A : L.Formula α) : L[[A.freeVarFinset]].Sentence := nameFormula (finiteRestriction A)

private theorem restrict_qf {β : Type w} {n : ℕ} {A : L.BoundedFormula α n}
    (hA : A.IsQF) (f : A.freeVarFinset → β) : (A.restrictFreeVar f).IsQF := by
  induction hA generalizing β with
  | falsum => exact BoundedFormula.isQF_bot
  | of_isAtomic h =>
    cases h with
    | equal => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ihB ihC => exact (ihB _).imp (ihC _)

theorem finiteRestriction_qf (A : L.Formula α) (hA : A.IsQF) : (finiteRestriction A).IsQF := by
  exact restrict_qf hA id

theorem finiteRestriction_truth (A : L.Formula α) (M : Type w) [L.Structure M]
    (a : α → M) :
    (finiteRestriction A).Realize (fun i => a i) ↔ A.Realize a := by
  exact BoundedFormula.realize_restrictFreeVar a (fun _ => rfl)

theorem finiteNamed_qf (A : L.Formula α) (hA : A.IsQF) : (finiteNamed A).IsQF := by
  exact nameFormula_qf _ (finiteRestriction_qf A hA)

/-- Universally quantify exactly the actual finite support in the shared formula syntax. -/
noncomputable def universalClosure (A : L.Formula α) : L.Sentence :=
  Formula.iAlls A.freeVarFinset (Formula.relabel Sum.inr (finiteRestriction A))

/-- The actual existential closure supplied by the shared syntax. -/
noncomputable abbrev existentialClosure (A : L.Formula α) : L.Sentence := A.exClosure

private def extendAssignment (A : L.Formula α) {M : Type w} [Inhabited M]
    (v : A.freeVarFinset → M) (i : α) : M :=
  if h : i ∈ A.freeVarFinset then v ⟨i, h⟩ else default

private theorem extension_truth (A : L.Formula α) (M : Type w) [L.Structure M] [Inhabited M]
    (v : A.freeVarFinset → M) :
    (finiteRestriction A).Realize v ↔ A.Realize (extendAssignment A v) := by
  apply BoundedFormula.realize_restrictFreeVar
  intro i
  simp [extendAssignment, i.property]

theorem universalClosure_truth (A : L.Formula α) (M : Type w) [L.Structure M] [Nonempty M] :
    (universalClosure A).Realize M ↔ ∀ a : α → M, A.Realize a := by
  classical
  let : Inhabited M := Classical.inhabited_of_nonempty (inferInstance : Nonempty M)
  have hu : (universalClosure A).Realize M ↔
      ∀ v : A.freeVarFinset → M, (finiteRestriction A).Realize v := by
    simp [universalClosure, Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel]
  rw [hu]
  constructor
  · intro h a
    exact (finiteRestriction_truth A M a).mp (h (fun i => a i))
  · intro h v
    exact (extension_truth A M v).mpr (h (extendAssignment A v))

theorem existentialClosure_truth (A : L.Formula α) (M : Type w) [L.Structure M] [Nonempty M] :
    (existentialClosure A).Realize M ↔ ∃ a : α → M, A.Realize a := by
  classical
  let : Inhabited M := Classical.inhabited_of_nonempty (inferInstance : Nonempty M)
  rw [existentialClosure, Formula.realize_exClosure]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨extendAssignment A v, (extension_truth A M v).mp hv⟩
  · rintro ⟨a, ha⟩
    exact ⟨fun i => a i, (finiteRestriction_truth A M a).mpr ha⟩

/-- Open a scoped matrix into finitely many free variables without changing its actual terms. -/
def matrixAsFormula {n : ℕ} (A : L.BoundedFormula Empty n) : L.Formula (Fin n) :=
  A.toFormula.relabel (Sum.elim Empty.elim id)

private theorem toFormula_qf {n : ℕ} {A : L.BoundedFormula Empty n} (hA : A.IsQF) :
    A.toFormula.IsQF := by
  induction hA with
  | falsum => exact BoundedFormula.isQF_bot
  | of_isAtomic h =>
    cases h with
    | equal => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ihB ihC => exact ihB.imp ihC

theorem matrixAsFormula_qf {n : ℕ} (A : L.BoundedFormula Empty n) (hA : A.IsQF) :
    (matrixAsFormula A).IsQF := by
  exact (toFormula_qf hA).relabel _

theorem matrixAsFormula_truth {n : ℕ} (A : L.BoundedFormula Empty n)
    (M : Type w) [L.Structure M] (a : Fin n → M) :
    (matrixAsFormula A).Realize a ↔ A.Realize Empty.elim a := by
  simp only [matrixAsFormula, Formula.realize_relabel, BoundedFormula.realize_toFormula,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr, id_eq]
  have he : (fun x : Empty => a x.elim) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [he]

theorem universal_matrix_truth {n : ℕ} (A : L.BoundedFormula Empty n)
    (M : Type w) [L.Structure M] :
    Sentence.Realize M A.alls ↔ ∀ a : Fin n → M, (matrixAsFormula A).Realize a := by
  change A.alls.Realize (default : Empty → M) ↔ _
  rw [BoundedFormula.realize_alls]
  apply forall_congr' fun a => ?_
  have hassign : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  simpa [hassign] using (matrixAsFormula_truth A M a).symm

theorem existential_matrix_truth {n : ℕ} (A : L.BoundedFormula Empty n)
    (M : Type w) [L.Structure M] :
    Sentence.Realize M A.exs ↔ ∃ a : Fin n → M, (matrixAsFormula A).Realize a := by
  change A.exs.Realize (default : Empty → M) ↔ _
  rw [BoundedFormula.realize_exs]
  apply exists_congr fun a => ?_
  have hassign : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  simpa [hassign] using (matrixAsFormula_truth A M a).symm

variable [∀ n, DecidableEq (L.Functions n)] [∀ n, DecidableEq (L.Relations n)]

instance namedFunctionsDecidableEq {β : Type a} [DecidableEq β] (n : ℕ) :
    DecidableEq (L[[β]].Functions n) := by
  change DecidableEq (L.Functions n ⊕ Language.constantsOnFunc β n)
  cases n with
  | zero => exact inferInstanceAs (DecidableEq (L.Functions 0 ⊕ β))
  | succ n => exact inferInstanceAs (DecidableEq (L.Functions (n + 1) ⊕ PEmpty.{a+1}))

instance namedRelationsDecidableEq {β : Type a} (n : ℕ) :
    DecidableEq (L[[β]].Relations n) := by
  change DecidableEq (L.Relations n ⊕ Empty)
  infer_instance

/-- Finite support naming followed by the executable ground row test. -/
def existentialTest (A : L.Formula α) : Bool := groundTest (finiteNamed A)

/-- Validity is the negation of satisfiability of the named negation. -/
def universalTest (A : L.Formula α) : Bool := !existentialTest A.not

def OpenHasModel (A : L.Formula α) : Prop :=
  ∃ (M : Type (max u a)) (inst : L.Structure M), Nonempty M ∧ ∃ a : α → M, @Formula.Realize L M inst α A a

theorem existentialTest_complete (A : L.Formula α) (hA : A.IsQF)
    (M : Type w) [L.Structure M] (a : α → M) (h : A.Realize a) :
    existentialTest A = true := by
  let : (Language.constantsOn A.freeVarFinset).Structure M :=
    Language.constantsOn.structure (fun i => a i)
  apply groundTest_complete (finiteNamed A) (finiteNamed_qf A hA) M
  have hr := (finiteRestriction_truth A M a).mpr h
  have he := Formula.realize_equivSentence_symm M (finiteNamed A) (fun i => a i)
  apply he.mp
  simpa [finiteNamed, nameFormula] using hr

/-- An accepted existential problem has the specified finite row model's reduct and witnesses. -/
theorem existentialTest_model (A : L.Formula α) (hA : A.IsQF)
    (h : existentialTest A = true) :
    ∃ r : Propositional.atoms (skeleton (finiteNamed A)) → Bool,
      let Γ := rowProblem (Propositional.atoms (skeleton (finiteNamed A)))
        (Propositional.extendRow _ r)
      letI := modelStructure Γ
      letI : L.Structure (Carrier Γ) :=
        (L.lhomWithConstants A.freeVarFinset).reduct (Carrier Γ)
      Propositional.eval (Propositional.extendRow _ r) (skeleton (finiteNamed A)) = true ∧
      literalTest Γ = true ∧
      ∃ a : α → Carrier Γ,
        (∀ i : A.freeVarFinset, a i = (L.con i : Carrier Γ)) ∧
        A.Realize a ∧ Finite (Carrier Γ) ∧
        Nat.card (Carrier Γ) ≤ (formulaSupport (finiteNamed A)).card + 1 := by
  classical
  obtain ⟨r, _hr, hb, hc⟩ := of_decide_eq_true h
  refine ⟨r, ?_⟩
  dsimp
  let Γ := rowProblem (Propositional.atoms (skeleton (finiteNamed A)))
    (Propositional.extendRow _ r)
  let : L[[A.freeVarFinset]].Structure (Carrier Γ) := modelStructure Γ
  let : L.Structure (Carrier Γ) := (L.lhomWithConstants A.freeVarFinset).reduct (Carrier Γ)
  have hm := passing_row_model (finiteNamed A) (finiteNamed_qf A hA) r hb hc
  have hr : (finiteRestriction A).Realize (fun i => (L.con i : Carrier Γ)) :=
    (nameFormula_reduct_truth (finiteRestriction A) (Carrier Γ)).mp hm.1
  let a : α → Carrier Γ := extendAssignment A (fun i => (L.con i : Carrier Γ))
  refine ⟨hb, hc, a, ?_, (extension_truth A (Carrier Γ) _).mp hr, hm.2.1, hm.2.2⟩
  intro i
  simp [a, extendAssignment, i.property]

theorem existentialTest_correct (A : L.Formula α) (hA : A.IsQF) :
    existentialTest A = true ↔ OpenHasModel A := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := existentialTest_model A hA h
    let Γ := rowProblem (Propositional.atoms (skeleton (finiteNamed A)))
      (Propositional.extendRow _ r)
    let : L[[A.freeVarFinset]].Structure (Carrier Γ) := modelStructure Γ
    let inst : L.Structure (Carrier Γ) := (L.lhomWithConstants A.freeVarFinset).reduct (Carrier Γ)
    obtain ⟨_hb, _hc, a, _hagree, ha, _hfinite, _hbound⟩ := hr
    exact ⟨Carrier Γ, inst, inferInstance, a, ha⟩
  · rintro ⟨M, inst, _hne, a, ha⟩
    let : L.Structure M := inst
    exact existentialTest_complete A hA M a ha

theorem existential_closure_correct (A : L.Formula α) (hA : A.IsQF) :
    existentialTest A = true ↔
      ∃ (M : Type (max u a)) (inst : L.Structure M), Nonempty M ∧
        @Sentence.Realize L M inst (existentialClosure A) := by
  rw [existentialTest_correct A hA]
  constructor
  · rintro ⟨M, inst, hne, a, ha⟩
    let : L.Structure M := inst
    let : Nonempty M := hne
    exact ⟨M, inst, hne, (existentialClosure_truth A M).mpr ⟨a, ha⟩⟩
  · rintro ⟨M, inst, hne, hM⟩
    let : L.Structure M := inst
    let : Nonempty M := hne
    exact ⟨M, inst, hne, (existentialClosure_truth A M).mp hM⟩

theorem universalTest_sound (A : L.Formula α) (hA : A.IsQF)
    (h : universalTest A = true) (M : Type w) [L.Structure M] (a : α → M) :
    A.Realize a := by
  classical
  by_contra hn
  have he := existentialTest_complete A.not hA.not M a hn
  simp [universalTest, he] at h

/-- A rejected validity claim has the reduct of its specified accepted row model as countermodel. -/
theorem universalTest_countermodel (A : L.Formula α) (hA : A.IsQF)
    (h : universalTest A = false) :
    ∃ r : Propositional.atoms (skeleton (finiteNamed A.not)) → Bool,
      let Γ := rowProblem (Propositional.atoms (skeleton (finiteNamed A.not)))
        (Propositional.extendRow _ r)
      letI := modelStructure Γ
      letI : L.Structure (Carrier Γ) :=
        (L.lhomWithConstants A.not.freeVarFinset).reduct (Carrier Γ)
      Propositional.eval (Propositional.extendRow _ r) (skeleton (finiteNamed A.not)) = true ∧
      literalTest Γ = true ∧
      ∃ a : α → Carrier Γ,
        (∀ i : A.not.freeVarFinset, a i = (L.con i : Carrier Γ)) ∧
        ¬A.Realize a ∧ Finite (Carrier Γ) ∧
        Nat.card (Carrier Γ) ≤ (formulaSupport (finiteNamed A.not)).card + 1 := by
  have he : existentialTest A.not = true := by
    simpa [universalTest] using h
  exact existentialTest_model A.not hA.not he

theorem universalTest_correct (A : L.Formula α) (hA : A.IsQF) :
    universalTest A = true ↔
      ∀ (M : Type (max u a)) (inst : L.Structure M), Nonempty M →
        @Sentence.Realize L M inst (universalClosure A) := by
  constructor
  · intro h M inst hne
    let : L.Structure M := inst
    let : Nonempty M := hne
    exact (universalClosure_truth A M).mpr (fun a => universalTest_sound A hA h M a)
  · intro h
    by_cases ht : universalTest A = true
    · exact ht
    · have hf : universalTest A = false := Bool.eq_false_iff.mpr ht
      obtain ⟨r, hr⟩ := universalTest_countermodel A hA hf
      let Γ := rowProblem (Propositional.atoms (skeleton (finiteNamed A.not)))
        (Propositional.extendRow _ r)
      let : L[[A.not.freeVarFinset]].Structure (Carrier Γ) := modelStructure Γ
      let inst : L.Structure (Carrier Γ) := (L.lhomWithConstants A.not.freeVarFinset).reduct (Carrier Γ)
      obtain ⟨_hb, _hc, a, _hagree, ha, _hfinite, _hbound⟩ := hr
      exact False.elim (ha ((universalClosure_truth A (Carrier Γ)).mp (h _ inst inferInstance) a))

/-- The algorithm also applies directly to the actual matrix of a universal prefix. -/
def universalMatrixTest {n : ℕ} (A : L.BoundedFormula Empty n) : Bool :=
  universalTest (matrixAsFormula A)

def existentialMatrixTest {n : ℕ} (A : L.BoundedFormula Empty n) : Bool :=
  existentialTest (matrixAsFormula A)

theorem universalMatrixTest_sound {n : ℕ} (A : L.BoundedFormula Empty n) (hA : A.IsQF)
    (h : universalMatrixTest A = true) (M : Type w) [L.Structure M] :
    Sentence.Realize M A.alls := by
  apply (universal_matrix_truth A M).mpr
  intro a
  exact universalTest_sound (matrixAsFormula A) (matrixAsFormula_qf A hA) h M a

theorem universalMatrixTest_correct {n : ℕ} (A : L.BoundedFormula Empty n) (hA : A.IsQF) :
    universalMatrixTest A = true ↔
      ∀ (M : Type u) (inst : L.Structure M), Nonempty M → @Sentence.Realize L M inst A.alls := by
  constructor
  · intro h M inst _hne
    let : L.Structure M := inst
    exact universalMatrixTest_sound A hA h M
  · intro h
    apply (universalTest_correct (matrixAsFormula A) (matrixAsFormula_qf A hA)).mpr
    intro M inst hne
    let : L.Structure M := inst
    let : Nonempty M := hne
    exact (universalClosure_truth (matrixAsFormula A) M).mpr
      ((universal_matrix_truth A M).mp (h M inst hne))

theorem existentialMatrixTest_correct {n : ℕ} (A : L.BoundedFormula Empty n) (hA : A.IsQF) :
    existentialMatrixTest A = true ↔ GroundHasModel A.exs := by
  change existentialTest (matrixAsFormula A) = true ↔ _
  rw [existentialTest_correct _ (matrixAsFormula_qf A hA)]
  constructor
  · rintro ⟨M, inst, hne, a, ha⟩
    let : L.Structure M := inst
    exact ⟨M, inst, hne, (existential_matrix_truth A M).mpr ⟨a, ha⟩⟩
  · rintro ⟨M, inst, hne, hM⟩
    let : L.Structure M := inst
    exact ⟨M, inst, hne, (existential_matrix_truth A M).mp hM⟩

end Lemmatheca.MathematicalLogic.QuantifierFreeValidity
