import Lemmatheca.MathematicalLogic.Theories
import Lemmatheca.MathematicalLogic.LargerModels
import Mathlib.Tactic

/-! Robinson arithmetic and full first-order induction in the shared syntax. -/
namespace Lemmatheca.MathematicalLogic.ArithmeticTheories
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
noncomputable section
universe u

inductive FunctionSymbol : ℕ → Type
  | zero : FunctionSymbol 0
  | succ : FunctionSymbol 1
  | add : FunctionSymbol 2
  | mul : FunctionSymbol 2
  deriving DecidableEq

def language : Language := ⟨FunctionSymbol, fun _ => Empty⟩
instance symbols_countable : Countable language.Symbols := by
  have : Countable (Σ n, FunctionSymbol n) := by
    apply Function.Injective.countable (f := fun p : Σ n, FunctionSymbol n =>
      match p with | ⟨_, .zero⟩ => (0 : ℕ) | ⟨_, .succ⟩ => 1
                   | ⟨_, .add⟩ => 2 | ⟨_, .mul⟩ => 3)
    intro a b h
    obtain ⟨_, a⟩ := a
    obtain ⟨_, b⟩ := b
    cases a <;> cases b <;> simp_all
  change Countable ((Σ n, FunctionSymbol n) ⊕ (Σ _ : ℕ, Empty))
  infer_instance

def zeroTerm {α : Type*} : language.Term α := .func .zero Fin.elim0
def succTerm {α : Type*} (t : language.Term α) : language.Term α := .func .succ (fun _ => t)
def addTerm {α : Type*} (s t : language.Term α) : language.Term α := .func .add ![s, t]
def mulTerm {α : Type*} (s t : language.Term α) : language.Term α := .func .mul ![s, t]
def numeral : ℕ → language.Term Empty
  | 0 => zeroTerm
  | n + 1 => succTerm (numeral n)

instance natStructure : language.Structure ℕ where
  funMap f ts := match f with
    | .zero => 0
    | .succ => ts 0 + 1
    | .add => ts 0 + ts 1
    | .mul => ts 0 * ts 1
  RelMap r _ := r.elim

variable (M : Type u) [language.Structure M]
def zeroValue : M := Structure.funMap (L := language) .zero Fin.elim0
def succValue (a : M) : M := Structure.funMap (L := language) .succ (fun _ => a)
def addValue (a b : M) : M := Structure.funMap (L := language) .add ![a, b]
def mulValue (a b : M) : M := Structure.funMap (L := language) .mul ![a, b]
def numeralValue (n : ℕ) : M := (numeral n).realize Empty.elim

@[simp] theorem realize_zeroTerm {α : Type*} (v : α → M) :
    (zeroTerm : language.Term α).realize v = zeroValue M := by
  change Structure.funMap _ _ = Structure.funMap _ _
  congr 1
  funext i
  exact i.elim0

@[simp] theorem realize_succTerm {α : Type*} (t : language.Term α) (v : α → M) :
    (succTerm t).realize v = succValue M (t.realize v) := rfl

@[simp] theorem realize_addTerm {α : Type*} (s t : language.Term α) (v : α → M) :
    (addTerm s t).realize v = addValue M (s.realize v) (t.realize v) := by
  change Structure.funMap _ _ = Structure.funMap _ _
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem realize_mulTerm {α : Type*} (s t : language.Term α) (v : α → M) :
    (mulTerm s t).realize v = mulValue M (s.realize v) (t.realize v) := by
  change Structure.funMap _ _ = Structure.funMap _ _
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem numeral_value_zero : numeralValue M 0 = zeroValue M := realize_zeroTerm M Empty.elim
@[simp] theorem numeral_value_succ (n : ℕ) :
    numeralValue M (n + 1) = succValue M (numeralValue M n) := rfl

theorem numeral_value_nat (n : ℕ) : numeralValue ℕ n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change numeralValue ℕ n + 1 = n + 1
    rw [ih]

/-- Universal closure over a displayed finite free-variable list. -/
def close {k : ℕ} (φ : language.Formula (Fin k)) : language.Sentence :=
  (BoundedFormula.relabel (fun i => (Sum.inr i : Empty ⊕ Fin k)) φ).alls

theorem realize_close {k : ℕ} (φ : language.Formula (Fin k)) :
    M ⊨ close φ ↔ ∀ a : Fin k → M, φ.Realize a := by
  simp only [close, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_relabel, Function.comp_def, Sum.elim_inr,
    Fin.castAdd_zero, Nat.add_zero, Fin.cast_eq_self]
  apply forall_congr'
  intro a
  unfold Formula.Realize
  rw [Subsingleton.elim (fun x : Fin 0 => a (Fin.natAdd k x)) default]

/-- Bind the displayed induction variable using the canonical single bound slot. -/
def allUnit {α : Type*} (φ : language.Formula (α ⊕ Unit)) : language.Formula α :=
  (BoundedFormula.relabel (Sum.elim Sum.inl (fun _ => Sum.inr (0 : Fin 1))) φ).all

theorem realize_allUnit {α : Type*} (φ : language.Formula (α ⊕ Unit)) (a : α → M) :
    (allUnit φ).Realize a ↔ ∀ b : M, φ.Realize (Sum.elim a (fun _ => b)) := by
  simp only [allUnit, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_relabel]
  apply forall_congr'
  intro b
  have hv : Sum.elim a ((Fin.snoc default b) ∘ Fin.castAdd 0) ∘
      Sum.elim Sum.inl (fun _ : Unit => Sum.inr (0 : Fin 1)) =
      Sum.elim a (fun _ : Unit => b) := by
    funext x
    cases x with
    | inl x => rfl
    | inr x =>
      change @Fin.snoc 0 (fun _ => M) default b (Fin.last 0) = b
      exact Fin.snoc_last _ _
  rw [hv]
  rw [Subsingleton.elim
    ((@Fin.snoc 0 (fun _ => M) default b) ∘ (Fin.natAdd 1 : Fin 0 → Fin 1))
    (default : Fin 0 → M)]

private def x : language.Term (Fin 1) := .var 0
private def x₂ : language.Term (Fin 2) := .var 0
private def y₂ : language.Term (Fin 2) := .var 1

def qSuccNeZero : language.Sentence := close ((succTerm x).equal zeroTerm).not
def qSuccInjective : language.Sentence :=
  close (((succTerm x₂).equal (succTerm y₂)).imp (x₂.equal y₂))
def qPredecessor : language.Sentence :=
  close ((x.equal zeroTerm).not.imp
    (((Term.var (.inl (0 : Fin 1))).equal (succTerm (.var (.inr ())))).iExs Unit))
def qAddZero : language.Sentence := close ((addTerm x zeroTerm).equal x)
def qAddSucc : language.Sentence :=
  close ((addTerm x₂ (succTerm y₂)).equal (succTerm (addTerm x₂ y₂)))
def qMulZero : language.Sentence := close ((mulTerm x zeroTerm).equal zeroTerm)
def qMulSucc : language.Sentence :=
  close ((mulTerm x₂ (succTerm y₂)).equal (addTerm (mulTerm x₂ y₂) x₂))

/-- Precisely the seven universally closed Robinson axioms. -/
def Q : language.Theory :=
  {qSuccNeZero, qSuccInjective, qPredecessor, qAddZero, qAddSucc, qMulZero, qMulSucc}

theorem model_Q_iff : M ⊨ Q ↔
    (∀ a : M, succValue M a ≠ zeroValue M) ∧ Function.Injective (succValue M) ∧
    (∀ a : M, a ≠ zeroValue M → ∃ b, a = succValue M b) ∧
    (∀ a : M, addValue M a (zeroValue M) = a) ∧
    (∀ a b : M, addValue M a (succValue M b) = succValue M (addValue M a b)) ∧
    (∀ a : M, mulValue M a (zeroValue M) = zeroValue M) ∧
    (∀ a b : M, mulValue M a (succValue M b) = addValue M (mulValue M a b) a) := by
  simp only [Q, Theory.model_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  simp only [qSuccNeZero, qSuccInjective, qPredecessor, qAddZero, qAddSucc,
    qMulZero, qMulSucc, realize_close]
  simp only [Formula.realize_not, Formula.realize_imp, Formula.realize_iExs,
    Formula.realize_equal, realize_zeroTerm, realize_succTerm, realize_addTerm,
    realize_mulTerm, x, x₂, y₂, Term.realize_var, Sum.elim_inl, Sum.elim_inr,
    Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Fin.cons_zero, Fin.cons_one,
    Function.Injective]
  have hex (a : M) : (∃ i : Unit → M, a = succValue M (i ())) ↔
      ∃ b : M, a = succValue M b :=
    ⟨fun ⟨i, hi⟩ => ⟨i (), hi⟩, fun ⟨b, hb⟩ => ⟨fun _ => b, hb⟩⟩
  simp only [hex]

theorem nat_models_Q : ℕ ⊨ Q := by
  rw [model_Q_iff]
  refine ⟨Nat.succ_ne_zero, Nat.succ_injective, ?_, Nat.add_zero, Nat.add_succ,
    Nat.mul_zero, Nat.mul_succ⟩
  intro a ha
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  exact ⟨b, rfl⟩

theorem numeral_add [M ⊨ Q] (m n : ℕ) :
    addValue M (numeralValue M m) (numeralValue M n) = numeralValue M (m + n) := by
  induction n with
  | zero => simpa using (model_Q_iff M).mp ‹M ⊨ Q› |>.2.2.2.1 (numeralValue M m)
  | succ n ih =>
    change addValue M (numeralValue M m) (succValue M (numeralValue M n)) =
      numeralValue M ((m + n) + 1)
    rw [numeral_value_succ]
    exact ((model_Q_iff M).mp ‹M ⊨ Q› |>.2.2.2.2.1
      (numeralValue M m) (numeralValue M n)).trans (congrArg (succValue M) ih)

theorem numeral_mul [M ⊨ Q] (m n : ℕ) :
    mulValue M (numeralValue M m) (numeralValue M n) = numeralValue M (m * n) := by
  induction n with
  | zero => simpa using (model_Q_iff M).mp ‹M ⊨ Q› |>.2.2.2.2.2.1 (numeralValue M m)
  | succ n ih =>
    rw [numeral_value_succ, (model_Q_iff M).mp ‹M ⊨ Q› |>.2.2.2.2.2.2,
      ih, numeral_add, Nat.mul_succ]

def closedTermValue (t : language.Term Empty) : ℕ := t.realize Empty.elim


theorem numeral_injective [M ⊨ Q] : Function.Injective (numeralValue M) := by
  intro m
  induction m with
  | zero =>
    intro n h
    cases n with
    | zero => rfl
    | succ n => exact False.elim ((model_Q_iff M).mp ‹M ⊨ Q› |>.1
        (numeralValue M n) (by simpa only [numeral_value_zero, numeral_value_succ] using h.symm))
  | succ m ih =>
    intro n h
    cases n with
    | zero => exact False.elim ((model_Q_iff M).mp ‹M ⊨ Q› |>.1
        (numeralValue M m) (by simpa only [numeral_value_zero, numeral_value_succ] using h))
    | succ n =>
      apply congrArg Nat.succ
      apply ih
      exact (model_Q_iff M).mp ‹M ⊨ Q› |>.2.1 h

theorem standard_embedding [M ⊨ Q] :
    ∃ e : ℕ ↪[language] M, ∀ n, e n = numeralValue M n := by
  refine ⟨{ toFun := numeralValue M
            inj' := numeral_injective M
            map_fun' := ?_
            map_rel' := ?_ }, fun _ => rfl⟩
  · intro n f ts
    cases f with
    | zero =>
      change numeralValue M 0 = Structure.funMap _ _
      rw [numeral_value_zero]
      change Structure.funMap _ _ = Structure.funMap _ _
      congr 1
      funext i
      exact i.elim0
    | succ =>
      change numeralValue M (ts 0 + 1) = Structure.funMap _ _
      rw [numeral_value_succ]
      change Structure.funMap _ _ = Structure.funMap _ _
      congr 1
      funext i
      fin_cases i
      rfl
    | add =>
      change numeralValue M (ts 0 + ts 1) = Structure.funMap _ _
      rw [← numeral_add]
      change Structure.funMap _ _ = Structure.funMap _ _
      congr 1
      funext i
      fin_cases i <;> rfl
    | mul =>
      change numeralValue M (ts 0 * ts 1) = Structure.funMap _ _
      rw [← numeral_mul]
      change Structure.funMap _ _ = Structure.funMap _ _
      congr 1
      funext i
      fin_cases i <;> rfl
  · intro n r
    exact r.elim

theorem closed_term_evaluation [M ⊨ Q] (t : language.Term Empty) :
    t.realize (M := M) Empty.elim = numeralValue M (closedTermValue t) := by
  obtain ⟨e, he⟩ := standard_embedding M
  have h := HomClass.realize_term e (t := t) (v := Empty.elim)
  have hv : e ∘ (Empty.elim : Empty → ℕ) = (Empty.elim : Empty → M) :=
    funext fun a => a.elim
  rw [hv, he] at h
  exact h


theorem Q_models_infinite [M ⊨ Q] : Infinite M := Infinite.of_injective _ (numeral_injective M)

def standardCopy : Set M := Set.range (numeralValue M)

theorem standard_copy_closed : zeroValue M ∈ standardCopy M ∧
    (∀ a ∈ standardCopy M, succValue M a ∈ standardCopy M) := by
  refine ⟨⟨0, numeral_value_zero M⟩, ?_⟩
  rintro a ⟨n, rfl⟩
  exact ⟨n + 1, numeral_value_succ M n⟩

theorem standard_copy_operations [M ⊨ Q] :
    (∀ a ∈ standardCopy M, ∀ b ∈ standardCopy M, addValue M a b ∈ standardCopy M) ∧
    (∀ a ∈ standardCopy M, ∀ b ∈ standardCopy M, mulValue M a b ∈ standardCopy M) := by
  constructor
  · rintro a ⟨m, rfl⟩ b ⟨n, rfl⟩
    exact ⟨m + n, (numeral_add M m n).symm⟩
  · rintro a ⟨m, rfl⟩ b ⟨n, rfl⟩
    exact ⟨m * n, (numeral_mul M m n).symm⟩

/-- Parameters stay free until the complete induction implication is closed. -/
def inductionAxiom {k : ℕ} (φ : language.Formula (Fin k ⊕ Unit)) : language.Sentence :=
  close (((φ.subst (Sum.elim Term.var (fun _ => zeroTerm))) ⊓
    (allUnit (φ.imp (φ.subst (Sum.elim (fun i => .var (.inl i))
      (fun _ => succTerm (.var (.inr ())))))))).imp (allUnit φ))

def inductionTheory : language.Theory :=
  {θ | ∃ k : ℕ, ∃ φ : language.Formula (Fin k ⊕ Unit), θ = inductionAxiom φ}

def PA : language.Theory := Q ∪ inductionTheory

theorem realize_induction_axiom {k : ℕ} (φ : language.Formula (Fin k ⊕ Unit)) :
    M ⊨ inductionAxiom φ ↔ ∀ a : Fin k → M,
      (φ.Realize (Sum.elim a (fun _ => zeroValue M)) ∧
        ∀ b : M, φ.Realize (Sum.elim a (fun _ => b)) →
          φ.Realize (Sum.elim a (fun _ => succValue M b))) →
      ∀ b : M, φ.Realize (Sum.elim a (fun _ => b)) := by
  simp only [inductionAxiom, realize_close, Formula.realize_imp, Formula.realize_inf,
    realize_allUnit]
  have hzero (a : Fin k → M) :
      Formula.Realize (φ.subst (Sum.elim Term.var (fun _ => zeroTerm))) a ↔
      φ.Realize (Sum.elim a (fun _ => zeroValue M)) := by
    rw [Formula.Realize, BoundedFormula.realize_subst]
    change φ.Realize _ ↔ φ.Realize _
    rw [iff_eq_eq]
    congr 1
    funext z
    cases z <;> simp
  have hsucc (a : Fin k → M) (b : M) :
      Formula.Realize (φ.subst (Sum.elim (fun i => .var (.inl i))
        (fun _ => succTerm (.var (.inr ()))))) (Sum.elim a (fun _ => b)) ↔
      φ.Realize (Sum.elim a (fun _ => succValue M b)) := by
    rw [Formula.Realize, BoundedFormula.realize_subst]
    change φ.Realize _ ↔ φ.Realize _
    rw [iff_eq_eq]
    congr 1
    funext z
    cases z <;> simp
  simp only [hzero, hsucc]

theorem PA_induction [M ⊨ PA] {k : ℕ} (φ : language.Formula (Fin k ⊕ Unit))
    (a : Fin k → M) (hzero : φ.Realize (Sum.elim a (fun _ => zeroValue M)))
    (hstep : ∀ b : M, φ.Realize (Sum.elim a (fun _ => b)) →
      φ.Realize (Sum.elim a (fun _ => succValue M b))) :
    ∀ b : M, φ.Realize (Sum.elim a (fun _ => b)) := by
  have hφ : inductionAxiom φ ∈ PA := Or.inr ⟨k, φ, rfl⟩
  exact (realize_induction_axiom M φ).mp
    ((‹M ⊨ PA›).realize_of_mem _ hφ) a ⟨hzero, hstep⟩

theorem PA_models_Q [M ⊨ PA] : M ⊨ Q := by
  exact (‹M ⊨ PA›).mono Set.subset_union_left

theorem nat_models_PA : ℕ ⊨ PA := by
  apply Theory.Model.union nat_models_Q
  constructor
  rintro θ ⟨k, φ, rfl⟩
  rw [realize_induction_axiom]
  intro a h b
  induction b with
  | zero => exact h.1
  | succ b ih => exact h.2 b ih

theorem Q_consistent : Consistent Q := by
  exact theory_consistent_of_model nat_models_Q

theorem PA_consistent : Consistent PA := by
  exact theory_consistent_of_model nat_models_PA

private theorem induct_formula [M ⊨ PA] {k : ℕ}
    (φ : language.Formula (Fin k ⊕ Unit)) (a : Fin k → M) (P : M → Prop)
    (hφ : ∀ b, φ.Realize (Sum.elim a (fun _ => b)) ↔ P b)
    (hz : P (zeroValue M)) (hs : ∀ b, P b → P (succValue M b)) : ∀ b, P b := by
  intro b
  apply (hφ b).mp
  exact PA_induction M φ a ((hφ _).mpr hz)
    (fun c hc => (hφ _).mpr (hs c ((hφ c).mp hc))) b

private theorem PA_model_zero_left [M ⊨ PA] (b : M) :
    addValue M (zeroValue M) b = b := by
  let φ : language.Formula (Fin 0 ⊕ Unit) :=
    (addTerm zeroTerm (.var (.inr ()))).equal (.var (.inr ()))
  have hφ (c : M) : φ.Realize (Sum.elim (Fin.elim0 : Fin 0 → M) (fun _ => c)) ↔
      addValue M (zeroValue M) c = c := by simp [φ]
  have hQ := (model_Q_iff M).mp (PA_models_Q M)
  apply induct_formula M φ Fin.elim0 _ hφ (hQ.2.2.2.1 _) _ b
  intro c hc
  exact (hQ.2.2.2.2.1 _ _).trans (congrArg (succValue M) hc)

private theorem PA_model_no_fixed [M ⊨ PA] (b : M) : succValue M b ≠ b := by
  let φ : language.Formula (Fin 0 ⊕ Unit) :=
    ((succTerm (.var (.inr ()))).equal (.var (.inr ()))).not
  have hφ (c : M) : φ.Realize (Sum.elim (Fin.elim0 : Fin 0 → M) (fun _ => c)) ↔
      succValue M c ≠ c := by simp [φ]
  have hQ := (model_Q_iff M).mp (PA_models_Q M)
  apply induct_formula M φ Fin.elim0 _ hφ (hQ.1 _) _ b
  intro c hc heq
  exact hc (hQ.2.1 heq)

private theorem PA_model_succ_add [M ⊨ PA] (a b : M) :
    addValue M (succValue M a) b = succValue M (addValue M a b) := by
  let φ : language.Formula (Fin 1 ⊕ Unit) :=
    (addTerm (succTerm (.var (.inl 0))) (.var (.inr ()))).equal
      (succTerm (addTerm (.var (.inl 0)) (.var (.inr ()))))
  have hφ (c : M) : φ.Realize (Sum.elim (fun _ : Fin 1 => a) (fun _ => c)) ↔
      addValue M (succValue M a) c = succValue M (addValue M a c) := by simp [φ]
  have hQ := (model_Q_iff M).mp (PA_models_Q M)
  apply induct_formula M φ (fun _ => a) _ hφ _ _ b
  · rw [hQ.2.2.2.1, hQ.2.2.2.1]
  · intro c hc
    exact (hQ.2.2.2.2.1 _ _).trans ((congrArg (succValue M) hc).trans
      (congrArg (succValue M) (hQ.2.2.2.2.1 _ _).symm))

private theorem PA_model_add_comm [M ⊨ PA] (a b : M) : addValue M a b = addValue M b a := by
  let φ : language.Formula (Fin 1 ⊕ Unit) :=
    (addTerm (.var (.inl 0)) (.var (.inr ()))).equal
      (addTerm (.var (.inr ())) (.var (.inl 0)))
  have hφ (c : M) : φ.Realize (Sum.elim (fun _ : Fin 1 => a) (fun _ => c)) ↔
      addValue M a c = addValue M c a := by simp [φ]
  have hQ := (model_Q_iff M).mp (PA_models_Q M)
  apply induct_formula M φ (fun _ => a) _ hφ _ _ b
  · exact (hQ.2.2.2.1 a).trans (PA_model_zero_left M a).symm
  · intro c hc
    exact (hQ.2.2.2.2.1 _ _).trans ((congrArg (succValue M) hc).trans
      (PA_model_succ_add M c a).symm)

theorem predecessor_from_induction : Derives inductionTheory qPredecessor := by
  apply HenkinCompleteness.consequence_iff_derives.mp
  apply Theory.models_sentence_iff.mpr
  intro N
  let φ : language.Formula (Fin 0 ⊕ Unit) :=
    ((Term.var (.inr ())).equal zeroTerm) ⊔
      (((Term.var (.inl (.inr ()))).equal (succTerm (.var (.inr ())))).iExs Unit)
  have hφ (b : N) : φ.Realize (Sum.elim (Fin.elim0 : Fin 0 → N) (fun _ => b)) ↔
      b = zeroValue N ∨ ∃ d : N, b = succValue N d := by
    simp only [φ, Formula.realize_sup, Formula.realize_equal, realize_zeroTerm,
      Term.realize_var, Sum.elim_inr, Formula.realize_iExs, realize_succTerm,
      Sum.elim_inl]
    constructor
    · rintro (h | ⟨i, hi⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i (), hi⟩
    · rintro (h | ⟨d, hd⟩)
      · exact Or.inl h
      · exact Or.inr ⟨fun _ => d, hd⟩
  have hi := (realize_induction_axiom N φ).mp
    (N.is_model.realize_of_mem (inductionAxiom φ) ⟨0, φ, rfl⟩) Fin.elim0
  have hall : ∀ b : N, b = zeroValue N ∨ ∃ d, b = succValue N d := by
    intro b
    exact (hφ b).mp (hi ⟨(hφ _).mpr (Or.inl rfl),
      fun c _ => (hφ _).mpr (Or.inr ⟨c, rfl⟩)⟩ b)
  rw [qPredecessor, realize_close]
  intro a
  simp only [Formula.realize_imp, Formula.realize_not, Formula.realize_equal,
    Formula.realize_iExs, x, Term.realize_var, realize_zeroTerm,
    realize_succTerm, Sum.elim_inl, Sum.elim_inr]
  intro hne
  obtain ⟨d, hd⟩ := (hall (a 0)).resolve_left hne
  exact ⟨fun _ => d, hd⟩

def zeroLeftSentence : language.Sentence := close ((addTerm zeroTerm x).equal x)
def noFixedPointSentence : language.Sentence := close ((succTerm x).equal x).not
def succAddSentence : language.Sentence :=
  close ((addTerm (succTerm x₂) y₂).equal (succTerm (addTerm x₂ y₂)))
def addCommSentence : language.Sentence := close ((addTerm x₂ y₂).equal (addTerm y₂ x₂))

theorem PA_zero_left : Derives PA zeroLeftSentence := by
  apply HenkinCompleteness.consequence_iff_derives.mp
  apply Theory.models_sentence_iff.mpr
  intro N
  rw [zeroLeftSentence, realize_close]
  intro a
  simpa [x, x₂, y₂] using PA_model_zero_left N (a 0)

theorem PA_no_fixed_point : Derives PA noFixedPointSentence := by
  apply HenkinCompleteness.consequence_iff_derives.mp
  apply Theory.models_sentence_iff.mpr
  intro N
  rw [noFixedPointSentence, realize_close]
  intro a
  simpa [x, x₂, y₂] using PA_model_no_fixed N (a 0)

theorem PA_succ_add : Derives PA succAddSentence := by
  apply HenkinCompleteness.consequence_iff_derives.mp
  apply Theory.models_sentence_iff.mpr
  intro N
  rw [succAddSentence, realize_close]
  intro a
  simpa [x, x₂, y₂] using PA_model_succ_add N (a 0) (a 1)

theorem PA_add_comm : Derives PA addCommSentence := by
  apply HenkinCompleteness.consequence_iff_derives.mp
  apply Theory.models_sentence_iff.mpr
  intro N
  rw [addCommSentence, realize_close]
  intro a
  simpa [x, x₂, y₂] using PA_model_add_comm N (a 0) (a 1)

def expandedLanguage : Language := language[[Unit]]
def expansionMap : language →ᴸ expandedLanguage := language.lhomWithConstants Unit
def freshConstant : expandedLanguage.Term Empty := .func (l := 0) (.inr ()) Fin.elim0

def avoidsNumeral (n : ℕ) : expandedLanguage.Sentence :=
  (freshConstant.equal (expansionMap.onTerm (numeral n))).not

def nonstandardTheory (T : language.Theory) : expandedLanguage.Theory :=
  expansionMap.onTheory T ∪ Set.range avoidsNumeral

@[simp] theorem realize_avoidsNumeral [expandedLanguage.Structure M]
    [expansionMap.IsExpansionOn M] (n : ℕ) :
    M ⊨ avoidsNumeral n ↔
      freshConstant.realize (M := M) Empty.elim ≠ numeralValue M n := by
  have hv : (default : Empty → M) = Empty.elim := funext fun a => a.elim
  simp only [avoidsNumeral, Sentence.Realize, Formula.realize_not,
    Formula.realize_equal, LHom.realize_onTerm, hv, numeralValue]

theorem nonstandard_theory_finitely_satisfiable (T : language.Theory) (hT : ℕ ⊨ T) :
    (nonstandardTheory T).IsFinitelySatisfiable := by
  classical
  intro Δ hΔ
  let pick (θ : expandedLanguage.Sentence) : ℕ :=
    if h : θ ∈ Set.range avoidsNumeral then Classical.choose h else 0
  let b : ℕ := Δ.sup pick + 1
  let : (constantsOn Unit).Structure ℕ := constantsOn.structure (fun _ => b)
  let : expandedLanguage.Structure ℕ := language.withConstantsStructure Unit
  let : expansionMap.IsExpansionOn ℕ := language.withConstants_expansion Unit
  have hmodel : ℕ ⊨ (↑Δ : expandedLanguage.Theory) := by
    constructor
    intro θ hθ
    rcases hΔ hθ with hbase | hconstraint
    · obtain ⟨ψ, hψ, rfl⟩ := hbase
      exact (expansionMap.realize_onSentence ℕ ψ).mpr (hT.realize_of_mem ψ hψ)
    · have hp : avoidsNumeral (pick θ) = θ := by
        dsimp only [pick]
        rw [dite_eq_left hconstraint]
        exact Classical.choose_spec hconstraint
      rw [← hp, realize_avoidsNumeral]
      have hc : freshConstant.realize (M := ℕ) Empty.elim = b := rfl
      rw [hc, numeral_value_nat]
      have hle : pick θ ≤ Δ.sup pick := Finset.le_sup hθ
      exact (Nat.lt_succ_of_le hle).ne'
  let := hmodel
  exact Theory.Model.isSatisfiable ℕ

theorem nonstandard_theory_satisfiable (T : language.Theory) (hT : ℕ ⊨ T) :
    (nonstandardTheory T).IsSatisfiable := by
  exact Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    (nonstandard_theory_finitely_satisfiable T hT)

theorem exists_nonstandard_of_nat_model (T : language.Theory) (hT : ℕ ⊨ T) :
    ∃ N : Theory.ModelType T, ∃ a : N, ∀ n : ℕ, a ≠ numeralValue N n := by
  obtain ⟨B₁⟩ := nonstandard_theory_satisfiable T hT
  let B := B₁.ulift
  let B₀ := B.subtheoryModel
    (Set.subset_union_left : expansionMap.onTheory T ⊆ nonstandardTheory T)
  let N := B₀.reduct expansionMap
  let : language.Structure B := expansionMap.reduct B
  refine ⟨N, freshConstant.realize (M := B) Empty.elim, ?_⟩
  intro n
  exact (realize_avoidsNumeral B n).mp
    (B.is_model.realize_of_mem _ (Or.inr ⟨n, rfl⟩))

theorem exists_nonstandard_PA :
    ∃ N : Theory.ModelType PA, ∃ a : N, ∀ n : ℕ, a ≠ numeralValue N n := by
  exact exists_nonstandard_of_nat_model PA nat_models_PA

theorem no_standard_isomorphism (a : M) (ha : ∀ n, a ≠ numeralValue M n) :
    ¬ Nonempty (ℕ ≃[language] M) := by
  rintro ⟨f⟩
  have hf (n : ℕ) : f n = numeralValue M n := by
    have h := HomClass.realize_term f (t := numeral n) (v := Empty.elim)
    have hv : f ∘ (Empty.elim : Empty → ℕ) = (Empty.elim : Empty → M) :=
      funext fun z => z.elim
    rw [hv] at h
    change numeralValue M n = f (numeralValue ℕ n) at h
    rw [numeral_value_nat] at h
    exact h.symm
  obtain ⟨n, hn⟩ := f.surjective a
  exact ha n (hn.symm.trans (hf n))

def trueArithmetic : language.Theory := language.completeTheory ℕ

theorem PA_subset_true_arithmetic : PA ⊆ trueArithmetic := by
  exact Theory.model_iff_subset_completeTheory.mp nat_models_PA

theorem exists_nonstandard_true_arithmetic :
    ∃ N : Theory.ModelType trueArithmetic, ∃ a : N, ∀ n : ℕ, a ≠ numeralValue N n := by
  exact exists_nonstandard_of_nat_model trueArithmetic (show ℕ ⊨ language.completeTheory ℕ from inferInstance)


def DefinesWithParameters {k : ℕ} (φ : language.Formula (Fin k ⊕ Unit))
    (a : Fin k → M) (A : Set M) : Prop :=
  ∀ b : M, φ.Realize (Sum.elim a (fun _ => b)) ↔ b ∈ A

theorem standard_copy_undefinable [M ⊨ PA] (h : standardCopy M ≠ Set.univ)
    {k : ℕ} (φ : language.Formula (Fin k ⊕ Unit)) (a : Fin k → M) :
    ¬ DefinesWithParameters M φ a (standardCopy M) := by
  intro hd
  apply h
  ext b
  simp only [Set.mem_univ, iff_true]
  apply (hd b).mp
  apply PA_induction M φ a
  · exact (hd (zeroValue M)).mpr (standard_copy_closed M).1
  · intro c hc
    exact (hd (succValue M c)).mpr ((standard_copy_closed M).2 c ((hd c).mp hc))

def FullSubsetInduction : Prop :=
  ∀ A : Set M, zeroValue M ∈ A → (∀ a ∈ A, succValue M a ∈ A) → A = Set.univ

theorem full_induction_standard_copy (h : FullSubsetInduction M) :
    standardCopy M = Set.univ := by
  exact h _ (standard_copy_closed M).1 (standard_copy_closed M).2


end
end Lemmatheca.MathematicalLogic.ArithmeticTheories
