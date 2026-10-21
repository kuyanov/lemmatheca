import Lemmatheca.DefinitionalExtensions.DefinitionalExtensions
import Mathlib.Tactic.FinCases

namespace Lemmatheca.Entry.DefinitionalExtensions
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.DefinitionalExtensions
open Lemmatheca.MathematicalLogic.FirstOrderProofs
noncomputable section

def functionLanguage (n : ℕ) : Language := ⟨fun k => PLift (k = n), fun _ => Empty⟩
def relationLanguage (n : ℕ) : Language := ⟨fun _ => Empty, fun k => PLift (k = n)⟩

def captureCorrect {L : Language} (E : L.Relations 2) : L.Formula Unit :=
  (E.formula ![.var (.inl ()), .var (.inr ())]).iExs Unit

def captureWrong {L : Language} (E : L.Relations 2) : L.Formula Unit :=
  (E.formula ![.var (.inr ()), .var (.inr ())]).iExs Unit

@[instance_reducible] def captureStructure : (relationLanguage 2).Structure Bool where
  funMap h := h.elim
  RelMap {n} h xs := by
    obtain ⟨h⟩ := h
    cases h
    exact xs 0 ≠ xs 1

theorem capture_counterexample :
    letI := captureStructure
    (∀ v : Unit → Bool, (captureCorrect (L := relationLanguage 2) ⟨rfl⟩).Realize v) ∧
      ∀ v : Unit → Bool, ¬ (captureWrong (L := relationLanguage 2) ⟨rfl⟩).Realize v := by
  constructor
  · intro v
    simp only [captureCorrect, Formula.realize_iExs]
    change ∃ w : Unit → Bool, v () ≠ w ()
    refine ⟨fun _ => !(v ()), ?_⟩
    cases v () <;> decide
  · intro v
    simp only [captureWrong, Formula.realize_iExs]
    change ¬ ∃ w : Unit → Bool, w () ≠ w ()
    simp

variable {L : Language}

def doublingPackage (plus : L.Functions 2) : DefinitionPackage L (functionLanguage 1) where
  functionGraph {n} h := by
    obtain ⟨h⟩ := h
    cases h
    exact (Term.var (.inr ())).equal
      (.func plus ![.var (.inl 0), .var (.inl 0)])
  relationFormula h := h.elim

def nestedDoubling (P : L.Relations 1) : (L.sum (functionLanguage 1)).Formula Unit :=
  Relations.formula (.inl P : (L.sum (functionLanguage 1)).Relations 1)
    (fun _ => .func (.inr ⟨rfl⟩) (fun _ =>
      .func (.inr ⟨rfl⟩) (fun _ => .var ())))

def nestedWitness (plus : L.Functions 2) (P : L.Relations 1) : L.Formula Unit :=
  let first : L.Formula ((Unit ⊕ Unit) ⊕ Unit) :=
    (Term.var (.inl (.inr ()))).equal
      (.func plus ![.var (.inl (.inl ())), .var (.inl (.inl ()))])
  let second : L.Formula ((Unit ⊕ Unit) ⊕ Unit) :=
    (Term.var (.inr ())).equal
      (.func plus ![.var (.inl (.inr ())), .var (.inl (.inr ()))])
  ((first ⊓ second ⊓ P.formula (fun _ => .var (.inr ()))).iExs Unit).iExs Unit

/-- A term equality graph is total and unique without background axioms. -/
theorem doubling_admissible (plus : L.Functions 2) :
    Admissible (doublingPackage plus) (∅ : L.Theory) := by
  intro n f
  obtain ⟨h⟩ := f
  cases h
  simp only [doublingPackage]
  apply Lemmatheca.MathematicalLogic.ChangingLanguages.deductive_completeness
  rw [Theory.models_sentence_iff]
  intro M
  rw [realize_totalUnique]
  intro x
  simp only [Formula.realize_equal, Term.realize_func]
  have ht (y : M) :
      (fun i => ((![.var (.inl 0), .var (.inl 0)] :
        Fin 2 → L.Term (Fin 1 ⊕ Unit)) i).realize (Sum.elim x (fun _ => y))) =
        ![x 0, x 0] := by
    funext i
    fin_cases i <;> rfl
  simp_rw [Term.realize_var, Sum.elim_inr, ht]
  exact existsUnique_eq

theorem nested_doubling_correct (plus : L.Functions 2) (P : L.Relations 1)
    {M : Type*} [L.Structure M] [(L.sum (functionLanguage 1)).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum (functionLanguage 1)).IsExpansionOn M]
    (h : M ⊨ (doublingPackage plus).definitions) (v : Unit → M) :
    (nestedDoubling P).Realize v ↔ (nestedWitness plus P).Realize v := by
  let p (a : M) : M := Structure.funMap plus ![a,a]
  let D (x : Fin 1 → M) : M :=
    @Structure.funMap (L.sum (functionLanguage 1)) M _ 1 (.inr ⟨rfl⟩) x
  have ht {β : Type} (a : β) (w : β → M) :
      (.func plus ![.var a,.var a] : L.Term β).realize w = p (w a) := by
    change Structure.funMap plus (fun i =>
      ((![.var a,.var a] : Fin 2 → L.Term β) i).realize w) = _
    congr 1
    funext i
    fin_cases i <;> rfl
  have hg := (doublingPackage plus).goodExpansion_iff_models.mpr h
  have hd (a : M) : D (fun _ => a) = p a := by
    have hh := (hg.1 1 ⟨rfl⟩ (fun _ => a) (D (fun _ => a))).mpr rfl
    change ((Term.var (.inr ())).equal
      (.func plus ![.var (.inl 0), .var (.inl 0)])).Realize
        (Sum.elim (fun _ : Fin 1 => a) (fun _ : Unit => D (fun _ => a))) at hh
    rw [Formula.realize_equal, ht] at hh
    exact hh
  have hw : (nestedWitness plus P).Realize v ↔
      Structure.RelMap P (fun _ => p (p (v ()))) := by
    simp only [nestedWitness, Formula.realize_iExs, Formula.realize_inf,
      Formula.realize_equal, Formula.realize_rel, ht, Term.realize_var,
      Sum.elim_inl, Sum.elim_inr]
    change (∃ u : Unit → M, ∃ w : Unit → M,
      (u () = p (v ()) ∧ w () = p (u ())) ∧ Structure.RelMap P (fun _ => w ())) ↔ _
    constructor
    · rintro ⟨u,w,⟨hu,hw⟩,hP⟩
      simpa only [hw,hu] using hP
    · intro hP
      exact ⟨fun _ => p (v ()), fun _ => p (p (v ())), ⟨rfl,rfl⟩, hP⟩
  rw [hw]
  change @Structure.RelMap (L.sum (functionLanguage 1)) M _ 1 (.inl P)
    (fun _ => D (fun _ => D (fun _ => v ()))) ↔ _
  apply (Iff.of_eq ((LHom.sumInl : L →ᴸ L.sum (functionLanguage 1)).map_onRelation P _)).trans
  simp only [hd]

/-- A proposed constant graph is either universally true or universally false. -/
def constantPackage (b : Bool) : DefinitionPackage Language.empty (functionLanguage 0) where
  functionGraph {n} h := by
    obtain ⟨h⟩ := h
    cases h
    exact if b then (Term.var (.inr ())).equal (.var (.inr ()))
      else ((Term.var (.inr ())).equal (.var (.inr ()))).not
  relationFormula h := h.elim

def singletonSentence : Language.empty.Sentence :=
  close ((Term.var false).equal (.var true) : Language.empty.Formula Bool)

theorem false_graph_not_total {M : Type*} [Nonempty M] [Language.empty.Structure M] :
    ¬ (∀ x : Fin 0 → M, ∃ y : M,
      ((constantPackage false).functionGraph ⟨rfl⟩).Realize (Sum.elim x (fun _ => y))) := by
  simp [constantPackage]

private theorem short_true_valid (M : Type*)
    [(Language.empty.sum (functionLanguage 0)).Structure M] :
    M ⊨ (constantPackage true).shortFunctionAxiom ⟨rfl⟩ := by
  let c : (Language.empty.sum (functionLanguage 0)).Term (Fin 0) :=
    .func (.inr ⟨rfl⟩) Term.var
  have he : (constantPackage true).shortFunctionAxiom ⟨rfl⟩ = close (c.equal c) := rfl
  rw [he, realize_close]
  intro x
  exact Formula.realize_equal.mpr rfl

private theorem short_false_impossible (M : Type*)
    [(Language.empty.sum (functionLanguage 0)).Structure M] :
    ¬ (M ⊨ (constantPackage false).shortFunctionAxiom ⟨rfl⟩) := by
  intro h
  let c : (Language.empty.sum (functionLanguage 0)).Term (Fin 0) :=
    .func (.inr ⟨rfl⟩) Term.var
  have he : (constantPackage false).shortFunctionAxiom ⟨rfl⟩ = close (c.equal c).not := rfl
  rw [he, realize_close] at h
  have hh := h Fin.elim0
  exact (Formula.realize_not.mp hh) (Formula.realize_equal.mpr rfl)

@[instance_reducible] private def constantStructure {M : Type*} (a : M) :
    (functionLanguage 0).Structure M where
  funMap _ _ := a
  RelMap r _ := r.elim

theorem false_graph_inconsistent :
    Derives (constantPackage false).definitions ⊥ ∧
      Derives ({(constantPackage false).shortFunctionAxiom ⟨rfl⟩} :
        (Language.empty.sum (functionLanguage 0)).Theory) ⊥ := by
  constructor
  · apply Lemmatheca.MathematicalLogic.ChangingLanguages.deductive_completeness
    rw [Theory.models_sentence_iff]
    intro M
    let : Language.empty.Structure M :=
      (LHom.sumInl : Language.empty →ᴸ Language.empty.sum (functionLanguage 0)).reduct M
    have hg := (constantPackage false).goodExpansion_iff_models.mpr M.is_model
    have hh := (hg.1 0 ⟨rfl⟩ Fin.elim0 _).mpr rfl
    simp [constantPackage] at hh
  · apply Lemmatheca.MathematicalLogic.ChangingLanguages.deductive_completeness
    rw [Theory.models_sentence_iff]
    intro M
    exact (short_false_impossible M
      (M.is_model.realize_of_mem _ (Set.mem_singleton _))).elim

theorem true_graph_total_not_unique {M : Type*} [Nontrivial M]
    [Language.empty.Structure M] :
    (∀ x : Fin 0 → M, ∃ y : M,
      ((constantPackage true).functionGraph ⟨rfl⟩).Realize (Sum.elim x (fun _ => y))) ∧
      ¬ (M ⊨ totalUnique ((constantPackage true).functionGraph ⟨rfl⟩)) := by
  constructor
  · intro x
    exact ⟨Classical.arbitrary M, by simp [constantPackage]⟩
  · rw [realize_totalUnique]
    intro h
    obtain ⟨a, b, hab⟩ := exists_pair_ne M
    obtain ⟨y, _, hy⟩ := h Fin.elim0
    exact hab ((hy a (by simp [constantPackage])).trans (hy b (by simp [constantPackage])).symm)

theorem true_graph_collapse :
    Derives (constantPackage true).definitions
      ((LHom.sumInl : Language.empty →ᴸ Language.empty.sum (functionLanguage 0)).onSentence
        singletonSentence) ∧ ¬ Derives (∅ : Language.empty.Theory) singletonSentence := by
  constructor
  · apply Lemmatheca.MathematicalLogic.ChangingLanguages.deductive_completeness
    rw [Theory.models_sentence_iff]
    intro M
    let : Language.empty.Structure M :=
      (LHom.sumInl : Language.empty →ᴸ Language.empty.sum (functionLanguage 0)).reduct M
    apply (LHom.realize_onSentence M
      (LHom.sumInl : Language.empty →ᴸ Language.empty.sum (functionLanguage 0)) _).mpr
    rw [singletonSentence, realize_close]
    intro x
    have hg := (constantPackage true).goodExpansion_iff_models.mpr M.is_model
    have he (y : M) : y = @Structure.funMap (Language.empty.sum (functionLanguage 0)) M _ 0
        (.inr ⟨rfl⟩) Fin.elim0 :=
      (hg.1 0 ⟨rfl⟩ Fin.elim0 y).mp (by simp [constantPackage])
    change x false = x true
    exact (he _).trans (he _).symm
  · intro hp
    let : Language.empty.Structure Bool := Language.emptyStructure
    have hh := derives_sound hp (M := Bool) default (by simp)
    have hh' : Bool ⊨ singletonSentence := by
      unfold Sentence.Realize
      convert hh using 1
    rw [singletonSentence, realize_close] at hh'
    have he := hh' (id : Bool → Bool)
    change false = true at he
    exact Bool.noConfusion he

theorem true_short_conservative (A : Language.empty.Sentence) :
    Derives ({(constantPackage true).shortFunctionAxiom ⟨rfl⟩} :
      (Language.empty.sum (functionLanguage 0)).Theory)
      ((LHom.sumInl : Language.empty →ᴸ Language.empty.sum (functionLanguage 0)).onSentence A) ↔
        Derives (∅ : Language.empty.Theory) A := by
  constructor
  · intro hp
    have hsem : (∅ : (Language.empty.sum (functionLanguage 0)).Theory) ⊨ᵇ
        (LHom.sumInl : Language.empty →ᴸ Language.empty.sum (functionLanguage 0)).onSentence A := by
      rw [Theory.models_sentence_iff]
      intro M
      exact derives_sound hp default (fun B hB => by
        obtain rfl := Set.mem_singleton_iff.mp hB
        exact short_true_valid M)
    have hnative := Lemmatheca.MathematicalLogic.ChangingLanguages.deductive_completeness hsem
    apply (Lemmatheca.MathematicalLogic.ChangingLanguages.derives_inclusion_iff
      (LHom.sumInl : Language.empty →ᴸ Language.empty.sum (functionLanguage 0))
      LHom.sumInl_injective).mp
    simpa only [LHom.onTheory, Set.image_empty] using hnative
  · intro hp
    have hnative := Lemmatheca.MathematicalLogic.ChangingLanguages.derives_map
      (LHom.sumInl : Language.empty →ᴸ Language.empty.sum (functionLanguage 0)) hp
    apply derives_mono hnative
    simp only [LHom.onTheory, Set.image_empty, Set.empty_subset]

def SatisfiesShort (S : (functionLanguage 0).Structure Bool) : Prop :=
  letI : Language.empty.Structure Bool := Language.emptyStructure
  letI := S
  letI : (Language.empty.sum (functionLanguage 0)).Structure Bool :=
    Language.sumStructure _ _ Bool
  Bool ⊨ (constantPackage true).shortFunctionAxiom ⟨rfl⟩

theorem true_short_two_expansions :
    ∃ S₁ S₂ : (functionLanguage 0).Structure Bool,
      S₁ ≠ S₂ ∧ SatisfiesShort S₁ ∧ SatisfiesShort S₂ := by
  refine ⟨constantStructure false, constantStructure true, ?_, ?_, ?_⟩
  · intro he
    have hh := congrArg (fun S : (functionLanguage 0).Structure Bool =>
      @Structure.funMap (functionLanguage 0) Bool S 0 ⟨rfl⟩ Fin.elim0) he
    exact Bool.noConfusion hh
  · let : Language.empty.Structure Bool := Language.emptyStructure
    let : (functionLanguage 0).Structure Bool := constantStructure false
    let : (Language.empty.sum (functionLanguage 0)).Structure Bool := Language.sumStructure _ _ Bool
    exact short_true_valid Bool
  · let : Language.empty.Structure Bool := Language.emptyStructure
    let : (functionLanguage 0).Structure Bool := constantStructure true
    let : (Language.empty.sum (functionLanguage 0)).Structure Bool := Language.sumStructure _ _ Bool
    exact short_true_valid Bool

end
end Lemmatheca.Entry.DefinitionalExtensions
