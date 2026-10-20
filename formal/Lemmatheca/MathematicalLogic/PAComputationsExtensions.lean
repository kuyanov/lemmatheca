import Lemmatheca.MathematicalLogic.PAComputations
import Mathlib.ModelTheory.Definability

/-! Actual function-symbol extensions of the shared PA language. -/
namespace Lemmatheca.MathematicalLogic.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open FirstOrderProofs
noncomputable section
universe u

def functionLanguage (n : ℕ) : Language :=
  ⟨fun k => PLift (k = n), fun _ => Empty⟩

def extendedLanguage (n : ℕ) : Language := language.sum (functionLanguage n)

def extensionMap (n : ℕ) : language →ᴸ extendedLanguage n := LHom.sumInl

def functionTerm {n : ℕ} {α : Type} (xs : Fin n → (extendedLanguage n).Term α) :
    (extendedLanguage n).Term α := .func (.inr ⟨rfl⟩) xs

def closeExtended {n : ℕ} {α : Type} [Fintype α]
    (φ : (extendedLanguage n).Formula α) : (extendedLanguage n).Sentence :=
  (φ.relabel (Sum.inr : α → Empty ⊕ α)).iAlls α

def graphDefinition {n : ℕ} (φ : language.Formula (Fin n ⊕ Unit)) :
    (extendedLanguage n).Sentence :=
  closeExtended (((extensionMap n).onFormula φ).subst
    (Sum.elim Term.var (fun _ => functionTerm Term.var)))

def extendedInduction {n k : ℕ}
    (φ : (extendedLanguage n).Formula (Fin k ⊕ Unit)) :
    (extendedLanguage n).Sentence :=
  let z := (extensionMap n).onTerm (zeroTerm : language.Term (Fin k))
  let s := (extensionMap n).onTerm
    (succTerm (.var (.inr ())) : language.Term (Fin k ⊕ Unit))
  closeExtended (((φ.subst (Sum.elim Term.var (fun _ => z))) ⊓
    ((φ.imp (φ.subst (Sum.elim (fun i => .var (.inl i))
      (fun _ => s)))).iAlls Unit)).imp (φ.iAlls Unit))

def graphExtension {n : ℕ} (φ : language.Formula (Fin n ⊕ Unit)) :
    (extendedLanguage n).Theory :=
  (extensionMap n).onTheory PA ∪ {graphDefinition φ} ∪
    {θ | ∃ k : ℕ, ∃ ψ : (extendedLanguage n).Formula (Fin k ⊕ Unit),
      θ = extendedInduction ψ}

private theorem model_total_unique {n : ℕ} (φ : language.Formula (Fin n ⊕ Unit))
    (hφ : Derives PA (totalUnique φ)) {M : Type u}
    [language.Structure M] [M ⊨ PA] (x : Fin n → M) :
    ∃! y : M, φ.Realize (extend x y) := by
  let : Nonempty M := ⟨zeroValue M⟩
  exact (realize_totalUnique φ).mp
    (derives_sound hφ default (fun B hB => Theory.realize_sentence_of_mem PA hB)) x

/-- The graph interpretation gives exactly one added function on every PA model. -/
theorem graph_function_unique {n : ℕ} (φ : language.Formula (Fin n ⊕ Unit))
    (hφ : Derives PA (totalUnique φ))
    {M : Type u} [language.Structure M] [M ⊨ PA] :
    ∃! f : (Fin n → M) → M, ∀ x, φ.Realize (extend x (f x)) := by
  let f (x : Fin n → M) : M := Classical.choose (model_total_unique φ hφ x)
  have hf (x : Fin n → M) : φ.Realize (extend x (f x)) :=
    (Classical.choose_spec (model_total_unique φ hφ x)).1
  refine ⟨f, hf, ?_⟩
  intro g hg
  funext x
  exact (Classical.choose_spec (model_total_unique φ hφ x)).2 (g x) (hg x)

@[instance_reducible] private def functionStructure {n : ℕ} {M : Type u}
    (f : (Fin n → M) → M) : (functionLanguage n).Structure M where
  funMap {k} h xs := by
    obtain ⟨h⟩ := h
    cases h
    exact f xs
  RelMap r _ := r.elim

private theorem function_definable {n : ℕ} {M : Type u} [language.Structure M]
    (φ : language.Formula (Fin n ⊕ Unit)) (f : (Fin n → M) → M)
    (hf : ∀ x y, φ.Realize (extend x y) ↔ y = f x) :
    (∅ : Set M).DefinableFun language f := by
  rw [Set.empty_definableFun_iff]
  refine ⟨φ.relabel (Sum.elim some (fun _ => none)), ?_⟩
  ext v
  simp only [Function.tupleGraph, Set.mem_ofPred_eq,
    Formula.realize_relabel]
  have he : v ∘ Sum.elim some (fun _ : Unit => none) = extend (v ∘ some) (v none) := by
    funext i
    cases i <;> rfl
  rw [he, hf]
  exact eq_comm

private theorem expanded_term_definable {n : ℕ} {M : Type u}
    [language.Structure M] (f : (Fin n → M) → M)
    (hf : (∅ : Set M).DefinableFun language f) {α : Type}
    (t : (extendedLanguage n).Term α) :
    letI := functionStructure f
    letI : (extendedLanguage n).Structure M := Language.sumStructure _ _ M
    (∅ : Set M).DefinableFun language t.realize := by
  let := functionStructure f
  let : (extendedLanguage n).Structure M := Language.sumStructure _ _ M
  induction t with
  | var i => exact language.definableFun_var i
  | @func k g ts ih =>
    cases g with
    | inl g =>
      change (∅ : Set M).DefinableFun language
        (fun v => Structure.funMap g (fun i => (ts i).realize v))
      exact (Set.DefinableFun.fun_symbol (L := language) g).comp ih
    | inr g =>
      obtain ⟨h⟩ := g
      cases h
      change (∅ : Set M).DefinableFun language (fun v => f (fun i => (ts i).realize v))
      exact hf.comp ih

private def bindingName {α : Type} (m : ℕ) :
    α ⊕ Fin (m + 1) → (α ⊕ Fin m) ⊕ Unit :=
  Sum.elim (Sum.inl ∘ Sum.inl)
    (Fin.lastCases (Sum.inr ()) (fun j => Sum.inl (Sum.inr j)))

private theorem bindingName_values {α : Type} {M : Type u} (m : ℕ)
    (v : α ⊕ Fin m → M) (u : Unit → M) :
    ((Sum.elim v u ∘ bindingName m) ∘ Sum.inl = v ∘ Sum.inl) ∧
    ((Sum.elim v u ∘ bindingName m) ∘ Sum.inr = Fin.snoc (v ∘ Sum.inr) (u ())) := by
  constructor
  · rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [bindingName]

private theorem expanded_formula_definable {n : ℕ} {M : Type u}
    [language.Structure M] (f : (Fin n → M) → M)
    (hf : (∅ : Set M).DefinableFun language f) {α : Type} {m : ℕ}
    (a : (extendedLanguage n).BoundedFormula α m) :
    letI := functionStructure f
    letI : (extendedLanguage n).Structure M := Language.sumStructure _ _ M
    (∅ : Set M).Definable language
      {v : α ⊕ Fin m → M | a.Realize (v ∘ Sum.inl) (v ∘ Sum.inr)} := by
  let := functionStructure f
  let : (extendedLanguage n).Structure M := Language.sumStructure _ _ M
  induction a with
  | falsum => simpa only [BoundedFormula.Realize, Set.ofPred_false] using
      (Set.definable_empty : (∅ : Set M).Definable language (∅ : Set ((α ⊕ Fin _ → M))))
  | equal s t =>
    have h := (expanded_term_definable f hf s).ofPred_eq (expanded_term_definable f hf t)
    convert h using 1
    ext v
    simp only [Set.mem_ofPred_eq, BoundedFormula.Realize]
    have hv : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) = v := by
      funext i
      cases i <;> rfl
    rw [hv]
  | rel r ts => cases r <;> contradiction
  | imp a b iha ihb =>
    convert iha.himp ihb using 1
    ext v
    rw [himp_eq]
    change (a.Realize (v ∘ Sum.inl) (v ∘ Sum.inr) →
      b.Realize (v ∘ Sum.inl) (v ∘ Sum.inr)) ↔
      (b.Realize (v ∘ Sum.inl) (v ∘ Sum.inr) ∨
        ¬ a.Realize (v ∘ Sum.inl) (v ∘ Sum.inr))
    tauto
  | @all m a ih =>
    have h := (ih.preimage_comp (bindingName m)).forall_of_finite
    convert h using 1
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · intro hx u
      simpa only [(bindingName_values m v u).1, (bindingName_values m v u).2] using hx (u ())
    · intro hx z
      simpa only [(bindingName_values m v (fun _ => z)).1,
        (bindingName_values m v (fun _ => z)).2] using hx (fun _ => z)

private theorem expanded_formula_arithmetic {n : ℕ} {M : Type u}
    [language.Structure M] (f : (Fin n → M) → M)
    (hf : (∅ : Set M).DefinableFun language f) {α : Type}
    (a : (extendedLanguage n).Formula α) :
    letI := functionStructure f
    letI : (extendedLanguage n).Structure M := Language.sumStructure _ _ M
    ∃ b : language.Formula α, ∀ v : α → M, a.Realize v ↔ b.Realize v := by
  let := functionStructure f
  let : (extendedLanguage n).Structure M := Language.sumStructure _ _ M
  have h := (expanded_formula_definable f hf a).preimage_comp
    (Sum.elim id (Fin.elim0 : Fin 0 → α))
  obtain ⟨b, hb⟩ := Set.empty_definable_iff.mp h
  refine ⟨b, ?_⟩
  intro v
  have he := Set.ext_iff.mp hb v
  change BoundedFormula.Realize a (fun x => v x)
    (fun i : Fin 0 => v (Fin.elim0 i)) ↔ b.Realize v at he
  simpa only [Formula.Realize, Subsingleton.elim
    (fun i : Fin 0 => v (Fin.elim0 i)) default] using he

private theorem realize_closeExtended {n : ℕ} {M : Type u}
    [(extendedLanguage n).Structure M] {α : Type} [Fintype α]
    (a : (extendedLanguage n).Formula α) :
    M ⊨ closeExtended a ↔ ∀ v : α → M, a.Realize v := by
  simp only [closeExtended, Sentence.Realize, Formula.realize_iAlls,
    Formula.realize_relabel, Function.comp_def, Sum.elim_inr]

private theorem realize_extendedInduction {n k : ℕ} {M : Type u}
    [language.Structure M] [(extendedLanguage n).Structure M]
    [(extensionMap n).IsExpansionOn M]
    (a : (extendedLanguage n).Formula (Fin k ⊕ Unit)) :
    M ⊨ extendedInduction a ↔ ∀ v : Fin k → M,
      (a.Realize (extend v (zeroValue M)) ∧
        ∀ y : M, a.Realize (extend v y) → a.Realize (extend v (succValue M y))) →
      ∀ y : M, a.Realize (extend v y) := by
  simp only [extendedInduction, realize_closeExtended, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_iAlls]
  have hunit (P : (Unit → M) → Prop) : (∀ u, P u) ↔ ∀ y : M, P (fun _ => y) := by
    constructor
    · intro h y
      exact h (fun _ => y)
    · intro h u
      have he : u = fun _ => u () := by funext i; cases i; rfl
      rw [he]
      exact h (u ())
  simp only [hunit]
  have hz (v : Fin k → M) :
      Formula.Realize (a.subst (Sum.elim Term.var (fun _ =>
        (extensionMap n).onTerm (zeroTerm : language.Term (Fin k))))) v ↔
      a.Realize (extend v (zeroValue M)) := by
    rw [Formula.Realize, BoundedFormula.realize_subst]
    change a.Realize _ ↔ a.Realize _
    have he : (fun i : Fin k ⊕ Unit =>
        (Sum.elim Term.var (fun _ =>
          (extensionMap n).onTerm (zeroTerm : language.Term (Fin k))) i).realize v) =
        extend v (zeroValue M) := by
      funext i
      cases i <;> simp [extend]
    rw [he]
  have hs (v : Fin k → M) (y : M) :
      Formula.Realize (a.subst (Sum.elim (fun i => .var (.inl i)) (fun _ =>
        (extensionMap n).onTerm
          (succTerm (.var (.inr ())) : language.Term (Fin k ⊕ Unit)))))
        (extend v y) ↔ a.Realize (extend v (succValue M y)) := by
    rw [Formula.Realize, BoundedFormula.realize_subst]
    change a.Realize _ ↔ a.Realize _
    have he : (fun i : Fin k ⊕ Unit =>
        (Sum.elim (fun j => Term.var (.inl j)) (fun _ =>
          (extensionMap n).onTerm
            (succTerm (.var (.inr ())) : language.Term (Fin k ⊕ Unit))) i).realize
              (extend v y)) = extend v (succValue M y) := by
      funext i
      cases i <;> simp [extend]
    rw [he]
  dsimp only [extend] at hz hs ⊢
  simp only [hz, hs]

/-- The conclusion concerns the actual extension language and includes all its
induction instances; the original arithmetic sentence is unchanged. -/
theorem graph_extension_conservative {n : ℕ}
    (φ : language.Formula (Fin n ⊕ Unit)) (hφ : Derives PA (totalUnique φ))
    (σ : language.Sentence)
    (hσ : Derives (graphExtension φ) ((extensionMap n).onSentence σ)) :
    Derives PA σ := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  obtain ⟨f, hf, _⟩ := graph_function_unique φ hφ (M := M)
  have hfun (x : Fin n → M) (y : M) : φ.Realize (extend x y) ↔ y = f x := by
    constructor
    · intro hy
      exact (model_total_unique φ hφ x).unique hy (hf x)
    · rintro rfl
      exact hf x
  have hd := function_definable φ f hfun
  let := functionStructure f
  let : (extendedLanguage n).Structure M := Language.sumStructure _ _ M
  let : (extensionMap n).IsExpansionOn M :=
    LHom.sumInl_isExpansionOn M
  have hdef : M ⊨ graphDefinition φ := by
    rw [graphDefinition, realize_closeExtended]
    intro x
    rw [Formula.Realize, BoundedFormula.realize_subst]
    change ((extensionMap n).onFormula φ).Realize _
    rw [LHom.realize_onFormula]
    convert hf x using 1
    funext i
    cases i <;> rfl
  have hind : M ⊨ ({θ | ∃ k : ℕ,
      ∃ a : (extendedLanguage n).Formula (Fin k ⊕ Unit), θ = extendedInduction a} :
        (extendedLanguage n).Theory) := by
    constructor
    rintro θ ⟨k, a, rfl⟩
    rw [realize_extendedInduction]
    intro v h
    obtain ⟨b, hb⟩ := expanded_formula_arithmetic f hd a
    intro y
    apply (hb _).mpr
    apply PA_induction M b v
    · exact (hb _).mp h.1
    · intro z hz
      exact (hb _).mp (h.2 z ((hb _).mpr hz))
  have hmodel : M ⊨ graphExtension φ := by
    apply Theory.Model.union
    · apply Theory.Model.union
      · exact (LHom.onTheory_model (extensionMap n) PA).mpr M.is_model
      · constructor
        rintro θ (rfl : θ = graphDefinition φ)
        exact hdef
    · exact hind
  have h := derives_sound hσ default (fun B hB => hmodel.realize_of_mem B hB)
  exact (LHom.realize_onSentence M (extensionMap n) σ).mp h

end
end Lemmatheca.MathematicalLogic.PAComputations
