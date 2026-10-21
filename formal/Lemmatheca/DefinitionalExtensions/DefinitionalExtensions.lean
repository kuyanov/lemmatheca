import Lemmatheca.DefinitionalExtensions.Support

/-! Explicit definitions and uniform elimination in the shared first-order syntax. -/
namespace Lemmatheca.MathematicalLogic.DefinitionalExtensions
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs

universe u v u' v' w z
noncomputable section
variable {L : Language.{u,v}} {K : Language.{u',v'}} {α : Type z}

/-- Old-language formulas assigned to all the new symbols. -/
structure DefinitionPackage (L : Language.{u,v}) (K : Language.{u',v'}) where
  functionGraph : ∀ {n}, K.Functions n → L.Formula (Fin n ⊕ Unit)
  relationFormula : ∀ {n}, K.Relations n → L.Formula (Fin n)

/-- Universal closure of a finite free-variable context. -/
def close {L : Language} {α : Type*} [Finite α] (A : L.Formula α) : L.Sentence :=
  (A.relabel (Sum.inr : α → Empty ⊕ α)).iAlls α

def totalUnique {n : ℕ} (A : L.Formula (Fin n ⊕ Unit)) : L.Sentence :=
  close (A.iExsUnique Unit)

/-- The native syntactic condition on the background theory. -/
def Admissible (d : DefinitionPackage L K) (T : L.Theory) : Prop :=
  ∀ n (f : K.Functions n), Derives T (totalUnique (d.functionGraph f))

/-- Conservativity concerns derivations in the existing native proof calculus. -/
def ConservativeAlong {J : Language} (j : L →ᴸ J) (T : L.Theory) (T' : J.Theory) : Prop :=
  ∀ A : L.Sentence, Derives T' (j.onSentence A) → Derives T A

namespace DefinitionPackage
variable (d : DefinitionPackage L K)

/-- The full biconditional graph axiom, including all input and output variables. -/
def functionAxiom {n : ℕ} (f : K.Functions n) : (L.sum K).Sentence :=
  close (((LHom.sumInl : L →ᴸ L.sum K).onFormula (d.functionGraph f)).iff
    ((Term.var (.inr ())).equal
      (.func (.inr f) (fun i => .var (.inl i)))))

def relationAxiom {n : ℕ} (R : K.Relations n) : (L.sum K).Sentence :=
  close ((Relations.formula (.inr R : (L.sum K).Relations n) Term.var).iff
    ((LHom.sumInl : L →ᴸ L.sum K).onFormula (d.relationFormula R)))

def definitions : (L.sum K).Theory :=
  {A | ∃ (n : ℕ) (f : K.Functions n), A = d.functionAxiom f} ∪
    {A | ∃ (n : ℕ) (R : K.Relations n), A = d.relationAxiom R}

def extension (T : L.Theory) : (L.sum K).Theory :=
  (LHom.sumInl : L →ᴸ L.sum K).onTheory T ∪ d.definitions

/-- The old equality graph or the given graph of a new symbol. -/
def symbolGraph {n : ℕ} : (L.sum K).Functions n → L.Formula (Fin n ⊕ Unit)
  | .inl f => (Term.var (.inr ())).equal (.func f (fun i => .var (.inl i)))
  | .inr f => d.functionGraph f

def symbolRelation {n : ℕ} : (L.sum K).Relations n → L.Formula (Fin n)
  | .inl R => R.formula Term.var
  | .inr R => d.relationFormula R

/-- The fresh tuple and output are disjoint sum tags, never raw variable names. -/
def termGraph (d : DefinitionPackage L K) : (L.sum K).Term α → L.Formula (α ⊕ Unit)
  | .var a => (Term.var (.inr ())).equal (.var (.inl a))
  | @Term.func _ _ n f ts =>
      ((Formula.iInf (fun i : Fin n =>
        (d.termGraph (ts i)).relabel (Sum.elim
          (fun a => Sum.inl (Sum.inl a)) (fun _ => Sum.inr i)))) ⊓
        (d.symbolGraph f).relabel
          (Sum.elim Sum.inr (fun _ => Sum.inl (Sum.inr ())))).iExs (Fin n)

def relationTranslation {n : ℕ} (R : (L.sum K).Relations n)
    (ts : Fin n → (L.sum K).Term α) : L.Formula α :=
  ((Formula.iInf (fun i : Fin n =>
    (d.termGraph (ts i)).relabel (Sum.elim Sum.inl (fun _ => Sum.inr i)))) ⊓
    (d.symbolRelation R).relabel Sum.inr).iExs (Fin n)

/-- Rebind the last available placeholder, keeping all earlier inputs separate. -/
def bindLast {α : Type*} (n : ℕ) : α ⊕ Fin (n+1) → (α ⊕ Fin n) ⊕ Unit :=
  Sum.elim (Sum.inl ∘ Sum.inl)
    (Fin.lastCases (Sum.inr ()) (fun i => Sum.inl (Sum.inr i)))

/-- Every available placeholder is an input until its original binder is rebuilt. -/
def translateAux (d : DefinitionPackage L K) : {n : ℕ} → (L.sum K).BoundedFormula α n → L.Formula (α ⊕ Fin n)
  | _, .falsum => ⊥
  | _, .equal s t => (d.termGraph s ⊓ d.termGraph t).iExs Unit
  | _, .rel R ts => d.relationTranslation R ts
  | _, .imp A B => (d.translateAux A).imp (d.translateAux B)
  | n, .all A => ((d.translateAux A).relabel (bindLast n)).iAlls Unit

def translate (A : (L.sum K).Formula α) : L.Formula α :=
  (d.translateAux A).relabel (Sum.elim id Fin.elim0)

def translateSentence (A : (L.sum K).Sentence) : L.Sentence := d.translate A

/-- Direct relation replacement when no function symbols have been added. -/
def oldTerm [∀ n, IsEmpty (K.Functions n)] : (L.sum K).Term α → L.Term α
  | .var a => .var a
  | .func (.inl f) ts => .func f (fun i => oldTerm (ts i))
  | .func (.inr f) _ => isEmptyElim f

def relationOnlyAux (d : DefinitionPackage L K) [∀ n, IsEmpty (K.Functions n)] :
    {n : ℕ} → (L.sum K).BoundedFormula α n → L.Formula (α ⊕ Fin n)
  | _, .falsum => ⊥
  | _, .equal s t => (oldTerm s).equal (oldTerm t)
  | _, .rel R ts => (d.symbolRelation R).subst (fun i => oldTerm (ts i))
  | _, .imp A B => (d.relationOnlyAux A).imp (d.relationOnlyAux B)
  | n, .all A => ((d.relationOnlyAux A).relabel (bindLast n)).iAlls Unit

def relationOnly [∀ n, IsEmpty (K.Functions n)]
    (A : (L.sum K).Formula α) : L.Formula α :=
  (d.relationOnlyAux A).relabel (Sum.elim id Fin.elim0)

/-- Conditions on the actual expanded symbol interpretations. -/
def GoodExpansion (M : Type w) [L.Structure M] [(L.sum K).Structure M] : Prop :=
  (∀ n (f : K.Functions n) (x : Fin n → M) (y : M),
    (d.functionGraph f).Realize (Sum.elim x (fun _ => y)) ↔
      y = @Structure.funMap (L.sum K) M _ n (.inr f) x) ∧
  (∀ n (R : K.Relations n) (x : Fin n → M),
    @Structure.RelMap (L.sum K) M _ n (.inr R) x ↔ (d.relationFormula R).Realize x)

/-- On a fixed old structure, the extra structure is exactly the new interpretations. -/
def IsDefinedExpansion (M : Type w) [L.Structure M] (S : K.Structure M) : Prop :=
  letI := S
  letI : (L.sum K).Structure M := Language.sumStructure L K M
  M ⊨ d.definitions

end DefinitionPackage

variable {M : Type w} [L.Structure M]

theorem realize_close {α : Type*} [Finite α] (A : L.Formula α) :
    M ⊨ close A ↔ ∀ v : α → M, A.Realize v := by
  simp only [close, Sentence.Realize, Formula.realize_iAlls,
    Formula.realize_relabel, Function.comp_def, Sum.elim_inr]

theorem realize_totalUnique {n : ℕ} (A : L.Formula (Fin n ⊕ Unit)) :
    M ⊨ totalUnique A ↔ ∀ x : Fin n → M, ∃! y : M,
      A.Realize (Sum.elim x (fun _ => y)) := by
  rw [totalUnique, realize_close]
  simp only [Formula.realize_iExsUnique]
  constructor
  · intro h x
    obtain ⟨y, hy, hu⟩ := h x
    refine ⟨y (), ?_, ?_⟩
    · simpa only [show (fun _ : Unit => y ()) = y by funext i; cases i; rfl] using hy
    · intro z hz
      have he := congrFun (hu (fun _ => z) hz) ()
      exact he
  · intro h x
    obtain ⟨y, hy, hu⟩ := h x
    refine ⟨fun _ => y, hy, ?_⟩
    intro z hz
    funext i
    cases i
    apply hu (z ())
    convert hz using 1

namespace DefinitionPackage
variable (d : DefinitionPackage L K)

private theorem realize_functionAxiom {n : ℕ} (f : K.Functions n)
    [(L.sum K).Structure M] [(LHom.sumInl : L →ᴸ L.sum K).IsExpansionOn M] :
    M ⊨ d.functionAxiom f ↔ ∀ x : Fin n → M, ∀ y : M,
      (d.functionGraph f).Realize (Sum.elim x (fun _ => y)) ↔
        y = @Structure.funMap (L.sum K) M _ n (.inr f) x := by
  simp only [functionAxiom, realize_close, Formula.realize_iff,
    LHom.realize_onFormula, Formula.realize_equal, Term.realize_var]
  dsimp only [Term.realize]
  constructor
  · intro h x y
    exact h (Sum.elim x (fun _ => y))
  · intro h v
    have hv : Sum.elim (fun i => v (.inl i)) (fun _ : Unit => v (.inr ())) = v := by
      funext a
      cases a with
      | inl i => rfl
      | inr i => cases i; rfl
    simpa only [hv] using h (fun i => v (.inl i)) (v (.inr ()))

private theorem realize_relationAxiom {n : ℕ} (R : K.Relations n)
    [(L.sum K).Structure M] [(LHom.sumInl : L →ᴸ L.sum K).IsExpansionOn M] :
    M ⊨ d.relationAxiom R ↔ ∀ x : Fin n → M,
      @Structure.RelMap (L.sum K) M _ n (.inr R) x ↔ (d.relationFormula R).Realize x := by
  simp only [relationAxiom, realize_close, Formula.realize_iff, LHom.realize_onFormula]
  dsimp only [Relations.formula, Relations.boundedFormula, Formula.Realize,
    BoundedFormula.Realize, Term.relabel, Term.realize]
  rfl

theorem goodExpansion_iff_models [(L.sum K).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum K).IsExpansionOn M] :
    d.GoodExpansion M ↔ M ⊨ d.definitions := by
  constructor
  · intro h
    constructor
    rintro A (⟨n,f,rfl⟩ | ⟨n,R,rfl⟩)
    · exact (realize_functionAxiom d f).mpr (h.1 n f)
    · exact (realize_relationAxiom d R).mpr (h.2 n R)
  · intro h
    constructor
    · intro n f
      exact (realize_functionAxiom d f).mp
        (h.realize_of_mem _ (Or.inl ⟨n,f,rfl⟩))
    · intro n R
      exact (realize_relationAxiom d R).mp
        (h.realize_of_mem _ (Or.inr ⟨n,R,rfl⟩))

/-- Actual existence and uniqueness of every new symbol interpretation. -/
theorem unique_expansion (T : L.Theory) (hd : Admissible d T) [Nonempty M] [M ⊨ T] :
    ∃! S : K.Structure M, d.IsDefinedExpansion M S := by
  have ht (n : ℕ) (f : K.Functions n) (x : Fin n → M) :
      ∃! y : M, (d.functionGraph f).Realize (Sum.elim x (fun _ => y)) :=
    (realize_totalUnique _).mp
      (derives_sound (hd n f) default (fun A hA => Theory.realize_sentence_of_mem T hA)) x
  let S : K.Structure M :=
    ⟨fun {n} f x => Classical.choose (ht n f x), fun {n} R x => (d.relationFormula R).Realize x⟩
  have hs : d.IsDefinedExpansion M S := by
    let := S
    let : (L.sum K).Structure M := Language.sumStructure L K M
    apply (d.goodExpansion_iff_models).mp
    constructor
    · intro n f x y
      change (d.functionGraph f).Realize (Sum.elim x (fun _ => y)) ↔
        y = Classical.choose (ht n f x)
      exact ⟨fun hy => (Classical.choose_spec (ht n f x)).2 y hy,
        fun hy => hy ▸ (Classical.choose_spec (ht n f x)).1⟩
    · intro n R x
      exact Iff.rfl
  refine ⟨S, hs, ?_⟩
  intro S' hS'
  let := S'
  let : (L.sum K).Structure M := Language.sumStructure L K M
  have hg := (d.goodExpansion_iff_models).mpr hS'
  apply Structure.ext
  · funext n f x
    apply (Classical.choose_spec (ht n f x)).2
    exact (hg.1 n f x _).mpr rfl
  · funext n R x
    exact propext (hg.2 n R x)


private theorem realize_symbolGraph [(L.sum K).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum K).IsExpansionOn M]
    (h : d.GoodExpansion M) {n : ℕ} (f : (L.sum K).Functions n)
    (x : Fin n → M) (y : M) :
    (d.symbolGraph f).Realize (Sum.elim x (fun _ => y)) ↔
      y = @Structure.funMap (L.sum K) M _ n f x := by
  cases f with
  | inl f => simp [symbolGraph, LHom.funMap_sumInl]
  | inr f => exact h.1 n f x y

private theorem realize_symbolRelation [(L.sum K).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum K).IsExpansionOn M]
    (h : d.GoodExpansion M) {n : ℕ} (R : (L.sum K).Relations n) (x : Fin n → M) :
    (d.symbolRelation R).Realize x ↔ @Structure.RelMap (L.sum K) M _ n R x := by
  cases R with
  | inl R =>
    simp only [symbolRelation, Formula.realize_rel, Term.realize_var]
    exact Iff.of_eq ((LHom.sumInl : L →ᴸ L.sum K).map_onRelation R x).symm
  | inr R => exact (h.2 n R x).symm

private theorem child_values {α : Type*} {M : Type*} {n : ℕ}
    (v : α → M) (y : M) (x : Fin n → M) (i : Fin n) :
    Sum.elim (Sum.elim v (fun _ : Unit => y)) x ∘
      Sum.elim (fun a => Sum.inl (Sum.inl a)) (fun _ : Unit => Sum.inr i) =
        Sum.elim v (fun _ : Unit => x i) := by
  funext a
  cases a <;> rfl

private theorem graph_values {α : Type*} {M : Type*} {n : ℕ}
    (v : α → M) (y : M) (x : Fin n → M) :
    Sum.elim (Sum.elim v (fun _ : Unit => y)) x ∘
      Sum.elim Sum.inr (fun _ : Unit => Sum.inl (Sum.inr ())) =
        Sum.elim x (fun _ : Unit => y) := by
  funext a
  cases a with
  | inl i => rfl
  | inr i => cases i; rfl

/-- Correctness includes all parameters and output values of the specified recurrence. -/
theorem realize_termGraph [(L.sum K).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum K).IsExpansionOn M]
    (h : d.GoodExpansion M) (t : (L.sum K).Term α) (v : α → M) (y : M) :
    (d.termGraph t).Realize (Sum.elim v (fun _ => y)) ↔ y = t.realize v := by
  induction t generalizing y with
  | var a => simp [termGraph]
  | @func n f ts ih =>
    simp only [termGraph, Formula.realize_iExs, Formula.realize_inf,
      Formula.realize_iInf, Formula.realize_relabel, child_values, graph_values]
    dsimp only [Term.realize]
    change (∃ x : Fin n → M,
      (∀ i, (d.termGraph (ts i)).Realize (Sum.elim v (fun _ => x i))) ∧
        (d.symbolGraph f).Realize (Sum.elim x (fun _ => y))) ↔
      y = @Structure.funMap (L.sum K) M _ n f (fun i => (ts i).realize v)
    simp_rw [ih, realize_symbolGraph d h]
    constructor
    · rintro ⟨x, hx, hy⟩
      have he : x = fun i => (ts i).realize v := funext hx
      simpa only [he] using hy
    · intro hy
      exact ⟨fun i => (ts i).realize v, fun _ => rfl, hy⟩

private theorem realize_graph_at [(L.sum K).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum K).IsExpansionOn M]
    (h : d.GoodExpansion M) (t : (L.sum K).Term α) (w : α ⊕ Unit → M) :
    (d.termGraph t).Realize w ↔ w (.inr ()) = t.realize (w ∘ Sum.inl) := by
  have hw : Sum.elim (w ∘ Sum.inl) (fun _ : Unit => w (.inr ())) = w := by
    funext a
    cases a with
    | inl i => rfl
    | inr i => cases i; rfl
  simpa only [hw] using d.realize_termGraph h t (w ∘ Sum.inl) (w (.inr ()))

private theorem tuple_child_values {α : Type*} {M : Type*} {n : ℕ}
    (v : α → M) (x : Fin n → M) (i : Fin n) :
    Sum.elim v x ∘ Sum.elim Sum.inl (fun _ : Unit => Sum.inr i) =
        Sum.elim v (fun _ : Unit => x i) := by
  funext a
  cases a <;> rfl

private theorem realize_relationTranslation [(L.sum K).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum K).IsExpansionOn M]
    (h : d.GoodExpansion M) {n : ℕ} (R : (L.sum K).Relations n)
    (ts : Fin n → (L.sum K).Term α) (v : α → M) :
    (d.relationTranslation R ts).Realize v ↔
      @Structure.RelMap (L.sum K) M _ n R (fun i => (ts i).realize v) := by
  simp only [relationTranslation, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_relabel, tuple_child_values, Sum.elim_comp_inr]
  simp_rw [realize_termGraph d h, realize_symbolRelation d h]
  constructor
  · rintro ⟨x, hx, hy⟩
    have he : x = fun i => (ts i).realize v := funext hx
    simpa only [he] using hy
  · intro hy
    exact ⟨fun i => (ts i).realize v, fun _ => rfl, hy⟩

private theorem bindLast_values {α : Type*} {M : Type*} (n : ℕ)
    (v : α → M) (xs : Fin n → M) (y : Unit → M) :
    Sum.elim (Sum.elim v xs) y ∘ bindLast n = Sum.elim v (Fin.snoc xs (y ())) := by
  funext a
  cases a with
  | inl i => rfl
  | inr i => refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [bindLast]

theorem realize_translateAux [(L.sum K).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum K).IsExpansionOn M]
    (h : d.GoodExpansion M) {n : ℕ} (A : (L.sum K).BoundedFormula α n)
    (v : α → M) (xs : Fin n → M) :
    (d.translateAux A).Realize (Sum.elim v xs) ↔ A.Realize v xs := by
  induction A with
  | falsum => rfl
  | equal s t =>
    simp only [translateAux, Formula.realize_iExs, Formula.realize_inf,
      realize_graph_at d h, Sum.elim_comp_inl, Sum.elim_inr]
    change (∃ u : Unit → M, u () = s.realize (Sum.elim v xs) ∧
      u () = t.realize (Sum.elim v xs)) ↔
      s.realize (Sum.elim v xs) = t.realize (Sum.elim v xs)
    constructor
    · rintro ⟨u,hs,ht⟩
      exact hs.symm.trans ht
    · intro he
      exact ⟨fun _ => s.realize (Sum.elim v xs), rfl, he⟩
  | rel R ts => exact realize_relationTranslation d h R ts _
  | imp A B ihA ihB =>
    simp only [translateAux, Formula.realize_imp, BoundedFormula.Realize, ihA, ihB]
  | @all n A ih =>
    simp only [translateAux, Formula.realize_iAlls, Formula.realize_relabel, bindLast_values]
    change (∀ y : Unit → M, (d.translateAux A).Realize
      (Sum.elim v (Fin.snoc xs (y ())))) ↔ ∀ y : M, A.Realize v (Fin.snoc xs y)
    simp_rw [ih]
    exact ⟨fun h y => h (fun _ => y), fun h y => h (y ())⟩

theorem realize_translate [(L.sum K).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum K).IsExpansionOn M]
    (h : d.GoodExpansion M) (A : (L.sum K).Formula α) (v : α → M) :
    (d.translate A).Realize v ↔ A.Realize v := by
  rw [translate, Formula.realize_relabel]
  have hv : v ∘ Sum.elim id (Fin.elim0 : Fin 0 → α) = Sum.elim v default := by
    funext a
    cases a with
    | inl i => rfl
    | inr i => exact i.elim0
  rw [hv]
  exact d.realize_translateAux h A v default

private theorem oldTerm_realize [∀ n, IsEmpty (K.Functions n)]
    [(L.sum K).Structure M] [(LHom.sumInl : L →ᴸ L.sum K).IsExpansionOn M]
    (t : (L.sum K).Term α) (v : α → M) : (oldTerm t).realize v = t.realize v := by
  induction t with
  | var a => rfl
  | @func n f ts ih =>
    cases f with
    | inl f =>
      change Structure.funMap f (fun i => (oldTerm (ts i)).realize v) =
        @Structure.funMap (L.sum K) M _ n (.inl f) (fun i => (ts i).realize v)
      calc
        _ = Structure.funMap f (fun i => (ts i).realize v) := congrArg _ (funext ih)
        _ = _ := ((LHom.sumInl : L →ᴸ L.sum K).map_onFunction f _).symm
    | inr f => exact isEmptyElim f

private theorem realize_relationOnlyAux [∀ n, IsEmpty (K.Functions n)]
    [(L.sum K).Structure M] [(LHom.sumInl : L →ᴸ L.sum K).IsExpansionOn M]
    (h : d.GoodExpansion M) {n : ℕ} (A : (L.sum K).BoundedFormula α n)
    (v : α → M) (xs : Fin n → M) :
    (d.relationOnlyAux A).Realize (Sum.elim v xs) ↔ A.Realize v xs := by
  induction A with
  | falsum => rfl
  | equal s t =>
    simp only [relationOnlyAux, Formula.realize_equal, oldTerm_realize]
    rfl
  | rel R ts =>
    rw [relationOnlyAux, Formula.Realize, BoundedFormula.realize_subst]
    change (d.symbolRelation R).Realize (fun i => (oldTerm (ts i)).realize (Sum.elim v xs)) ↔ _
    simp only [oldTerm_realize]
    exact realize_symbolRelation d h R _
  | imp A B ihA ihB =>
    simp only [relationOnlyAux, Formula.realize_imp, BoundedFormula.Realize, ihA, ihB]
  | @all n A ih =>
    simp only [relationOnlyAux, Formula.realize_iAlls, Formula.realize_relabel, bindLast_values]
    change (∀ y : Unit → M, (d.relationOnlyAux A).Realize
      (Sum.elim v (Fin.snoc xs (y ())))) ↔ ∀ y : M, A.Realize v (Fin.snoc xs y)
    simp_rw [ih]
    exact ⟨fun h y => h (fun _ => y), fun h y => h (y ())⟩

theorem realize_relationOnly [∀ n, IsEmpty (K.Functions n)] [(L.sum K).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum K).IsExpansionOn M]
    (h : M ⊨ d.definitions) (A : (L.sum K).Formula α) (v : α → M) :
    (d.relationOnly A).Realize v ↔ A.Realize v := by
  rw [relationOnly, Formula.realize_relabel]
  have hv : v ∘ Sum.elim id (Fin.elim0 : Fin 0 → α) = Sum.elim v default := by
    funext a
    cases a with
    | inl i => rfl
    | inr i => exact i.elim0
  rw [hv]
  exact realize_relationOnlyAux d ((d.goodExpansion_iff_models).mpr h) A v default

open Support

private theorem scopedTerm_uses [DecidableEq α] {P : α → Prop} {n : ℕ} (t : (L.sum K).Term (α ⊕ Fin n))
    (h : ∀ a ∈ t.varFinsetLeft, P a) : TermUses (Sum.elim P (fun _ => True)) t := by
  intro a ha
  cases a with
  | inl a => exact h a ((term_inl_support t a).mpr ha)
  | inr i => trivial

private theorem termGraph_uses [DecidableEq α] {P : α → Prop} (t : (L.sum K).Term α)
    (h : TermUses P t) : Uses (Sum.elim P (fun _ => True)) (d.termGraph t) := by
  induction t generalizing P with
  | var a =>
    apply equal_uses
    · intro b hb
      have he : b = Sum.inr () := Finset.mem_singleton.mp hb
      subst b
      trivial
    · intro b hb
      have he : b = Sum.inl a := Finset.mem_singleton.mp hb
      subst b
      exact h a (Finset.mem_singleton_self a)
  | @func n f ts ih =>
    apply iExs_uses
    apply inf_uses
    · apply iInf_uses
      intro i
      apply relabel_uses
      intro a ha
      have hi : TermUses P (ts i) := by
        intro b hb
        exact h b (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hb⟩)
      have hh := ih i hi a ha
      cases a <;> exact hh
    · apply relabel_uses_all
      intro a
      cases a <;> trivial

private theorem relationTranslation_uses [DecidableEq α] {P : α → Prop} {n : ℕ}
    (R : (L.sum K).Relations n) (ts : Fin n → (L.sum K).Term α)
    (h : ∀ i, TermUses P (ts i)) : Uses P (d.relationTranslation R ts) := by
  apply iExs_uses
  apply inf_uses
  · apply iInf_uses
    intro i
    apply relabel_uses
    intro a ha
    have hh := termGraph_uses d (ts i) (h i) a ha
    cases a <;> exact hh
  · apply relabel_uses_all
    intro a
    trivial

private theorem translateAux_uses [DecidableEq α] {P : α → Prop} {n : ℕ}
    (A : (L.sum K).BoundedFormula α n) (h : ∀ a ∈ A.freeVarFinset, P a) :
    Uses (Sum.elim P (fun _ => True)) (d.translateAux A) := by
  induction A with
  | falsum => exact bot_uses _
  | equal s t =>
    apply iExs_uses
    apply inf_uses
    · exact termGraph_uses d s (scopedTerm_uses s (fun a ha => h a (Finset.mem_union_left _ ha)))
    · exact termGraph_uses d t (scopedTerm_uses t (fun a ha => h a (Finset.mem_union_right _ ha)))
  | rel R ts =>
    apply relationTranslation_uses
    intro i
    exact scopedTerm_uses (ts i) (fun a ha => h a
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ha⟩))
  | imp A B ihA ihB =>
    exact imp_uses (ihA (fun a ha => h a (Finset.mem_union_left _ ha)))
      (ihB (fun a ha => h a (Finset.mem_union_right _ ha)))
  | @all n A ih =>
    apply iAlls_uses
    apply relabel_uses
    intro a ha
    have hh := ih h a ha
    cases a with
    | inl a => exact hh
    | inr i => refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [bindLast]

private theorem oldTerm_uses [DecidableEq α] [∀ n, IsEmpty (K.Functions n)] {P : α → Prop}
    (t : (L.sum K).Term α) (h : TermUses P t) : TermUses P (oldTerm t) := by
  induction t with
  | var a => exact h
  | @func n f ts ih =>
    cases f with
    | inl f =>
      intro a ha
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
      apply ih i ?_ a hi
      intro b hb
      exact h b (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hb⟩)
    | inr f => exact isEmptyElim f

private theorem relationOnlyAux_uses [DecidableEq α] [∀ n, IsEmpty (K.Functions n)] {P : α → Prop} {n : ℕ}
    (A : (L.sum K).BoundedFormula α n) (h : ∀ a ∈ A.freeVarFinset, P a) :
    Uses (Sum.elim P (fun _ => True)) (d.relationOnlyAux A) := by
  induction A with
  | falsum => exact bot_uses _
  | equal s t =>
    exact equal_uses
      (oldTerm_uses s (scopedTerm_uses s (fun a ha => h a (Finset.mem_union_left _ ha))))
      (oldTerm_uses t (scopedTerm_uses t (fun a ha => h a (Finset.mem_union_right _ ha))))
  | rel R ts =>
    apply subst_uses
    intro i
    exact oldTerm_uses (ts i) (scopedTerm_uses (ts i) (fun a ha => h a
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ha⟩)))
  | imp A B ihA ihB =>
    exact imp_uses (ihA (fun a ha => h a (Finset.mem_union_left _ ha)))
      (ihB (fun a ha => h a (Finset.mem_union_right _ ha)))
  | @all n A ih =>
    apply iAlls_uses
    apply relabel_uses
    intro a ha
    have hh := ih h a ha
    cases a with
    | inl a => exact hh
    | inr i => refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [bindLast]

theorem translate_freeVar_subset [DecidableEq α] (A : (L.sum K).Formula α) :
    (d.translate A).freeVarFinset ⊆ A.freeVarFinset := by
  classical
  change Uses (fun a => a ∈ A.freeVarFinset) (d.translate A)
  apply relabel_uses
  intro a ha
  have hh := translateAux_uses d A (fun _ ha => ha) a ha
  cases a with
  | inl a => exact hh
  | inr i => exact i.elim0

theorem relationOnly_freeVar_subset [DecidableEq α] [∀ n, IsEmpty (K.Functions n)]
    (A : (L.sum K).Formula α) :
    (d.relationOnly A).freeVarFinset ⊆ A.freeVarFinset := by
  classical
  change Uses (fun a => a ∈ A.freeVarFinset) (d.relationOnly A)
  apply relabel_uses
  intro a ha
  have hh := relationOnlyAux_uses d A (fun _ ha => ha) a ha
  cases a with
  | inl a => exact hh
  | inr i => exact i.elim0

/-- The witness is the formula computed before the model is quantified. -/
theorem uniform_elimination (A : (L.sum K).Formula α) :
    ∃ B : L.Formula α, B = d.translate A ∧
      ∀ (M : Type w) [L.Structure M] [(L.sum K).Structure M]
        [(LHom.sumInl : L →ᴸ L.sum K).IsExpansionOn M],
        M ⊨ d.definitions → ∀ v : α → M, B.Realize v ↔ A.Realize v := by
  refine ⟨d.translate A, rfl, ?_⟩
  intro M sL sK hinc hD v
  exact d.realize_translate ((d.goodExpansion_iff_models).mpr hD) A v

/-- Syntactic conservativity in the existing proof calculus. -/
theorem derives_extension_iff (T : L.Theory) (hd : Admissible d T) (A : L.Sentence) :
    Derives (d.extension T) ((LHom.sumInl : L →ᴸ L.sum K).onSentence A) ↔
      Derives T A := by
  constructor
  · intro hp
    apply ChangingLanguages.deductive_completeness
    apply Theory.models_sentence_iff.mpr
    intro M
    obtain ⟨S, hS, _⟩ := d.unique_expansion T hd (M := M)
    let := S
    let : (L.sum K).Structure M := Language.sumStructure L K M
    have hmodel : M ⊨ d.extension T :=
      Theory.Model.union ((LHom.onTheory_model _ T).mpr M.is_model) hS
    have hh := derives_sound hp default (fun B hB => hmodel.realize_of_mem B hB)
    exact (LHom.realize_onSentence M (LHom.sumInl : L →ᴸ L.sum K) A).mp hh
  · intro hp
    exact derives_mono (ChangingLanguages.derives_map (LHom.sumInl : L →ᴸ L.sum K) hp)
      Set.subset_union_left

theorem satisfiable_extension_iff (T : L.Theory) (hd : Admissible d T) :
    (d.extension T).IsSatisfiable ↔ T.IsSatisfiable := by
  constructor
  · intro h
    exact Theory.isSatisfiable_of_isSatisfiable_onTheory
      (LHom.sumInl : L →ᴸ L.sum K) (h.mono Set.subset_union_left)
  · intro h
    let M := h.some
    obtain ⟨S, hS, _⟩ := d.unique_expansion T hd (M := M)
    let := S
    let : (L.sum K).Structure M := Language.sumStructure L K M
    have : M ⊨ d.extension T :=
      Theory.Model.union ((LHom.onTheory_model _ T).mpr M.is_model) hS
    exact Theory.Model.isSatisfiable M

theorem consistent_extension_iff (T : L.Theory) (hd : Admissible d T) :
    Consistent (d.extension T) ↔ Consistent T := by
  exact not_congr (d.derives_extension_iff T hd (⊥ : L.Sentence))

/-- The shorter graph axiom; equivalent only under the total unique condition. -/
def shortFunctionAxiom {n : ℕ} (f : K.Functions n) : (L.sum K).Sentence :=
  close (((LHom.sumInl : L →ᴸ L.sum K).onFormula (d.functionGraph f)).subst
    (Sum.elim Term.var (fun _ => .func (.inr f) Term.var)))

theorem short_iff_full {n : ℕ} (f : K.Functions n) [(L.sum K).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum K).IsExpansionOn M]
    (h : M ⊨ totalUnique (d.functionGraph f)) :
    M ⊨ d.shortFunctionAxiom f ↔ M ⊨ d.functionAxiom f := by
  have hshort : M ⊨ d.shortFunctionAxiom f ↔ ∀ x : Fin n → M,
      (d.functionGraph f).Realize (Sum.elim x (fun _ =>
        @Structure.funMap (L.sum K) M _ n (.inr f) x)) := by
    rw [shortFunctionAxiom, realize_close]
    apply forall_congr'
    intro x
    rw [Formula.Realize, BoundedFormula.realize_subst]
    change ((LHom.sumInl : L →ᴸ L.sum K).onFormula (d.functionGraph f)).Realize _ ↔ _
    rw [LHom.realize_onFormula]
    apply Iff.of_eq
    congr 1
    funext a
    cases a <;> rfl
  rw [hshort, realize_functionAxiom]
  have ht := (realize_totalUnique _).mp h
  constructor
  · intro hs x y
    constructor
    · intro hy
      exact (ht x).unique hy (hs x)
    · intro hy
      exact hy ▸ hs x
  · intro hs x
    exact (hs x _).mpr rfl

end DefinitionPackage
end
end Lemmatheca.MathematicalLogic.DefinitionalExtensions
