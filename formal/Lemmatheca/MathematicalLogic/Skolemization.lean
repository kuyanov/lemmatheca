import Lemmatheca.MathematicalLogic.FirstOrderNormalForms

/-! Skolemization of finite prenex sentences, with exactly the preceding universals
as arguments of each fresh witness symbol. -/

namespace Lemmatheca.MathematicalLogic.Skolemization

open FirstOrder FirstOrder.Language

universe u v w u' v'

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

theorem constant_witness (A : M → Prop) :
    (∃ y, A y) ↔ ∃ f : (Fin 0 → M) → M, ∀ xs, A (f xs) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨fun _ => y, fun _ => hy⟩
  · rintro ⟨f, hf⟩
    exact ⟨f Fin.elim0, hf Fin.elim0⟩

theorem old_symbol_conflict (h : M → M) :
    ¬ ((∃ x, x ≠ h x) ∧ ∀ x, x = h x) := by
  rintro ⟨⟨x, hx⟩, hall⟩
  exact hx (hall x)

/-- A quantifier prefix together with its actual quantifier-free matrix. -/
inductive Prenex (L : Language.{u, v}) : ℕ → Type (max u v)
  | matrix {n : ℕ} (φ : L.BoundedFormula Empty n) (h : φ.IsQF) : Prenex L n
  | all {n : ℕ} : Prenex L (n + 1) → Prenex L n
  | ex {n : ℕ} : Prenex L (n + 1) → Prenex L n

namespace Prenex

/-- Forget the explicit prefix decomposition. -/
def toFormula : {n : ℕ} → Prenex L n → L.BoundedFormula Empty n
  | _, .matrix φ _ => φ
  | _, .all p => p.toFormula.all
  | _, .ex p => p.toFormula.ex

theorem toFormula_isPrenex {n : ℕ} (p : Prenex L n) : p.toFormula.IsPrenex := by
  induction p with
  | matrix φ h => exact h.isPrenex
  | all p ih => exact ih.all
  | ex p ih => exact ih.ex

theorem of_isPrenex {n : ℕ} {φ : L.BoundedFormula Empty n} (h : φ.IsPrenex) :
    ∃ p : Prenex L n, p.toFormula = φ := by
  induction h with
  | of_isQF h => exact ⟨.matrix _ h, rfl⟩
  | all h ih => obtain ⟨p, rfl⟩ := ih; exact ⟨.all p, rfl⟩
  | ex h ih => obtain ⟨p, rfl⟩ := ih; exact ⟨.ex p, rfl⟩

/-- Interpretations of the fresh symbols. At an existential step the arity is
the number of universal variables encountered so far. -/
def Witnesses : {n : ℕ} → Prenex L n → ℕ → Type w
  | _, .matrix _ _, _ => PUnit
  | _, .all p, k => p.Witnesses (k + 1)
  | _, .ex p, k => ((Fin k → M) → M) × p.Witnesses k

/-- Evaluate the matrix after replacing each existential slot by its witness
function applied only to the preceding universal values. -/
def skolemRealize : {n : ℕ} → (p : Prenex L n) → {k : ℕ} →
    p.Witnesses (M := M) k → (Fin n → M) → (Fin k → M) → Prop
  | _, .matrix φ _, _, _, xs, _ => φ.Realize Empty.elim xs
  | _, .all p, _, fs, xs, us => ∀ a : M,
      p.skolemRealize fs (Fin.snoc xs a) (Fin.snoc us a)
  | _, .ex p, _, fs, xs, us => p.skolemRealize fs.2 (Fin.snoc xs (fs.1 us)) us

theorem reduct {n k : ℕ} (p : Prenex L n) (fs : p.Witnesses (M := M) k)
    (xs : Fin n → M) (us : Fin k → M) (h : p.skolemRealize fs xs us) :
    p.toFormula.Realize Empty.elim xs := by
  induction p generalizing k with
  | matrix φ hq => exact h
  | all p ih => exact fun a => ih fs (Fin.snoc xs a) (Fin.snoc us a) (h a)
  | ex p ih =>
    rw [toFormula, BoundedFormula.realize_ex]
    exact ⟨fs.1 us, ih fs.2 _ us h⟩

/-- Uniformity in the previously chosen universal tuple is the key to obtaining
functions with the intended argument lists. -/
theorem uniform_expansion {n k : ℕ} (p : Prenex L n)
    (e : (Fin k → M) → (Fin n → M))
    (h : ∀ us, p.toFormula.Realize Empty.elim (e us)) :
    ∃ fs : p.Witnesses (M := M) k, ∀ us, p.skolemRealize fs (e us) us := by
  classical
  induction p generalizing k with
  | matrix φ hq => exact ⟨PUnit.unit, h⟩
  | all p ih =>
    let e' : (Fin (k + 1) → M) → (Fin (_ + 1) → M) := fun vs =>
      Fin.snoc (e (vs ∘ Fin.castSucc)) (vs (Fin.last k))
    obtain ⟨fs, hfs⟩ := ih e' (fun vs => h (vs ∘ Fin.castSucc) (vs (Fin.last k)))
    refine ⟨fs, fun us a => ?_⟩
    simpa [e'] using hfs (Fin.snoc us a)
  | ex p ih =>
    simp only [toFormula, BoundedFormula.realize_ex] at h
    choose f hf using h
    obtain ⟨fs, hfs⟩ := ih (fun us => Fin.snoc (e us) (f us)) hf
    exact ⟨(f, fs), hfs⟩

theorem expansion_iff {n : ℕ} (p : Prenex L n) (xs : Fin n → M) :
    p.toFormula.Realize Empty.elim xs ↔
      ∃ fs : p.Witnesses (M := M) 0, p.skolemRealize fs xs Fin.elim0 := by
  constructor
  · intro h
    obtain ⟨fs, hfs⟩ := p.uniform_expansion (fun _ => xs) (fun _ => h)
    exact ⟨fs, hfs Fin.elim0⟩
  · rintro ⟨fs, hfs⟩
    exact p.reduct fs xs Fin.elim0 hfs

/-- Fresh symbols indexed by their existential occurrence and required arity. -/
inductive Symbol : {n : ℕ} → Prenex L n → ℕ → ℕ → Type (max u v)
  | all {n k a : ℕ} {p : Prenex L (n + 1)} : Symbol p (k + 1) a → Symbol (.all p) k a
  | here {n k : ℕ} {p : Prenex L (n + 1)} : Symbol (.ex p) k k
  | there {n k a : ℕ} {p : Prenex L (n + 1)} : Symbol p k a → Symbol (.ex p) k a

/-- The language containing precisely the new function symbols and no relations. -/
abbrev witnessLanguage {n : ℕ} (p : Prenex L n) (k : ℕ) : Language where
  Functions := Symbol p k
  Relations := fun _ => Empty

/-- The expanded language keeps old and fresh symbols in disjoint summands. -/
abbrev expansionLanguage {n : ℕ} (p : Prenex L n) (k : ℕ) : Language :=
  L.sum (p.witnessLanguage k)

/-- Interpret the new symbol attached to each existential occurrence. -/
def symbolInterpretation : {n : ℕ} → (p : Prenex L n) → {k a : ℕ} →
    p.Witnesses (M := M) k → Symbol p k a → (Fin a → M) → M
  | _, .all p, _, _, fs, .all s => p.symbolInterpretation fs s
  | _, .ex _, _, _, fs, .here => fs.1
  | _, .ex p, _, _, fs, .there s => p.symbolInterpretation fs.2 s

/-- Every witness family gives an expansion on exactly the old domain. -/
@[instance_reducible]
def witnessStructure {n k : ℕ} (p : Prenex L n) (fs : p.Witnesses (M := M) k) :
    (p.witnessLanguage k).Structure M where
  funMap := p.symbolInterpretation fs
  RelMap := fun r => Empty.elim r

section Translation

variable {L' : Language.{u', v'}}

/-- A supply of function symbols in a target language, with the right arities. -/
def Symbols : {n : ℕ} → Prenex L n → ℕ → Type u'
  | _, .matrix _ _, _ => PUnit
  | _, .all p, k => Symbols p (k + 1)
  | _, .ex p, k => L'.Functions k × Symbols p k

/-- Fill all scoped slots of a matrix by terms in the current universal slots. -/
def fill {n k : ℕ} (φ : L'.BoundedFormula Empty n)
    (ts : Fin n → L'.Term (Empty ⊕ Fin k)) : L'.BoundedFormula Empty k :=
  (φ.toFormula.subst (Sum.elim Empty.elim ts)).relabel (n := k) id

theorem fill_realize [L'.Structure M] {n k : ℕ} (φ : L'.BoundedFormula Empty n)
    (ts : Fin n → L'.Term (Empty ⊕ Fin k)) (us : Fin k → M) :
    (fill φ ts).Realize Empty.elim us ↔
      φ.Realize Empty.elim (fun i => (ts i).realize (Sum.elim Empty.elim us)) := by
  simp only [fill, BoundedFormula.realize_relabel, Fin.castAdd_zero,
    Function.comp_id, BoundedFormula.realize_subst]
  simp only [Function.comp_def, Fin.cast_eq_self]
  rw [Formula.boundedFormula_realize_eq_realize]
  change φ.toFormula.Realize (fun x : Empty ⊕ Fin n =>
    (Sum.elim Empty.elim ts x).realize (Sum.elim Empty.elim us)) ↔ _
  rw [BoundedFormula.realize_toFormula]
  apply Iff.of_eq
  congr 1
  funext x
  exact x.elim

/-- Translate an explicit prefix, carrying the replacement term for each old slot. -/
def translate (ι : L →ᴸ L') : {n k : ℕ} → (p : Prenex L n) →
    @Symbols L L' _ p k → (Fin n → L'.Term (Empty ⊕ Fin k)) →
    L'.BoundedFormula Empty k
  | _, _, .matrix φ _, _, ts => fill (ι.onBoundedFormula φ) ts
  | _, _, .all p, ss, ts =>
      (translate ι p ss (Fin.snoc (fun i =>
        (ts i).relabel (Sum.map id Fin.castSucc)) (.var (.inr (Fin.last _))))).all
  | _, _, .ex p, ss, ts =>
      translate ι p ss.2 (Fin.snoc ts (.func ss.1 (fun i => .var (.inr i))))

/-- Read a syntactic supply as its family of interpreted functions. -/
def interpretSymbols [L'.Structure M] : {n k : ℕ} → (p : Prenex L n) →
    @Symbols L L' _ p k → p.Witnesses (M := M) k
  | _, _, .matrix _ _, _ => PUnit.unit
  | _, _, .all p, ss => interpretSymbols p ss
  | _, _, .ex p, ss => (Structure.funMap ss.1, interpretSymbols p ss.2)

theorem translate_realize [L'.Structure M] (ι : L →ᴸ L') [ι.IsExpansionOn M]
    {n k : ℕ} (p : Prenex L n) (ss : @Symbols L L' _ p k)
    (ts : Fin n → L'.Term (Empty ⊕ Fin k)) (us : Fin k → M) :
    (p.translate ι ss ts).Realize Empty.elim us ↔
      p.skolemRealize (p.interpretSymbols ss)
        (fun i => (ts i).realize (Sum.elim Empty.elim us)) us := by
  induction p generalizing k with
  | matrix φ hq =>
    rw [translate, fill_realize, ι.realize_onBoundedFormula]
    rfl
  | all p ih =>
    change @Symbols L L' _ p (k + 1) at ss
    simp only [translate, BoundedFormula.realize_all, interpretSymbols, skolemRealize]
    apply forall_congr'
    intro a
    rw [ih]
    apply Iff.of_eq
    congr 1
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.snoc_castSucc, Term.realize_relabel]
      congr 1
      funext z
      cases z with
      | inl z => exact z.elim
      | inr z => simp
  | ex p ih =>
    rw [translate, ih]
    simp only [interpretSymbols, skolemRealize]
    apply Iff.of_eq
    congr 1
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Term.realize]
    · simp

/-- The canonical supply uses distinct constructors for different occurrences. -/
def symbolSupply {n k : ℕ} (p : Prenex L n)
    (ι : ∀ {a}, Symbol p k a → L'.Functions a) : @Symbols L L' _ p k :=
  match p with
  | .matrix _ _ => PUnit.unit
  | .all p => p.symbolSupply (fun s => ι (.all s))
  | .ex p => (ι .here, p.symbolSupply (fun s => ι (.there s)))

theorem translate_isUniversal (ι : L →ᴸ L') {n k : ℕ} (p : Prenex L n)
    (ss : @Symbols L L' _ p k) (ts : Fin n → L'.Term (Empty ⊕ Fin k)) :
    (p.translate ι ss ts).IsUniversal := by
  induction p generalizing k with
  | matrix φ hq =>
    apply BoundedFormula.IsQF.isUniversal
    induction hq with
    | falsum => exact BoundedFormula.isQF_bot
    | of_isAtomic ha =>
      cases ha with
      | equal t s => exact (BoundedFormula.IsAtomic.equal _ _).isQF
      | rel r ts => exact (BoundedFormula.IsAtomic.rel _ _).isQF
    | imp hφ hψ ihφ ihψ => exact (ihφ ss).imp (ihψ ss)
  | all p ih => exact (ih ss _).all
  | ex p ih => exact ih ss.2 _

end Translation

/-- The actual universal sentence in the expanded first-order language. -/
def skolemForm (p : Prenex L 0) : (p.expansionLanguage 0).Sentence :=
  p.translate LHom.sumInl (p.symbolSupply (fun s => Sum.inr s)) Fin.elim0

theorem skolemForm_isUniversal (p : Prenex L 0) : p.skolemForm.IsUniversal :=
  p.translate_isUniversal _ _ _

omit [L.Structure M] in
private theorem interpret_symbolSupply
    {L' : Language.{u', v'}} [L'.Structure M] {n k : ℕ} (p : Prenex L n)
    (fs : p.Witnesses (M := M) k) (ι : ∀ {a}, Symbol p k a → L'.Functions a)
    (h : ∀ {a} (s : Symbol p k a) (us : Fin a → M),
      Structure.funMap (ι s) us = p.symbolInterpretation fs s us) :
    p.interpretSymbols (p.symbolSupply ι) = fs := by
  induction p generalizing k with
  | matrix φ hq =>
    change PUnit at fs
    cases fs
    rfl
  | all p ih => exact ih fs (fun s => ι (.all s)) (fun s us => h (.all s) us)
  | ex p ih =>
    apply Prod.ext
    · funext us
      exact h .here us
    · exact ih fs.2 (fun s => ι (.there s)) (fun s us => h (.there s) us)

theorem expansion (p : Prenex L 0) (h : M ⊨ p.toFormula) :
    ∃ W : (p.witnessLanguage 0).Structure M,
      let := W
      M ⊨ p.skolemForm := by
  have he : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  have hz : (default : Fin 0 → M) = Fin.elim0 := Subsingleton.elim _ _
  have h' : BoundedFormula.Realize p.toFormula (Empty.elim : Empty → M) Fin.elim0 := by
    simpa only [Sentence.Realize, Formula.Realize, he, hz] using h
  obtain ⟨fs, hfs⟩ := p.expansion_iff Fin.elim0 |>.mp h'
  let W : (p.witnessLanguage 0).Structure M := p.witnessStructure fs
  let := W
  refine ⟨W, ?_⟩
  simp only [Sentence.Realize, Formula.Realize, he, hz]
  change (p.translate (L' := p.expansionLanguage 0) LHom.sumInl (p.symbolSupply (fun s => Sum.inr s))
    Fin.elim0).Realize Empty.elim Fin.elim0
  rw [p.translate_realize (L' := p.expansionLanguage 0) LHom.sumInl]
  have hs := interpret_symbolSupply (L' := p.expansionLanguage 0) p fs (fun s => Sum.inr s)
    (fun _ _ => rfl)
  rw [hs]
  simpa only [Subsingleton.elim (fun i : Fin 0 => _) Fin.elim0] using hfs

theorem skolemForm_reduct (p : Prenex L 0)
    [(p.expansionLanguage 0).Structure M]
    [(LHom.sumInl : L →ᴸ p.expansionLanguage 0).IsExpansionOn M]
    (h : M ⊨ p.skolemForm) :
    M ⊨ p.toFormula := by
  have he : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  have hz : (default : Fin 0 → M) = Fin.elim0 := Subsingleton.elim _ _
  simp only [Sentence.Realize, Formula.Realize, he, hz] at h ⊢
  have hh := (p.translate_realize (L' := p.expansionLanguage 0) LHom.sumInl
    (p.symbolSupply (fun s => Sum.inr s)) Fin.elim0 Fin.elim0).mp h
  have hr := p.reduct _ _ _ hh
  simpa only [Subsingleton.elim (fun i : Fin 0 => _) Fin.elim0] using hr

theorem model_expansion_iff (p : Prenex L 0) :
    M ⊨ p.toFormula ↔ ∃ W : (p.witnessLanguage 0).Structure M,
      let := W
      M ⊨ p.skolemForm := by
  constructor
  · exact p.expansion
  · rintro ⟨W, hW⟩
    let := W
    exact p.skolemForm_reduct hW

theorem background_expansion_iff (p : Prenex L 0) (T : L.Theory) :
    (M ⊨ T ∧ M ⊨ p.toFormula) ↔
      ∃ W : (p.witnessLanguage 0).Structure M,
        let := W
        M ⊨ (LHom.sumInl : L →ᴸ p.expansionLanguage 0).onTheory T ∧ M ⊨ p.skolemForm := by
  constructor
  · rintro ⟨hT, hp⟩
    obtain ⟨W, hW⟩ := p.expansion hp
    let := W
    exact ⟨W, (LHom.sumInl.onTheory_model T).mpr hT, hW⟩
  · rintro ⟨W, hT, hW⟩
    let := W
    exact ⟨(LHom.sumInl.onTheory_model T).mp hT, p.skolemForm_reduct hW⟩

theorem equisatisfiable (p : Prenex L 0) (T : L.Theory) :
    (T ∪ {p.toFormula}).IsSatisfiable ↔
      ((LHom.sumInl : L →ᴸ p.expansionLanguage 0).onTheory T ∪ {p.skolemForm}).IsSatisfiable := by
  constructor
  · rintro ⟨N⟩
    have hT : N ⊨ T := N.is_model.mono Set.subset_union_left
    have hp : N ⊨ p.toFormula := N.is_model.realize_of_mem _ (by simp)
    obtain ⟨W, hWT, hWp⟩ := (p.background_expansion_iff T).mp ⟨hT, hp⟩
    let := W
    let : N ⊨ (LHom.sumInl : L →ᴸ p.expansionLanguage 0).onTheory T ∪ {p.skolemForm} :=
      ⟨fun φ hφ => by
        rcases hφ with hφ | hφ
        · exact hWT.realize_of_mem φ hφ
        · have heq : φ = p.skolemForm := Set.mem_singleton_iff.mp hφ
          simpa only [heq] using hWp⟩
    exact Theory.Model.isSatisfiable N
  · rintro ⟨N⟩
    let : L.Structure N := (LHom.sumInl : L →ᴸ p.expansionLanguage 0).reduct N
    have hT : N ⊨ T := (LHom.sumInl.onTheory_model T).mp
      (N.is_model.mono Set.subset_union_left)
    have hp : N ⊨ p.toFormula := p.skolemForm_reduct
      (N.is_model.realize_of_mem _ (by simp))
    let : N ⊨ T ∪ {p.toFormula} := ⟨fun φ hφ => by
      rcases hφ with hφ | hφ
      · exact hT.realize_of_mem φ hφ
      · have heq : φ = p.toFormula := Set.mem_singleton_iff.mp hφ
        simpa only [heq] using hp⟩
    exact Theory.Model.isSatisfiable N

end Prenex

/-- A single fresh function symbol of the specified arity. -/
def oneWitnessLanguage (k : ℕ) : Language where
  Functions := fun n => PLift (n = k)
  Relations := fun _ => Empty

@[instance_reducible]
def oneWitnessStructure {k : ℕ} (f : (Fin k → M) → M) :
    (oneWitnessLanguage k).Structure M where
  funMap := fun s xs => by
    rcases s with ⟨rfl⟩
    exact f xs
  RelMap := fun r => Empty.elim r

/-- Replace the last available slot by the new function applied to all earlier slots. -/
def oneWitnessBody {k : ℕ} (φ : L.BoundedFormula Empty (k + 1)) :
    (L.sum (oneWitnessLanguage k)).BoundedFormula Empty k :=
  Prenex.fill (LHom.sumInl.onBoundedFormula φ)
    (Fin.snoc (fun i => .var (.inr i))
      (.func (.inr ⟨rfl⟩) (fun i => .var (.inr i))))

theorem oneWitnessBody_realize {k : ℕ} [W : (oneWitnessLanguage k).Structure M]
    (φ : L.BoundedFormula Empty (k + 1)) (xs : Fin k → M) :
    (oneWitnessBody φ).Realize Empty.elim xs ↔
      φ.Realize Empty.elim (Fin.snoc xs
        (Structure.funMap (L := oneWitnessLanguage k) (⟨rfl⟩ : PLift (k = k)) xs)) := by
  rw [oneWitnessBody, Prenex.fill_realize, LHom.sumInl.realize_onBoundedFormula]
  apply Iff.of_eq
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, Term.realize, Sum.elim_inr]
    rfl
  · simp

private theorem sentence_alls_iff {n : ℕ} (φ : L.BoundedFormula Empty n) :
    M ⊨ φ.alls ↔ ∀ xs, φ.Realize (Empty.elim : Empty → M) xs := by
  have he : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  simpa only [Sentence.Realize, he] using
    (BoundedFormula.realize_alls (φ := φ) (v := Empty.elim))

/-- The one-witness step as an actual first-order formula, with arbitrary
quantifiers still allowed inside its body. -/
theorem one_witness_formula {k : ℕ} (φ : L.BoundedFormula Empty (k + 1)) :
    M ⊨ φ.ex.alls ↔ ∃ W : (oneWitnessLanguage k).Structure M,
      let := W
      M ⊨ (oneWitnessBody φ).alls := by
  rw [sentence_alls_iff]
  simp only [BoundedFormula.realize_ex]
  constructor
  · intro h
    obtain ⟨f, hf⟩ := Classical.skolem.mp h
    let W : (oneWitnessLanguage k).Structure M := oneWitnessStructure f
    let := W
    refine ⟨W, (sentence_alls_iff _).mpr (fun xs => ?_)⟩
    apply (oneWitnessBody_realize φ xs).mpr
    exact hf xs
  · rintro ⟨W, hW⟩
    let := W
    have h := (sentence_alls_iff _).mp hW
    intro xs
    exact ⟨_, (oneWitnessBody_realize φ xs).mp (h xs)⟩

/-- Every sentence has one universal companion in a fresh-function language,
chosen independently of any background theory and working for every such theory. -/
theorem every_sentence_universal (σ : L.Sentence) :
    ∃ (W : Language.{max u v, 0}) (τ : (L.sum W).Sentence),
      W.IsAlgebraic ∧ τ.IsUniversal ∧
        ∀ T : L.Theory,
        ((T ∪ {σ}).IsSatisfiable ↔
          ((LHom.sumInl : L →ᴸ L.sum W).onTheory T ∪ {τ}).IsSatisfiable) := by
  obtain ⟨p, hp⟩ := Prenex.of_isPrenex σ.toPrenex_isPrenex
  refine ⟨p.witnessLanguage 0, p.skolemForm, (fun _ => inferInstance),
    p.skolemForm_isUniversal, ?_⟩
  intro T
  rw [← p.equisatisfiable T]
  have equiv : ∀ (N : Type (max u v)) [L.Structure N] [Nonempty N],
      N ⊨ p.toFormula ↔ N ⊨ σ := by
    intro N _ _
    rw [hp]
    simp only [Sentence.Realize, Formula.Realize]
    exact BoundedFormula.realize_toPrenex σ
  constructor
  · rintro ⟨N⟩
    let : N ⊨ T ∪ {p.toFormula} := ⟨fun θ hθ => by
      rcases hθ with hθ | hθ
      · exact N.is_model.realize_of_mem θ (Set.mem_union_left _ hθ)
      · have heq : θ = p.toFormula := Set.mem_singleton_iff.mp hθ
        rw [heq]
        exact (equiv N).mpr (N.is_model.realize_of_mem _ (by simp))⟩
    exact Theory.Model.isSatisfiable N
  · rintro ⟨N⟩
    let : N ⊨ T ∪ {σ} := ⟨fun θ hθ => by
      rcases hθ with hθ | hθ
      · exact N.is_model.realize_of_mem θ (Set.mem_union_left _ hθ)
      · have heq : θ = σ := Set.mem_singleton_iff.mp hθ
        rw [heq]
        exact (equiv N).mp (N.is_model.realize_of_mem _ (by simp))⟩
    exact Theory.Model.isSatisfiable N

end Lemmatheca.MathematicalLogic.Skolemization
