import Lemmatheca.IntuitionisticFirstOrderDeduction.EqualityErasure

/-! Actual single-conclusion first-order sequent trees. Left rules retain their
principal formula. The cut-free and cutful grammars are distinct inductive types;
equality-free certificates additionally record pure end sequents. -/
namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
noncomputable section
abbrev BF := Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
abbrev Formula := Lemmatheca.ProofTheory.FirstOrder.Formula
abbrev Context := Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context
abbrev liftContext := @Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext
abbrev ContextPure := @Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure

local instance ifoqCalculusFormulaEq {L : Language.{u,v}} {α : Type w} :
    DecidableEq (Formula L α) := Classical.decEq _

/-- A finite cut-free tree in the displayed primitive calculus. -/
inductive CoreProof (L : Language.{u,v}) :
    {α : Type w} → Context L α → Formula L α → Type max u v (w+1)
  | relation {α Γ k} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin 0)) :
      (.rel R ts : Formula L α) ∈ Γ → CoreProof L Γ (.rel R ts)
  | falsumLeft {α Γ C} : (.falsum : Formula L α) ∈ Γ → CoreProof L Γ C
  | conjLeft {α Γ A B C} : (.conj A B : Formula L α) ∈ Γ →
      CoreProof L (insert A (insert B Γ)) C → CoreProof L Γ C
  | conjRight {α Γ A B} : CoreProof L (α := α) Γ A → CoreProof L Γ B →
      CoreProof L Γ (.conj A B)
  | disjLeft {α Γ A B C} : (.disj A B : Formula L α) ∈ Γ →
      CoreProof L (insert A Γ) C → CoreProof L (insert B Γ) C → CoreProof L Γ C
  | disjRightLeft {α Γ A B} : CoreProof L (α := α) Γ A → CoreProof L Γ (.disj A B)
  | disjRightRight {α Γ A B} : CoreProof L (α := α) Γ B → CoreProof L Γ (.disj A B)
  | implLeft {α Γ A B C} : (.impl A B : Formula L α) ∈ Γ →
      CoreProof L Γ A → CoreProof L (insert B Γ) C → CoreProof L Γ C
  | implRight {α Γ A B} : CoreProof L (α := α) (insert A Γ) B → CoreProof L Γ (.impl A B)
  | negLeft {α Γ A C} : (.neg A : Formula L α) ∈ Γ →
      CoreProof L Γ A → CoreProof L Γ C
  | negRight {α Γ A} : CoreProof L (α := α) (insert A Γ) .falsum → CoreProof L Γ (.neg A)
  | allLeft {α Γ C} {B : BF L α 1} (t : L.Term α) : (.all B) ∈ Γ →
      CoreProof L (insert (B.instantiate t) Γ) C → CoreProof L Γ C
  | allRight {α Γ} {B : BF L α 1} :
      CoreProof L (liftContext Γ) B.toFormula → CoreProof L (α := α) Γ (.all B)
  | exLeft {α Γ C} {B : BF L α 1} : (.ex B) ∈ Γ →
      CoreProof L (insert B.toFormula (liftContext Γ)) (C.rename Sum.inl) →
      CoreProof L (α := α) Γ C
  | exRight {α Γ} {B : BF L α 1} (t : L.Term α) :
      CoreProof L Γ (B.instantiate t) → CoreProof L (α := α) Γ (.ex B)

/-- The maximum number of inference edges from the root to a leaf. -/
def CoreProof.height : ∀ {α : Type w} {Γ : Context L α} {A : Formula L α},
    CoreProof L Γ A → ℕ
  | _, _, _, .relation _ _ _ | _, _, _, .falsumLeft _ => 0
  | _, _, _, .conjRight p q | _, _, _, .disjLeft _ p q
    | _, _, _, .implLeft _ p q => 1 + max p.height q.height
  | _, _, _, .conjLeft _ p | _, _, _, .disjRightLeft p
    | _, _, _, .disjRightRight p | _, _, _, .implRight p
    | _, _, _, .negLeft _ p | _, _, _, .negRight p
    | _, _, _, .allLeft _ _ p | _, _, _, .allRight p
    | _, _, _, .exLeft _ p | _, _, _, .exRight _ p => 1 + p.height

/-- Every sequent displayed at every node has equality-free formulas. -/
def CoreProof.Pure : ∀ {α : Type w} {Γ : Context L α} {A : Formula L α},
    CoreProof L Γ A → Prop
  | _, Γ, A, p => ContextPure Γ ∧ A.EqualityFree ∧ match p with
    | .relation _ _ _ | .falsumLeft _ => True
    | .conjRight p q | .disjLeft _ p q | .implLeft _ p q => p.Pure ∧ q.Pure
    | .conjLeft _ p | .disjRightLeft p | .disjRightRight p | .implRight p
      | .negLeft _ p | .negRight p | .allLeft _ _ p | .allRight p
      | .exLeft _ p | .exRight _ p => p.Pure

private theorem pureInsert {L : Language.{u,v}} {α : Type w}
    {Γ : Context L α} {A : Formula L α} (hΓ : ContextPure Γ)
    (hA : A.EqualityFree) : ContextPure (insert A Γ) := by
  intro B hB
  rcases Finset.mem_insert.mp hB with rfl | hB
  · exact hA
  · exact hΓ B hB

private theorem pureLift {L : Language.{u,v}} {α : Type w}
    {Γ : Context L α} (hΓ : ContextPure Γ) : ContextPure (liftContext Γ) := by
  intro B hB
  rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
  exact (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map A _).2 (hΓ A hA)

theorem CoreProof.pure_of_endpoints {L : Language.{u,v}} {α : Type w}
    {Γ : Context L α} {A : Formula L α} (p : CoreProof L Γ A)
    (hΓ : ContextPure Γ) (hA : A.EqualityFree) : p.Pure := by
  revert hΓ hA
  induction p with
  | relation R ts hmem => intro hΓ hA; exact ⟨hΓ, hA, True.intro⟩
  | falsumLeft hmem => intro hΓ hA; exact ⟨hΓ, hA, True.intro⟩
  | conjLeft hmem p ih =>
    intro hΓ hA
    have hp := hΓ _ hmem
    exact ⟨hΓ, hA, ih (pureInsert (pureInsert hΓ hp.2) hp.1) hA⟩
  | conjRight p q ihp ihq =>
    intro hΓ hA
    exact ⟨hΓ, hA, ihp hΓ hA.1, ihq hΓ hA.2⟩
  | disjLeft hmem p q ihp ihq =>
    intro hΓ hA
    have hp := hΓ _ hmem
    exact ⟨hΓ, hA, ihp (pureInsert hΓ hp.1) hA,
      ihq (pureInsert hΓ hp.2) hA⟩
  | disjRightLeft p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih hΓ hA.1⟩
  | disjRightRight p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih hΓ hA.2⟩
  | implLeft hmem p q ihp ihq =>
    intro hΓ hA
    have hp := hΓ _ hmem
    exact ⟨hΓ, hA, ihp hΓ hp.1, ihq (pureInsert hΓ hp.2) hA⟩
  | implRight p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih (pureInsert hΓ hA.1) hA.2⟩
  | negLeft hmem p ih =>
    intro hΓ hA
    have hp := hΓ _ hmem
    exact ⟨hΓ, hA, ih hΓ hp⟩
  | negRight p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih (pureInsert hΓ hA) True.intro⟩
  | allLeft t hmem p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih (pureInsert hΓ
      ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).2
        (hΓ _ hmem))) hA⟩
  | allRight p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih (pureLift hΓ)
      ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).2 hA)⟩
  | exLeft hmem p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih
      (pureInsert (pureLift hΓ)
        ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).2
          (hΓ _ hmem)))
      ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).2 hA)⟩
  | exRight t p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih hΓ
      ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).2 hA)⟩

/-- The same primitive calculus with an explicit split-context pure cut. -/
inductive CutProof (L : Language.{u,v}) :
    {α : Type w} → Context L α → Formula L α → Type max u v (w+1)
  | relation {α Γ k} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin 0)) :
      (.rel R ts : Formula L α) ∈ Γ → CutProof L Γ (.rel R ts)
  | falsumLeft {α Γ C} : (.falsum : Formula L α) ∈ Γ → CutProof L Γ C
  | conjLeft {α Γ A B C} : (.conj A B : Formula L α) ∈ Γ →
      CutProof L (insert A (insert B Γ)) C → CutProof L Γ C
  | conjRight {α Γ A B} : CutProof L (α := α) Γ A → CutProof L Γ B →
      CutProof L Γ (.conj A B)
  | disjLeft {α Γ A B C} : (.disj A B : Formula L α) ∈ Γ →
      CutProof L (insert A Γ) C → CutProof L (insert B Γ) C → CutProof L Γ C
  | disjRightLeft {α Γ A B} : CutProof L (α := α) Γ A → CutProof L Γ (.disj A B)
  | disjRightRight {α Γ A B} : CutProof L (α := α) Γ B → CutProof L Γ (.disj A B)
  | implLeft {α Γ A B C} : (.impl A B : Formula L α) ∈ Γ →
      CutProof L Γ A → CutProof L (insert B Γ) C → CutProof L Γ C
  | implRight {α Γ A B} : CutProof L (α := α) (insert A Γ) B → CutProof L Γ (.impl A B)
  | negLeft {α Γ A C} : (.neg A : Formula L α) ∈ Γ →
      CutProof L Γ A → CutProof L Γ C
  | negRight {α Γ A} : CutProof L (α := α) (insert A Γ) .falsum → CutProof L Γ (.neg A)
  | allLeft {α Γ C} {B : BF L α 1} (t : L.Term α) : (.all B) ∈ Γ →
      CutProof L (insert (B.instantiate t) Γ) C → CutProof L Γ C
  | allRight {α Γ} {B : BF L α 1} :
      CutProof L (liftContext Γ) B.toFormula → CutProof L (α := α) Γ (.all B)
  | exLeft {α Γ C} {B : BF L α 1} : (.ex B) ∈ Γ →
      CutProof L (insert B.toFormula (liftContext Γ)) (C.rename Sum.inl) →
      CutProof L (α := α) Γ C
  | exRight {α Γ} {B : BF L α 1} (t : L.Term α) :
      CutProof L Γ (B.instantiate t) → CutProof L (α := α) Γ (.ex B)
  | cut {α Γ Δ B A} : (B : Formula L α).EqualityFree →
      CutProof L Γ B → CutProof L (insert B Δ) A → CutProof L (Γ ∪ Δ) A

/-- The maximum number of inference edges from the root to a leaf. -/
def CutProof.height : ∀ {α : Type w} {Γ : Context L α} {A : Formula L α},
    CutProof L Γ A → ℕ
  | _, _, _, .relation _ _ _ | _, _, _, .falsumLeft _ => 0
  | _, _, _, .conjRight p q | _, _, _, .disjLeft _ p q
    | _, _, _, .implLeft _ p q => 1 + max p.height q.height
  | _, _, _, .conjLeft _ p | _, _, _, .disjRightLeft p
    | _, _, _, .disjRightRight p | _, _, _, .implRight p
    | _, _, _, .negLeft _ p | _, _, _, .negRight p
    | _, _, _, .allLeft _ _ p | _, _, _, .allRight p
    | _, _, _, .exLeft _ p | _, _, _, .exRight _ p => 1 + p.height
  | _, _, _, .cut _ p q => 1 + max p.height q.height

/-- Every sequent displayed at every node has equality-free formulas. -/
def CutProof.Pure : ∀ {α : Type w} {Γ : Context L α} {A : Formula L α},
    CutProof L Γ A → Prop
  | _, Γ, A, p => ContextPure Γ ∧ A.EqualityFree ∧ match p with
    | .relation _ _ _ | .falsumLeft _ => True
    | .conjRight p q | .disjLeft _ p q | .implLeft _ p q => p.Pure ∧ q.Pure
    | .conjLeft _ p | .disjRightLeft p | .disjRightRight p | .implRight p
      | .negLeft _ p | .negRight p | .allLeft _ _ p | .allRight p
      | .exLeft _ p | .exRight _ p => p.Pure
    | .cut _ p q => p.Pure ∧ q.Pure

theorem CutProof.pure_of_endpoints {L : Language.{u,v}} {α : Type w}
    {Γ : Context L α} {A : Formula L α} (p : CutProof L Γ A)
    (hΓ : ContextPure Γ) (hA : A.EqualityFree) : p.Pure := by
  revert hΓ hA
  induction p with
  | relation R ts hmem => intro hΓ hA; exact ⟨hΓ, hA, True.intro⟩
  | falsumLeft hmem => intro hΓ hA; exact ⟨hΓ, hA, True.intro⟩
  | conjLeft hmem p ih =>
    intro hΓ hA
    have hp := hΓ _ hmem
    exact ⟨hΓ, hA, ih (pureInsert (pureInsert hΓ hp.2) hp.1) hA⟩
  | conjRight p q ihp ihq =>
    intro hΓ hA
    exact ⟨hΓ, hA, ihp hΓ hA.1, ihq hΓ hA.2⟩
  | disjLeft hmem p q ihp ihq =>
    intro hΓ hA
    have hp := hΓ _ hmem
    exact ⟨hΓ, hA, ihp (pureInsert hΓ hp.1) hA,
      ihq (pureInsert hΓ hp.2) hA⟩
  | disjRightLeft p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih hΓ hA.1⟩
  | disjRightRight p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih hΓ hA.2⟩
  | implLeft hmem p q ihp ihq =>
    intro hΓ hA
    have hp := hΓ _ hmem
    exact ⟨hΓ, hA, ihp hΓ hp.1, ihq (pureInsert hΓ hp.2) hA⟩
  | implRight p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih (pureInsert hΓ hA.1) hA.2⟩
  | negLeft hmem p ih =>
    intro hΓ hA
    have hp := hΓ _ hmem
    exact ⟨hΓ, hA, ih hΓ hp⟩
  | negRight p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih (pureInsert hΓ hA) True.intro⟩
  | allLeft t hmem p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih (pureInsert hΓ
      ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).2
        (hΓ _ hmem))) hA⟩
  | allRight p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih (pureLift hΓ)
      ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).2 hA)⟩
  | exLeft hmem p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih
      (pureInsert (pureLift hΓ)
        ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).2
          (hΓ _ hmem)))
      ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).2 hA)⟩
  | exRight t p ih =>
    intro hΓ hA
    exact ⟨hΓ, hA, ih hΓ
      ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).2 hA)⟩
  | @cut α Γ Δ B A hB p q ihp ihq =>
    intro hΓΔ hA
    have hΓ : ContextPure Γ := fun C hC => hΓΔ C (Finset.mem_union_left _ hC)
    have hΔ : ContextPure Δ := fun C hC => hΓΔ C (Finset.mem_union_right _ hC)
    exact ⟨hΓΔ, hA, ihp hΓ hB, ihq (pureInsert hΔ hB) hA⟩

/-- An actual cut-free tree whose end sequent lies in the equality-free fragment. -/
structure RawProof (L : Language.{u,v}) {α : Type w} (Γ : Context L α) (A : Formula L α) :
    Type max u v (w+1) where
  tree : CoreProof L Γ A
  context_pure : ContextPure Γ
  conclusion_pure : A.EqualityFree

/-- An actual cutful tree with equality-free end sequent and cut formulas. -/
structure RawCutProof (L : Language.{u,v}) {α : Type w} (Γ : Context L α) (A : Formula L α) :
    Type max u v (w+1) where
  tree : CutProof L Γ A
  context_pure : ContextPure Γ
  conclusion_pure : A.EqualityFree

/-- Public cut-free certificates retain a disjoint countable auxiliary reserve. -/
def Proof (L : Language.{u,v}) {α : Type w} (Γ : Context L α) (A : Formula L α) :
    Type max u v (w+1) :=
  RawProof L (Γ.image (fun B => B.rename (Sum.inl : α → α ⊕ ℕ))) (A.rename Sum.inl)

/-- Public certificates with explicit cuts and the same auxiliary reserve. -/
def CutCertificate (L : Language.{u,v}) {α : Type w} (Γ : Context L α) (A : Formula L α) :
    Type max u v (w+1) :=
  RawCutProof L (Γ.image (fun B => B.rename (Sum.inl : α → α ⊕ ℕ))) (A.rename Sum.inl)

def Derives (L : Language.{u,v}) {α : Type w} (Γ : Context L α) (A : Formula L α) : Prop :=
  Nonempty (Proof L Γ A)

def CutDerives (L : Language.{u,v}) {α : Type w} (Γ : Context L α) (A : Formula L α) : Prop :=
  Nonempty (CutCertificate L Γ A)

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder
