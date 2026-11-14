import Lemmatheca.HeytingArithmetic.Axioms
import Lemmatheca.ClassicalFirstOrderDeductionTranslations.Public

/-! Finitely supported actual native proofs, distinct from their nonemptiness.
The sole mode flag adds classical contradiction; logical equality is enabled. -/
namespace Lemmatheca.ProofTheory.HeytingArithmetic
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
universe w
variable {α β : Type w} {c : Bool}
noncomputable section
local instance haCertificateEq {δ : Type w} : DecidableEq (Formula δ) := Classical.decEq _

/-- Closed arithmetic axioms viewed in the original free-name set. -/
def liftTheory (T : Set Sentence) (α : Type w) : Set (Formula α) :=
  (fun θ => θ.rename (Empty.elim : Empty → α)) '' T

def assumptions (T : Set Sentence) (Γ : Context α) : Set (Formula α) :=
  liftTheory T α ∪ (↑Γ : Set (Formula α))

abbrev TheoryCertificate (c : Bool) (T : Set Sentence) (Γ : Context α) (A : Formula α) :=
  Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.TheoryProof c true LA (assumptions T Γ) A

abbrev Certificate (c : Bool) (Γ : Context α) (A : Formula α) :=
  TheoryCertificate c theory Γ A

def Provable (c : Bool) (Γ : Context α) (A : Formula α) : Prop :=
  Nonempty (Certificate c Γ A)

/-- Identical finite support, with an actual raw rather than public proof tree. -/
structure RawCertificate (c : Bool) (T : Set Sentence) (Γ : Context α) (A : Formula α) where
  support : Context α
  allowed : ∀ B ∈ support, B ∈ assumptions T Γ
  derivation : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation c true LA support A

namespace TheoryCertificate
variable {T S : Set Sentence} {Γ Δ : Context α} {A : Formula α}

/-- Fix original names and replace every public reserve name by zero. -/
def toRaw (p : TheoryCertificate c T Γ A) : RawCertificate c T Γ A := by
  let σ : α ⊕ ℕ → LA.Term α := Sum.elim Term.var (fun _ => zeroTerm)
  have fix (B : Formula α) : (B.rename (Sum.inl : α → α ⊕ ℕ)).subst σ = B := by
    rw [formula_rename_subst]
    exact B.subst_id
  let raw : Derivation c true LA
      (p.assumptions.image (fun B => B.rename (Sum.inl : α → α ⊕ ℕ)))
      (A.rename Sum.inl) := p.derivation
  refine ⟨p.assumptions, p.allowed, ?_⟩
  simpa only [Finset.image_image, Function.comp_def, fix, Finset.image_id'] using
    raw.substitute σ

theorem toRaw_support (p : TheoryCertificate c T Γ A) :
    p.toRaw.support = p.assumptions := by rfl

/-- Left-rename the supplied raw finite proof into its public reserve. -/
def ofRaw (p : RawCertificate c T Γ A) : TheoryCertificate c T Γ A := by
  exact ⟨p.support, p.allowed,
    p.derivation.rename (Sum.inl : α → α ⊕ ℕ)⟩

theorem ofRaw_support (p : RawCertificate c T Γ A) :
    (ofRaw p).assumptions = p.support := by rfl

/-- Closed arithmetic axioms remain closed under original-name renaming. -/
def rename (p : TheoryCertificate c T Γ A) (f : α → β) :
    TheoryCertificate c T (Γ.image (fun B => B.rename f)) (A.rename f) := by
  refine ⟨p.assumptions.image (fun B => B.rename f), ?_, p.derivation.rename f⟩
  intro B hB
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
  rcases p.allowed C hC with hT | hΓ
  · left
    obtain ⟨θ, hθ, rfl⟩ := hT
    refine ⟨θ, hθ, ?_⟩
    rw [rename_comp]
    apply congrArg (fun g : Empty → β => θ.rename g)
    funext x
    exact x.elim
  · right
    exact Finset.mem_image.mpr ⟨C, hΓ, rfl⟩

/-- A certificate over a smaller axiom set remains an actual certificate. -/
def mono (p : TheoryCertificate c T Γ A) (h : T ⊆ S) :
    TheoryCertificate c S Γ A := by
  refine ⟨p.assumptions, ?_, p.derivation⟩
  intro B hB
  rcases p.allowed B hB with hT | hΓ
  · left
    obtain ⟨θ, hθ, rfl⟩ := hT
    exact ⟨θ, h hθ, rfl⟩
  · exact Or.inr hΓ

end TheoryCertificate

/-- Copy the finite actual intuitionistic tree into the classical mode. -/
def Certificate.classicalize {Γ : Context α} {A : Formula α}
    (p : Certificate false Γ A) : Certificate true Γ A := by
  exact ⟨p.assumptions, p.allowed, p.derivation.classicalize⟩

/-- A closed axiom is fixed by substitution into any original-name set. -/
theorem closed_subst (θ : Sentence) (σ : α → LA.Term β) :
    (θ.rename (Empty.elim : Empty → α)).subst σ = θ.rename Empty.elim := by
  simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_comp, Term.subst]
  congr 1
  funext x
  exact x.elim

theorem closed_rename (θ : Sentence) (f : α → β) :
    (θ.rename (Empty.elim : Empty → α)).rename f = θ.rename Empty.elim := by
  rw [rename_comp]
  apply congrArg (fun g : Empty → β => θ.rename g)
  funext x
  exact x.elim

namespace TheoryCertificate
variable {T : Set Sentence} {Γ Δ : Context α} {A B C : Formula α}

def ofProof (p : Proof c true LA Γ A) : TheoryCertificate c T Γ A :=
  ⟨Γ, fun _ h => Or.inr h, p⟩

def assumption (h : A ∈ Γ) : TheoryCertificate c T Γ A :=
  ofProof (Proof.assumption h)

def fromAxiom (θ : Sentence) (hθ : θ ∈ T) :
    TheoryCertificate c T Γ (θ.rename (Empty.elim : Empty → α)) := by
  refine ⟨{θ.rename Empty.elim}, ?_, Proof.assumption (Finset.mem_singleton_self _)⟩
  intro D hD
  have he := Finset.mem_singleton.mp hD
  subst D
  exact Or.inl ⟨θ, hθ, rfl⟩

def weaken (p : TheoryCertificate c T Γ A) (h : Γ ⊆ Δ) :
    TheoryCertificate c T Δ A := by
  refine ⟨p.assumptions, ?_, p.derivation⟩
  intro D hD
  rcases p.allowed D hD with hT | hΓ
  · exact Or.inl hT
  · exact Or.inr (h hΓ)

/-- Union precisely the two supplied finite supports before a logical step. -/
def combine (p : TheoryCertificate c T Γ A) (q : TheoryCertificate c T Γ B)
    (f : ∀ Ξ : Context α, Proof c true LA Ξ A → Proof c true LA Ξ B → Proof c true LA Ξ C) :
    TheoryCertificate c T Γ C := by
  refine ⟨p.assumptions ∪ q.assumptions, ?_, f _
    (p.derivation.weaken Finset.subset_union_left)
    (q.derivation.weaken Finset.subset_union_right)⟩
  intro D hD
  rcases Finset.mem_union.mp hD with hp | hq
  · exact p.allowed D hp
  · exact q.allowed D hq

def conjIntro (p : TheoryCertificate c T Γ A) (q : TheoryCertificate c T Γ B) :
    TheoryCertificate c T Γ (.conj A B) :=
  combine p q (fun _ => Proof.conjIntro)

def conjLeft (p : TheoryCertificate c T Γ (.conj A B)) : TheoryCertificate c T Γ A :=
  ⟨p.assumptions, p.allowed, Proof.conjElimLeft p.derivation⟩

def conjRight (p : TheoryCertificate c T Γ (.conj A B)) : TheoryCertificate c T Γ B :=
  ⟨p.assumptions, p.allowed, Proof.conjElimRight p.derivation⟩

def disjLeft (p : TheoryCertificate c T Γ A) : TheoryCertificate c T Γ (.disj A B) :=
  ⟨p.assumptions, p.allowed, Proof.disjIntroLeft p.derivation⟩

def disjRight (p : TheoryCertificate c T Γ B) : TheoryCertificate c T Γ (.disj A B) :=
  ⟨p.assumptions, p.allowed, Proof.disjIntroRight p.derivation⟩

def impElim (p : TheoryCertificate c T Γ (.impl A B)) (q : TheoryCertificate c T Γ A) :
    TheoryCertificate c T Γ B := combine p q (fun _ => Proof.impElim)

def negElim (p : TheoryCertificate c T Γ A) (q : TheoryCertificate c T Γ (.neg A)) :
    TheoryCertificate c T Γ .falsum := combine p q (fun _ => Proof.negElim)

def falsumElim (p : TheoryCertificate c T Γ .falsum) : TheoryCertificate c T Γ A :=
  ⟨p.assumptions, p.allowed, Proof.falsumElim p.derivation⟩

/-- Discharge an assumption by erasing it from the supplied finite support. -/
def impIntro (p : TheoryCertificate c T (insert A Γ) B) :
    TheoryCertificate c T Γ (.impl A B) := by
  refine ⟨p.assumptions.erase A, ?_, Proof.impIntro (p.derivation.weaken ?_)⟩
  · intro D hD
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hD
    rcases p.allowed D hmem with hT | hΓ
    · exact Or.inl hT
    · exact Or.inr ((Finset.mem_insert.mp hΓ).resolve_left hne)
  · intro D hD
    by_cases he : D = A
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨he, hD⟩))

def negIntro (p : TheoryCertificate c T (insert A Γ) .falsum) :
    TheoryCertificate c T Γ (.neg A) := by
  refine ⟨p.assumptions.erase A, ?_, Proof.negIntro (p.derivation.weaken ?_)⟩
  · intro D hD
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hD
    rcases p.allowed D hmem with hT | hΓ
    · exact Or.inl hT
    · exact Or.inr ((Finset.mem_insert.mp hΓ).resolve_left hne)
  · intro D hD
    by_cases he : D = A
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨he, hD⟩))

def disjElim (p : TheoryCertificate c T Γ (.disj A B))
    (q : TheoryCertificate c T (insert A Γ) C)
    (r : TheoryCertificate c T (insert B Γ) C) : TheoryCertificate c T Γ C := by
  let qa := impIntro q
  let rb := impIntro r
  let ab : TheoryCertificate c T Γ (.conj (.impl A C) (.impl B C)) := conjIntro qa rb
  exact combine p ab (fun Ξ hp hab => Proof.disjElim hp
    (Proof.impElim ((Proof.conjElimLeft hab).weaken (Finset.subset_insert _ _))
      (Proof.assumption (Finset.mem_insert_self _ _)))
    (Proof.impElim ((Proof.conjElimRight hab).weaken (Finset.subset_insert _ _))
      (Proof.assumption (Finset.mem_insert_self _ _))))

def substitute (p : TheoryCertificate c T Γ A) (σ : α → LA.Term β) :
    TheoryCertificate c T (Γ.image (fun B => B.subst σ)) (A.subst σ) := by
  refine ⟨p.assumptions.image (fun B => B.subst σ), ?_, p.derivation.substitute σ⟩
  intro D hD
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hD
  rcases p.allowed E hE with hT | hΓ
  · left
    obtain ⟨θ, hθ, rfl⟩ := hT
    exact ⟨θ, hθ, (closed_subst θ σ).symm⟩
  · exact Or.inr (Finset.mem_image.mpr ⟨E, hΓ, rfl⟩)

def allElim {D : BF α 1} (t : LA.Term α) (p : TheoryCertificate c T Γ (.all D)) :
    TheoryCertificate c T Γ (D.instantiate t) :=
  ⟨p.assumptions, p.allowed, Proof.allElim t p.derivation⟩

def exIntro {D : BF α 1} (t : LA.Term α) (p : TheoryCertificate c T Γ (D.instantiate t)) :
    TheoryCertificate c T Γ (.ex D) :=
  ⟨p.assumptions, p.allowed, Proof.exIntro t p.derivation⟩

/-- Pull a finite lifted support back with zero, retaining the supplied fresh-parameter tree. -/
def allIntro {D : BF α 1}
    (p : TheoryCertificate c T (Γ.image (fun B => B.rename Sum.inl)) D.toFormula) :
    TheoryCertificate c T Γ (.all D) := by
  let σ : α ⊕ Fin 1 → LA.Term α := Sum.elim Term.var (fun _ => zeroTerm)
  have fix (E : Formula α) : (E.rename (Sum.inl : α → α ⊕ Fin 1)).subst σ = E := by
    rw [formula_rename_subst]
    exact E.subst_id
  have pull {E : Formula (α ⊕ Fin 1)} (hE : E ∈ p.assumptions) :
      E.subst σ ∈ assumptions T Γ ∧ (E.subst σ).rename Sum.inl = E := by
    rcases p.allowed E hE with hT | hΓ
    · obtain ⟨θ, hθ, rfl⟩ := hT
      rw [closed_subst θ σ]
      exact ⟨Or.inl ⟨θ, hθ, rfl⟩, closed_rename θ Sum.inl⟩
    · obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hΓ
      rw [fix]
      exact ⟨Or.inr hF, rfl⟩
  refine ⟨p.assumptions.image (fun E => E.subst σ), ?_, Proof.allIntro (p.derivation.weaken ?_)⟩
  · intro E hE
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hE
    exact (pull hF).1
  · intro E hE
    exact Finset.mem_image.mpr ⟨E.subst σ, Finset.mem_image.mpr ⟨E, hE, rfl⟩, (pull hE).2⟩

end TheoryCertificate

section UniverseRenaming
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v
variable {δ : Type u} {ε : Type v}
theorem termEqual_subst_poly (s t : LA.Term δ) (σ : δ → LA.Term ε) :
    (termEqual s t).subst σ = termEqual (s.subst σ) (t.subst σ) := by
  simp [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual,
    subst_equal, term_subst_relabel, term_relabel_subst, freeScope]

theorem formula_rename_subst_poly {ζ : Type*} {n} (A : BF δ n) (f : δ → ε) (σ : ε → LA.Term ζ) :
    (A.rename f).subst σ = A.subst (fun x => σ (f x)) := by
  simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, subst_comp, Term.subst]
theorem formula_subst_rename_poly {ζ : Type*} {n} (A : BF δ n) (σ : δ → LA.Term ε) (f : ε → ζ) :
    (A.subst σ).rename f = A.subst (fun x => (σ x).relabel f) := by
  simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, subst_comp, term_subst_vars]
theorem liftContext_subst_poly (Γ : Context δ) (σ : δ → LA.Term ε) :
    (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ).image
      (fun A => A.subst (liftSubst σ 1)) =
      Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext (Γ.image (fun A => A.subst σ)) := by
  simp only [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext,
    Finset.image_image, Function.comp_def, formula_rename_subst_poly,
    formula_subst_rename_poly, liftSubst, Sum.elim_inl]
variable {Γ Δ : Context δ} {A B : Formula δ}
/-- The usual supplied-tree substitution, allowing distinct name universes. -/
def rawUniverseSubstitute (p : Derivation c true LA Γ A) (σ : δ → LA.Term ε) :
    Derivation c true LA (Γ.image (fun B => B.subst σ)) (A.subst σ) := by
  clear Δ B
  revert ε
  induction p with
  | assumption hA => intro ε σ; exact .assumption (Finset.mem_image.mpr ⟨_, hA, rfl⟩)
  | conjIntro _ _ ihA ihB =>
      intro ε σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_conj]
      exact .conjIntro (ihA σ) (ihB σ)
  | conjElimLeft _ ih =>
      intro ε σ
      exact .conjElimLeft (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_conj] using ih σ)
  | conjElimRight _ ih =>
      intro ε σ
      exact .conjElimRight (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_conj] using ih σ)
  | disjIntroLeft _ ih => intro ε σ; rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_disj]; exact .disjIntroLeft (ih σ)
  | disjIntroRight _ ih => intro ε σ; rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_disj]; exact .disjIntroRight (ih σ)
  | disjElim _ _ _ ihAB ihA ihB =>
      intro ε σ
      apply Derivation.disjElim (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_disj] using ihAB σ)
      · simpa only [Finset.image_insert] using ihA σ
      · simpa only [Finset.image_insert] using ihB σ
  | impIntro _ ih =>
      intro ε σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_impl]
      apply Derivation.impIntro
      simpa only [Finset.image_insert] using ih σ
  | impElim _ _ ihAB ihA =>
      intro ε σ
      exact .impElim (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_impl] using ihAB σ) (ihA σ)
  | negIntro _ ih =>
      intro ε σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg]
      apply Derivation.negIntro
      simpa only [Finset.image_insert, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum] using ih σ
  | negElim _ _ ihA ihnA =>
      intro ε σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum]
      exact .negElim (ihA σ) (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg] using ihnA σ)
  | falsumElim _ ih =>
      intro ε σ
      exact .falsumElim (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum] using ih σ)
  | classicalContradiction hc _ ih =>
      intro ε σ
      apply Derivation.classicalContradiction hc
      simpa only [Finset.image_insert, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum] using ih σ
  | allElim t _ ih =>
      intro ε σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst]
      exact .allElim (t.subst σ) (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all] using ih σ)
  | exIntro t _ ih =>
      intro ε σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex]
      apply Derivation.exIntro (t.subst σ)
      simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst] using ih σ
  | allIntro _ ih =>
      intro ε σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all]
      apply Derivation.allIntro
      simpa only [liftContext_subst_poly, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula_subst] using ih (liftSubst σ 1)
  | exElim _ _ ihEx ihB =>
      intro ε σ
      apply Derivation.exElim (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex] using ihEx σ)
      have hp := ihB (liftSubst σ 1)
      simp only [Finset.image_insert, liftContext_subst_poly] at hp
      simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula_subst, formula_rename_subst_poly, formula_subst_rename_poly,
        liftSubst, Sum.elim_inl] using hp
  | equalIntro t he =>
      intro ε σ
      rw [termEqual_subst_poly]
      exact Derivation.equalIntro (t.subst σ) he
  | equalElim φ s t he _ _ ihEq ihφ =>
      intro ε σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst]
      exact .equalElim (φ.subst σ) (s.subst σ) (t.subst σ) he
        (by simpa only [termEqual_subst_poly] using ihEq σ)
        (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst] using ihφ σ)

def rawUniverseRename (p : Derivation c true LA Γ A) (f : δ → ε) :
    Derivation c true LA (Γ.image (fun B => B.rename f)) (A.rename f) :=
  rawUniverseSubstitute p (fun x => .var (f x))

def publicUniverseRename {Γ : Context δ} {A : Formula δ}
    (p : Proof c true LA Γ A) (f : δ → ε) :
    Proof c true LA (Γ.image (fun B => B.rename f)) (A.rename f) := by
  let r : Derivation c true LA (Γ.image (fun B => B.rename (Sum.inl : δ → δ ⊕ ℕ)))
      (A.rename Sum.inl) := p
  simpa only [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof, Finset.image_image, rename_comp, Function.comp_def, Sum.map_inl] using
    rawUniverseRename r (Sum.map f id)

namespace TheoryCertificate
variable {T : Set Sentence} {Γ : Context δ} {A : Formula δ}
def universeRename (p : TheoryCertificate c T Γ A) (f : δ → ε) :
    TheoryCertificate c T (Γ.image (fun B => B.rename f)) (A.rename f) := by
  refine ⟨p.assumptions.image (fun B => B.rename f), ?_, publicUniverseRename p.derivation f⟩
  intro B hB
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
  rcases p.allowed C hC with hT | hΓ
  · left
    obtain ⟨θ, hθ, rfl⟩ := hT
    refine ⟨θ, hθ, ?_⟩
    rw [rename_comp]
    apply congrArg (fun g : Empty → ε => θ.rename g)
    funext x
    exact x.elim
  · exact Or.inr (Finset.mem_image.mpr ⟨C, hΓ, rfl⟩)
end TheoryCertificate
end UniverseRenaming

end
end Lemmatheca.ProofTheory.HeytingArithmetic
