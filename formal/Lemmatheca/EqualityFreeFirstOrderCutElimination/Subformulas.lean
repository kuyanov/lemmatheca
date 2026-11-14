import Lemmatheca.EqualityFreeFirstOrderCutElimination.Cut

/-! Scoped occurrences and actual term instances, indexed by each displayed
sequent's free-name type. No shape-only erasure is used. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder (ScopeSubst)
universe u v w w' w''
variable {L : Language.{u,v}} {α : Type w}
noncomputable section

/-- Selecting actual scoped children retains all slots encountered under binders. -/
inductive Nnf.ScopedSubformula : {n m : ℕ} → Nnf L α n → Nnf L α m → Prop
  | refl {n} (A : Nnf L α n) : ScopedSubformula A A
  | andLeft {n m} {C : Nnf L α n} {A B : Nnf L α m} :
      ScopedSubformula C A → ScopedSubformula C (.and A B)
  | andRight {n m} {C : Nnf L α n} {A B : Nnf L α m} :
      ScopedSubformula C B → ScopedSubformula C (.and A B)
  | orLeft {n m} {C : Nnf L α n} {A B : Nnf L α m} :
      ScopedSubformula C A → ScopedSubformula C (.or A B)
  | orRight {n m} {C : Nnf L α n} {A B : Nnf L α m} :
      ScopedSubformula C B → ScopedSubformula C (.or A B)
  | allBody {n m} {C : Nnf L α n} {A : Nnf L α (m+1)} :
      ScopedSubformula C A → ScopedSubformula C (.all A)
  | exBody {n m} {C : Nnf L α n} {A : Nnf L α (m+1)} :
      ScopedSubformula C A → ScopedSubformula C (.ex A)

/-- A genuine scoped occurrence with an actual term substitution witnessing its
literal equality to the displayed formula. -/
def InstantiatedSubformula (Γ : Sequent L α) (β : Type w') (D : Nnf L β 0) : Prop :=
  ∃ A ∈ Γ, ∃ n, ∃ C : Nnf L α n, C.ScopedSubformula A ∧
    ∃ σ : ScopeSubst L α β n 0, C.map σ = D

/-- Every formula in every displayed context, including parameter-changing
branches. The predicate is indexed by the actual name type at each node. -/
def CoreProof.Every (P : (δ : Type w) → Nnf L δ 0 → Prop) :
    {δ : Type w} → {Γ : Sequent L δ} → CoreProof L Γ → Prop
  | δ, Γ, p => (∀ A ∈ Γ, P δ A) ∧ match p with
    | .identity _ _ _ _ | .truth _ => True
    | .andIntro p q => p.Every P ∧ q.Every P
    | .orIntro p | .botIntro p | .allIntro _ p | .exIntro _ _ p => p.Every P

private theorem scopedTrans {n m k} {C : Nnf L α n} {B : Nnf L α m}
    {A : Nnf L α k} (hCB : C.ScopedSubformula B) (hBA : B.ScopedSubformula A) :
    C.ScopedSubformula A := by
  induction hBA with
  | refl => exact hCB
  | andLeft h ih => exact .andLeft (ih hCB)
  | andRight h ih => exact .andRight (ih hCB)
  | orLeft h ih => exact .orLeft (ih hCB)
  | orRight h ih => exact .orRight (ih hCB)
  | allBody h ih => exact .allBody (ih hCB)
  | exBody h ih => exact .exBody (ih hCB)

private theorem instantiated_map {δ : Type w'} {ε : Type w''}
    {Γ : Sequent L α} {A : Nnf L δ 0} (h : InstantiatedSubformula Γ δ A)
    (τ : ScopeSubst L δ ε 0 0) : InstantiatedSubformula Γ ε (A.map τ) := by
  rcases h with ⟨F, hF, n, C, hC, σ, rfl⟩
  exact ⟨F, hF, n, C, hC, (fun x => (σ x).subst τ), (C.map_comp σ τ).symm⟩

private theorem instantiated_rename {δ : Type w'} {ε : Type w''}
    {Γ : Sequent L α} {A : Nnf L δ 0} (h : InstantiatedSubformula Γ δ A)
    (f : δ → ε) : InstantiatedSubformula Γ ε (A.rename f) := by
  exact instantiated_map h _

private theorem instantiated_and {δ : Type w'} {Γ : Sequent L α}
    {A B : Nnf L δ 0} (h : InstantiatedSubformula Γ δ (.and A B)) :
    InstantiatedSubformula Γ δ A ∧ InstantiatedSubformula Γ δ B := by
  rcases h with ⟨F, hF, n, C, hC, σ, heq⟩
  cases C with
  | bot => cases heq
  | top => cases heq
  | pos R ts => cases heq
  | neg R ts => cases heq
  | or X Y => cases heq
  | all X => cases heq
  | ex X => cases heq
  | and X Y =>
    cases heq
    exact ⟨⟨F, hF, _, X, scopedTrans (.andLeft (.refl X)) hC, σ, rfl⟩,
      ⟨F, hF, _, Y, scopedTrans (.andRight (.refl Y)) hC, σ, rfl⟩⟩

private theorem instantiated_or {δ : Type w'} {Γ : Sequent L α}
    {A B : Nnf L δ 0} (h : InstantiatedSubformula Γ δ (.or A B)) :
    InstantiatedSubformula Γ δ A ∧ InstantiatedSubformula Γ δ B := by
  rcases h with ⟨F, hF, n, C, hC, σ, heq⟩
  cases C with
  | bot => cases heq
  | top => cases heq
  | pos R ts => cases heq
  | neg R ts => cases heq
  | and X Y => cases heq
  | all X => cases heq
  | ex X => cases heq
  | or X Y =>
    cases heq
    exact ⟨⟨F, hF, _, X, scopedTrans (.orLeft (.refl X)) hC, σ, rfl⟩,
      ⟨F, hF, _, Y, scopedTrans (.orRight (.refl Y)) hC, σ, rfl⟩⟩

private theorem instantiated_all_open {δ : Type w'} {Γ : Sequent L α}
    {B : Nnf L δ 1} (h : InstantiatedSubformula Γ δ (.all B)) :
    InstantiatedSubformula Γ (δ ⊕ Fin 1) B.toFormula := by
  rcases h with ⟨F, hF, n, C, hC, σ, heq⟩
  cases C with
  | bot => cases heq
  | top => cases heq
  | pos R ts => cases heq
  | neg R ts => cases heq
  | and X Y => cases heq
  | or X Y => cases heq
  | ex X => cases heq
  | all X =>
    cases heq
    refine ⟨F, hF, _, X, scopedTrans (.allBody (.refl X)) hC,
      (fun x => ((Lemmatheca.ProofTheory.FirstOrder.liftScope σ) x).subst
        (fun v => .var (.inl v))), ?_⟩
    exact (X.map_comp _ _).symm

private theorem instantiated_ex_instance {δ : Type w'} {Γ : Sequent L α}
    {B : Nnf L δ 1} (h : InstantiatedSubformula Γ δ (.ex B)) (t : L.Term δ) :
    InstantiatedSubformula Γ δ (B.instantiate t) := by
  rcases h with ⟨F, hF, n, C, hC, σ, heq⟩
  cases C with
  | bot => cases heq
  | top => cases heq
  | pos R ts => cases heq
  | neg R ts => cases heq
  | and X Y => cases heq
  | or X Y => cases heq
  | all X => cases heq
  | ex X =>
    cases heq
    refine ⟨F, hF, _, X, scopedTrans (.exBody (.refl X)) hC,
      (fun x => ((Lemmatheca.ProofTheory.FirstOrder.liftScope σ) x).subst
        (Sum.elim (fun v => .var (.inl v)) (fun _ => t.relabel Sum.inl))), ?_⟩
    exact (X.map_comp _ _).symm

private theorem instantiated_member {Γ : Sequent L α} {A : Nnf L α 0}
    (hA : A ∈ Γ) : InstantiatedSubformula Γ α A :=
  ⟨A, hA, 0, A, .refl A, Term.var, A.map_id⟩

private theorem analytic_from {Γ : Sequent L α} {δ : Type w} {Ξ : Sequent L δ}
    (p : CoreProof L Ξ) (hΞ : ∀ A ∈ Ξ, InstantiatedSubformula Γ δ A) :
    p.Every (fun ε A => InstantiatedSubformula Γ ε A) := by
  revert hΞ
  induction p with
  | identity R ts hp hn => intro hΞ; exact ⟨hΞ, True.intro⟩
  | truth htop => intro hΞ; exact ⟨hΞ, True.intro⟩
  | @andIntro δ Δ A B p q ihp ihq =>
    intro hΞ
    have hparts := instantiated_and (hΞ _ (Finset.mem_insert_self _ _))
    refine ⟨hΞ, ihp ?_, ihq ?_⟩
    · intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hparts.1
      · exact hΞ D (Finset.mem_insert_of_mem hD)
    · intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hparts.2
      · exact hΞ D (Finset.mem_insert_of_mem hD)
  | @orIntro δ Δ A B p ih =>
    intro hΞ
    have hparts := instantiated_or (hΞ _ (Finset.mem_insert_self _ _))
    refine ⟨hΞ, ih ?_⟩
    intro D hD
    rcases Finset.mem_insert.mp hD with rfl | hD
    · exact hparts.1
    rcases Finset.mem_insert.mp hD with rfl | hD
    · exact hparts.2
    · exact hΞ D (Finset.mem_insert_of_mem hD)
  | botIntro p ih =>
    intro hΞ
    exact ⟨hΞ, ih (fun D hD => hΞ D (Finset.mem_insert_of_mem hD))⟩
  | @allIntro δ Δ B p ih =>
    intro hΞ
    have hbody := instantiated_all_open (hΞ _ (Finset.mem_insert_self _ _))
    refine ⟨hΞ, ih ?_⟩
    intro D hD
    rcases Finset.mem_insert.mp hD with rfl | hD
    · exact hbody
    rcases Finset.mem_image.mp hD with ⟨E, hE, rfl⟩
    exact instantiated_rename (hΞ E (Finset.mem_insert_of_mem hE)) Sum.inl
  | @exIntro δ Δ B t p ih =>
    intro hΞ
    have hbody := instantiated_ex_instance (hΞ _ (Finset.mem_insert_self _ _)) t
    refine ⟨hΞ, ih ?_⟩
    intro D hD
    rcases Finset.mem_insert.mp hD with rfl | hD
    · exact hbody
    · exact hΞ D (Finset.mem_insert_of_mem hD)

private theorem raw_empty_impossible {δ : Type w} {Ξ : Sequent L δ}
    (p : CoreProof L Ξ) (hΞ : Ξ = ∅) : False := by
  cases p <;> simp_all

/-- Downward local-rule closure, at every actual extended name type. -/
theorem CoreProof.analytic {Γ : Sequent L α} (p : CoreProof L Γ) :
    p.Every (fun δ A => InstantiatedSubformula Γ δ A) := by
  exact analytic_from p (fun A hA => instantiated_member hA)

theorem CutProof.eliminate_analytic {Γ : Sequent L α} (p : CutProof L Γ) :
    p.eliminate.Every (fun δ A => InstantiatedSubformula Γ δ A) := by
  exact p.eliminate.analytic

/-- Public end formulas are represented as instances of the original displayed
formulas, even though internal trees also use reserved and eigenparameter names. -/
theorem proof_analytic {Γ : Sequent L α} (p : Proof Γ) :
    p.Every (fun δ A => InstantiatedSubformula Γ δ A) := by
  apply analytic_from p
  intro A hA
  rcases Finset.mem_image.mp hA with ⟨B, hB, rfl⟩
  exact instantiated_rename (instantiated_member hB) Sum.inl

theorem cutCertificate_eliminate_analytic {Γ : Sequent L α} (p : CutCertificate Γ) :
    p.eliminate.Every (fun δ A => InstantiatedSubformula Γ δ A) := by
  exact proof_analytic p.eliminate

/-- Primitive last-rule analysis after the actual cut transformation. -/
theorem no_raw_empty_with_cut : ¬ Nonempty (CutProof L (∅ : Sequent L α)) := by
  rintro ⟨p⟩
  exact raw_empty_impossible p.eliminate rfl

theorem no_raw_bot_with_cut : ¬ Nonempty (CutProof L ({Nnf.bot} : Sequent L α)) := by
  rintro ⟨p⟩
  exact raw_empty_impossible (p.eliminate.invertBot (Δ := ∅) (by simp)) rfl

theorem no_empty_with_cut : ¬ CutDerives (∅ : Sequent L α) := by
  unfold CutDerives CutCertificate renameContext
  simpa only [Finset.image_empty] using (no_raw_empty_with_cut (L := L) (α := α ⊕ ℕ))

theorem no_bot_with_cut : ¬ CutDerives ({Nnf.bot} : Sequent L α) := by
  unfold CutDerives CutCertificate renameContext
  simpa only [Finset.image_singleton, Nnf.rename, Nnf.subst, Nnf.map] using
    (no_raw_bot_with_cut (L := L) (α := α ⊕ ℕ))

end
end Lemmatheca.ProofTheory.ClassicalFirstOrder
