import Lemmatheca.FirstOrderProofs.FirstOrderProofCore

/-! Finite classical natural deduction. `CoreProof` has only the logical and
equality rules. `Proof` permits an auxiliary reserve of names, as in the entry;
all structural operations below are syntactic proof-tree transformations. -/
namespace Lemmatheca.MathematicalLogic.FirstOrderProofs
open FirstOrder FirstOrder.Language
universe u v w
variable {L : Language.{u, v}} {α β : Type w}
noncomputable section
local instance {δ : Type w} : DecidableEq (L.Formula δ) := Classical.decEq _
local instance {δ : Type w} : DecidableEq δ := Classical.decEq _

/-- A finite proof in the displayed calculus may use an additional reserve of
names. Original assumptions and conclusion are embedded unchanged. -/
def Proof (L : Language.{u, v}) {α : Type w} (Γ : Finset (L.Formula α))
    (A : L.Formula α) : Prop :=
  CoreProof L (Γ.image (Formula.relabel (Sum.inl : α → α ⊕ ℕ)))
    (A.relabel Sum.inl)

theorem CoreProof.rename {Γ : Finset (L.Formula α)} {A : L.Formula α}
    (f : α → β) (h : CoreProof L Γ A) :
    CoreProof L (Γ.image (Formula.relabel f)) (A.relabel f) := by
  simpa only [formula_subst_vars] using h.substitute (fun x => .var (f x))

namespace Proof
variable {Γ Δ : Finset (L.Formula α)} {A B C : L.Formula α}

theorem assumption (hA : A ∈ Γ) : Proof L Γ A :=
  CoreProof.assumption (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
theorem conjIntro (hA : Proof L Γ A) (hB : Proof L Γ B) : Proof L Γ (A ⊓ B) :=
  CoreProof.conjIntro hA hB
theorem conjElimLeft (h : Proof L Γ (A ⊓ B)) : Proof L Γ A := CoreProof.conjElimLeft h
theorem conjElimRight (h : Proof L Γ (A ⊓ B)) : Proof L Γ B := CoreProof.conjElimRight h
theorem disjIntroLeft (h : Proof L Γ A) : Proof L Γ (A ⊔ B) := CoreProof.disjIntroLeft h
theorem disjIntroRight (h : Proof L Γ B) : Proof L Γ (A ⊔ B) := CoreProof.disjIntroRight h
theorem disjElim (h : Proof L Γ (A ⊔ B)) (hA : Proof L (insert A Γ) C)
    (hB : Proof L (insert B Γ) C) : Proof L Γ C := by
  exact CoreProof.disjElim (A := A.relabel Sum.inl) (B := B.relabel Sum.inl) h
    (by simpa only [Proof, Finset.image_insert] using hA)
    (by simpa only [Proof, Finset.image_insert] using hB)
theorem impIntro (h : Proof L (insert A Γ) B) : Proof L Γ (A.imp B) :=
  CoreProof.impIntro (A := A.relabel Sum.inl) (B := B.relabel Sum.inl) (by simpa only [Proof, Finset.image_insert] using h)
theorem impElim (h : Proof L Γ (A.imp B)) (hA : Proof L Γ A) : Proof L Γ B :=
  CoreProof.impElim h hA
theorem negIntro (h : Proof L (insert A Γ) ⊥) : Proof L Γ A.not :=
  CoreProof.negIntro (A := A.relabel Sum.inl) (by
    simpa only [Proof, Finset.image_insert, Formula.relabel, BoundedFormula.relabel_bot] using h)
theorem negElim (h : Proof L Γ A) (hn : Proof L Γ A.not) : Proof L Γ ⊥ :=
  CoreProof.negElim h hn
theorem falsumElim (h : Proof L Γ ⊥) : Proof L Γ A := CoreProof.falsumElim h
theorem classicalContradiction (h : Proof L (insert A.not Γ) ⊥) : Proof L Γ A :=
  CoreProof.classicalContradiction (A := A.relabel Sum.inl) (by
    simpa only [Proof, Finset.image_insert, Formula.relabel, BoundedFormula.relabel_not,
      BoundedFormula.relabel_bot] using h)
theorem equalIntro (t : L.Term α) : Proof L Γ (t.equal t) := by
  unfold Proof
  rw [← formula_subst_vars, formula_subst_equal, term_subst_vars]
  exact CoreProof.equalIntro (t.relabel Sum.inl)

theorem allElim {φ : L.BoundedFormula α 1} (t : L.Term α)
    (h : Proof L Γ φ.all) : Proof L Γ (instantiate φ t) := by
  unfold Proof at h ⊢
  rw [← formula_subst_vars, instantiate_subst, term_subst_vars]
  exact CoreProof.allElim (φ := φ.subst (fun x => .var (.inl x))) (t.relabel Sum.inl)
    (by simpa only [← formula_subst_vars, formula_subst_all] using h)

theorem exIntro {φ : L.BoundedFormula α 1} (t : L.Term α)
    (h : Proof L Γ (instantiate φ t)) : Proof L Γ φ.ex := by
  unfold Proof at h ⊢
  rw [← formula_subst_vars, formula_subst_ex]
  apply CoreProof.exIntro (t.relabel Sum.inl)
  simpa only [← formula_subst_vars, instantiate_subst, term_subst_vars] using h

/-- Fresh eigenparameters are transported across the reserve of auxiliary names. -/
theorem allIntro {φ : L.BoundedFormula α 1}
    (h : Proof L (α := α ⊕ Fin 1) (liftContext Γ) φ.toFormula) : Proof L Γ φ.all := by
  let f : (α ⊕ Fin 1) ⊕ ℕ → (α ⊕ ℕ) ⊕ Fin 1 :=
    Sum.elim (Sum.map Sum.inl id) (fun i => .inl (.inr i))
  have hp := CoreProof.rename f h
  unfold Proof
  rw [← formula_subst_vars, formula_subst_all]
  apply CoreProof.allIntro
  have hv : liftSubst (fun x : α => (Term.var (.inl x) : L.Term (α ⊕ ℕ))) 1 =
      fun z => .var (f (.inl z)) := by
    funext z
    cases z <;> rfl
  simpa only [Proof, liftContext, Finset.image_image, formula_relabel_relabel,
    toFormula_subst, hv, formula_subst_vars, Function.comp_def, f,
    Sum.elim_inl, Sum.map_inl] using hp

theorem exElim {φ : L.BoundedFormula α 1}
    (hEx : Proof L Γ φ.ex)
    (hB : Proof L (insert φ.toFormula (liftContext Γ)) (C.relabel Sum.inl)) :
    Proof L Γ C := by
  let f : (α ⊕ Fin 1) ⊕ ℕ → (α ⊕ ℕ) ⊕ Fin 1 :=
    Sum.elim (Sum.map Sum.inl id) (fun i => .inl (.inr i))
  have hp := CoreProof.rename f hB
  unfold Proof at hEx ⊢
  apply CoreProof.exElim (φ := φ.subst (fun x => .var (.inl x)))
    (by simpa only [← formula_subst_vars, formula_subst_ex] using hEx)
  have hv : liftSubst (fun x : α => (Term.var (.inl x) : L.Term (α ⊕ ℕ))) 1 =
      fun z => .var (f (.inl z)) := by
    funext z
    cases z <;> rfl
  simpa only [Proof, liftContext, Finset.image_insert, Finset.image_image,
    formula_relabel_relabel, toFormula_subst, hv, formula_subst_vars,
    Function.comp_def, f, Sum.elim_inl, Sum.map_inl] using hp

theorem equalElim (φ : L.BoundedFormula α 1) (s t : L.Term α)
    (he : Proof L Γ (s.equal t)) (hp : Proof L Γ (instantiate φ s)) :
    Proof L Γ (instantiate φ t) := by
  unfold Proof at he hp ⊢
  rw [← formula_subst_vars, instantiate_subst, term_subst_vars]
  apply CoreProof.equalElim (φ.subst (fun x => .var (.inl x))) (s.relabel Sum.inl) (t.relabel Sum.inl)
  · simpa only [← formula_subst_vars, formula_subst_equal, term_subst_vars] using he
  · simpa only [← formula_subst_vars, instantiate_subst, term_subst_vars] using hp

theorem weakening (h : Proof L Γ A) (hsub : Γ ⊆ Δ) : Proof L Δ A :=
  CoreProof.weakening h (Finset.image_subset_image hsub)

theorem cut (hA : Proof L Γ A) (hB : Proof L (insert A Δ) B) :
    Proof L (Γ ∪ Δ) B :=
  impElim (weakening (impIntro hB) Finset.subset_union_right)
    (weakening hA Finset.subset_union_left)

theorem substitute (σ : α → L.Term β) (h : Proof L Γ A) :
    Proof L (Γ.image (fun φ => φ.subst σ)) (A.subst σ) := by
  let τ : α ⊕ ℕ → L.Term (β ⊕ ℕ) :=
    Sum.elim (fun x => (σ x).relabel Sum.inl) (fun i => .var (.inr i))
  have hp := CoreProof.substitute h τ
  simpa only [Proof, Finset.image_image, Function.comp_def, formula_relabel_subst,
    formula_subst_relabel, τ, Sum.elim_inl] using hp

theorem rename (f : α → β) (h : Proof L Γ A) :
    Proof L (Γ.image (Formula.relabel f)) (A.relabel f) := by
  simpa only [formula_subst_vars] using substitute (fun x => .var (f x)) h

/-- The named-eigenparameter version of universal introduction follows by
renaming that fresh name to the protected slot. -/
theorem allIntroParameter {φ : L.BoundedFormula α 1} (c : α)
    (hcφ : c ∉ φ.freeVarFinset) (hcΓ : ∀ B ∈ Γ, c ∉ B.freeVarFinset)
    (h : Proof L Γ (instantiate φ (.var c))) : Proof L Γ φ.all := by
  let σ : α → L.Term (α ⊕ Fin 1) := fun x =>
    if x = c then .var (.inr 0) else .var (.inl x)
  have hφ : φ.subst σ = φ.subst (fun x => .var (.inl x)) := by
    apply formula_subst_agree
    intro x hx
    have hxc : x ≠ c := fun he => hcφ (he ▸ hx)
    simp only [σ, ite_eq_right hxc]
  have hΓ : Γ.image (fun B => B.subst σ) = liftContext Γ := by
    apply Finset.image_congr
    intro B hB
    rw [← formula_subst_vars]
    apply formula_subst_agree
    intro x hx
    have hxc : x ≠ c := fun he => hcΓ B hB (he ▸ hx)
    simp only [σ, ite_eq_right hxc]
  have hσc : σ c = .var (.inr 0) := by simp [σ]
  have hp := substitute σ h
  rw [hΓ] at hp
  simp only [instantiate_subst, hφ, Term.subst, hσc, instantiate_lifted] at hp
  exact allIntro hp

/-- The existential witness may likewise use an already available name which
is absent from the remaining assumptions, quantified body and conclusion. -/
theorem exElimParameter {φ : L.BoundedFormula α 1} (c : α)
    (hcφ : c ∉ φ.freeVarFinset) (hcΓ : ∀ B ∈ Γ, c ∉ B.freeVarFinset)
    (hcC : c ∉ C.freeVarFinset) (hEx : Proof L Γ φ.ex)
    (hB : Proof L (insert (instantiate φ (.var c)) Γ) C) : Proof L Γ C := by
  let σ : α → L.Term (α ⊕ Fin 1) := fun x =>
    if x = c then .var (.inr 0) else .var (.inl x)
  have hφ : φ.subst σ = φ.subst (fun x => .var (.inl x)) := by
    apply formula_subst_agree
    intro x hx
    have hxc : x ≠ c := fun he => hcφ (he ▸ hx)
    simp only [σ, ite_eq_right hxc]
  have hΓ : Γ.image (fun B => B.subst σ) = liftContext Γ := by
    apply Finset.image_congr
    intro B hB
    rw [← formula_subst_vars]
    apply formula_subst_agree
    intro x hx
    have hxc : x ≠ c := fun he => hcΓ B hB (he ▸ hx)
    simp only [σ, ite_eq_right hxc]
  have hC : C.subst σ = C.relabel Sum.inl := by
    rw [← formula_subst_vars]
    apply formula_subst_agree
    intro x hx
    have hxc : x ≠ c := fun he => hcC (he ▸ hx)
    simp only [σ, ite_eq_right hxc]
  apply exElim hEx
  have hσc : σ c = .var (.inr 0) := by simp [σ]
  have hp := substitute σ hB
  simpa only [Finset.image_insert, hΓ, instantiate_subst, hφ, Term.subst,
    hσc, instantiate_lifted, hC] using hp

/-- Reflect an injective change of original names by replacing any names outside
its range with an auxiliary name. This is substitution in the core calculus. -/
theorem parameterCloseMap (f : α → β) (hf : Function.Injective f)
    (h : Proof L (Γ.image (Formula.relabel f)) (A.relabel f)) : Proof L Γ A := by
  classical
  let r : β → L.Term (α ⊕ ℕ) := fun y =>
    if hy : ∃ x, f x = y then .var (.inl (Classical.choose hy)) else .var (.inr 0)
  have hr (x : α) : r (f x) = .var (.inl x) := by
    simp only [r, dite_eq_left (show ∃ z, f z = f x from ⟨x, rfl⟩)]
    rw [hf (Classical.choose_spec (show ∃ z, f z = f x from ⟨x, rfl⟩))]
  let τ : β ⊕ ℕ → L.Term (α ⊕ ℕ) := Sum.elim r (fun i => .var (.inr i))
  have hp := CoreProof.substitute h τ
  simpa only [Proof, Finset.image_image, Function.comp_def, formula_relabel_subst,
    τ, Sum.elim_inl, hr, formula_subst_vars] using hp

theorem parameterClose
    (h : Proof L (α := β ⊕ α) (Γ.image (Formula.relabel Sum.inr)) (A.relabel Sum.inr)) :
    Proof L Γ A := parameterCloseMap Sum.inr Sum.inr_injective h

/-- Replace one selected member of a finite tuple, keeping all other terms
fixed. The unary body captures only the selected coordinate. -/
theorem replaceSlot {n : ℕ} (φ : L.BoundedFormula α n)
    (ts : Fin n → L.Term α) (i : Fin n) (t : L.Term α)
    (he : Proof L Γ ((ts i).equal t)) (hp : Proof L Γ (instantiateSlots φ ts)) :
    Proof L Γ (instantiateSlots φ (Function.update ts i t)) := by
  let σ : α ⊕ Fin n → L.Term (α ⊕ Fin 1) :=
    Sum.elim (fun x => .var (.inl x))
      (fun j => if j = i then .var (.inr 0) else (ts j).relabel Sum.inl)
  let ψ : L.BoundedFormula α 1 := BoundedFormula.relabel id (φ.toFormula.subst σ)
  have hinst (u : L.Term α) :
      instantiate ψ u = instantiateSlots φ (Function.update ts i u) := by
    change instantiate (BoundedFormula.relabel id (φ.toFormula.subst σ)) u = _
    rw [instantiate_capture, formula_subst_subst]
    unfold instantiateSlots
    congr 1
    funext x
    cases x with
    | inl x => rfl
    | inr j =>
        by_cases hj : j = i
        · subst j
          simp [σ, Term.subst]
        · simp [σ, hj, term_subst_relabel]
  rw [← hinst]
  apply equalElim ψ (ts i) t he
  have hsame : Function.update ts i (ts i) = ts := Function.update_eq_self i ts
  simpa only [hinst, hsame] using hp

/-- Simultaneous equality replacement is a finite iteration of the displayed
single-object equality-elimination rule. -/
theorem equalSlots {n : ℕ} (φ : L.BoundedFormula α n)
    (ts us : Fin n → L.Term α) (he : ∀ i, Proof L Γ ((ts i).equal (us i)))
    (hp : Proof L Γ (instantiateSlots φ ts)) : Proof L Γ (instantiateSlots φ us) := by
  have hfin (s : Finset (Fin n)) :
      Proof L Γ (instantiateSlots φ (fun i => if i ∈ s then us i else ts i)) := by
    induction s using Finset.induction_on with
    | empty => simpa using hp
    | @insert i s hi ih =>
        let vs : Fin n → L.Term α := fun j => if j ∈ s then us j else ts j
        have hvi : vs i = ts i := by simp [vs, hi]
        have hnext := replaceSlot φ vs i (us i)
          (by simpa only [hvi] using he i) ih
        have hupdate : Function.update vs i (us i) =
            fun j => if j ∈ insert i s then us j else ts j := by
          funext j
          by_cases hji : j = i
          · subst j
            simp
          · simp [vs, hji]
        simpa only [hupdate] using hnext
  simpa only [Finset.mem_univ, ite_true] using hfin Finset.univ

end Proof

/-- An arbitrary theory derives a formula using a finite collection of its axioms. -/
def Derives (T : Set (L.Formula α)) (A : L.Formula α) : Prop :=
  ∃ Γ : Finset (L.Formula α), (↑Γ : Set (L.Formula α)) ⊆ T ∧ Proof L Γ A
/-- Syntactic consistency is absence of a derivation of falsity. -/
def Consistent (T : Set (L.Formula α)) : Prop := ¬ Derives T ⊥
/-- Implication over a theory allows its antecedent as an additional assumption. -/
def ImpliesOver (T : Set (L.Formula α)) (A B : L.Formula α) : Prop := Derives (insert A T) B
/-- Equivalence over a theory requires both syntactic implications. -/
def EquivalentOver (T : Set (L.Formula α)) (A B : L.Formula α) : Prop :=
  ImpliesOver T A B ∧ ImpliesOver T B A
/-- A schema supplies one sentence for each item of indexing data. -/
def schemaTheory {ι : Type*} (s : ι → L.Sentence) : L.Theory := Set.range s

theorem Proof.sound {M : Type*} [L.Structure M] [Nonempty M] {Γ : Finset (L.Formula α)}
    {A : L.Formula α} (h : Proof L Γ A) (a : α → M)
    (hΓ : ∀ B ∈ Γ, B.Realize a) : A.Realize a := by
  let m : M := Classical.choice inferInstance
  have hp := CoreProof.sound h (Sum.elim a (fun _ => m)) (by
    intro C hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
    simpa using hΓ B hB)
  simpa using hp

theorem derives_sound {M : Type*} [L.Structure M] [Nonempty M] {T : Set (L.Formula α)}
    {A : L.Formula α} (h : Derives T A) (a : α → M)
    (hT : ∀ B ∈ T, B.Realize a) : A.Realize a := by
  rcases h with ⟨Γ, hΓ, hp⟩
  exact hp.sound a (fun B hB => hT B (hΓ hB))

theorem derives_assumption {T : Set (L.Formula α)} {A : L.Formula α}
    (hA : A ∈ T) : Derives T A := by
  exact ⟨{A}, by simpa using hA, .assumption (by simp)⟩
theorem derives_mono {T U : Set (L.Formula α)} {A : L.Formula α}
    (h : Derives T A) (hTU : T ⊆ U) : Derives U A := by
  rcases h with ⟨Γ, hΓ, hp⟩
  exact ⟨Γ, hΓ.trans hTU, hp⟩
theorem derives_cut {T U : Set (L.Formula α)} {A B : L.Formula α}
    (hA : Derives T A) (hB : Derives (insert A U) B) : Derives (T ∪ U) B := by
  rcases hA with ⟨Γ, hΓ, hpA⟩
  rcases hB with ⟨Δ, hΔ, hpB⟩
  refine ⟨Γ ∪ Δ.erase A, ?_, .cut hpA (.weakening hpB ?_)⟩
  · intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact Or.inl (hΓ hC)
    · have hc := Finset.mem_erase.mp hC
      exact Or.inr ((Set.mem_insert_iff.mp (hΔ hc.2)).resolve_left hc.1)
  · intro C hC
    by_cases hCA : C = A
    · simp [hCA]
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hCA, hC⟩)
theorem derives_imp_iff {T : Set (L.Formula α)} {A B : L.Formula α} :
    Derives T (A.imp B) ↔ Derives (insert A T) B := by
  constructor
  · rintro ⟨Γ, hΓ, hp⟩
    refine ⟨insert A Γ, ?_, .impElim (.weakening hp (Finset.subset_insert _ _))
      (.assumption (by simp))⟩
    intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (hΓ hC)
  · rintro ⟨Γ, hΓ, hp⟩
    refine ⟨Γ.erase A, ?_, .impIntro (.weakening hp ?_)⟩
    · intro C hC
      have hc := Finset.mem_erase.mp hC
      exact (Set.mem_insert_iff.mp (hΓ hc.2)).resolve_left hc.1
    · intro C hC
      by_cases hCA : C = A
      · simp [hCA]
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hCA, hC⟩)
theorem derives_explosion {T : Set (L.Formula α)} {A : L.Formula α}
    (h : Derives T ⊥) : Derives T A := by
  rcases h with ⟨Γ, hΓ, hp⟩
  exact ⟨Γ, hΓ, .falsumElim hp⟩
theorem derives_iff_not_consistent_neg {T : Set (L.Formula α)} {A : L.Formula α} :
    Derives T A ↔ ¬ Consistent (insert A.not T) := by
  classical
  constructor
  · rintro ⟨Γ, hΓ, hp⟩ hcon
    apply hcon
    refine ⟨insert A.not Γ, ?_, .negElim (.weakening hp (Finset.subset_insert _ _))
      (.assumption (by simp))⟩
    intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (hΓ hC)
  · intro hn
    obtain ⟨Γ, hΓ, hp⟩ := Classical.not_not.mp hn
    refine ⟨Γ.erase A.not, ?_, .classicalContradiction (.weakening hp ?_)⟩
    · intro C hC
      have hc := Finset.mem_erase.mp hC
      exact (Set.mem_insert_iff.mp (hΓ hc.2)).resolve_left hc.1
    · intro C hC
      by_cases hCA : C = A.not
      · simp [hCA]
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hCA, hC⟩)
theorem derives_finite_support {T : Set (L.Formula α)} {A : L.Formula α}
    (h : Derives T A) : ∃ Γ : Finset (L.Formula α),
      (↑Γ : Set (L.Formula α)) ⊆ T ∧ Derives (↑Γ) A := by
  rcases h with ⟨Γ, hΓ, hp⟩
  exact ⟨Γ, hΓ, Γ, Set.Subset.rfl, hp⟩
theorem consistent_iff_finite {T : Set (L.Formula α)} :
    Consistent T ↔ ∀ Γ : Finset (L.Formula α), (↑Γ : Set (L.Formula α)) ⊆ T →
      Consistent (↑Γ : Set (L.Formula α)) := by
  constructor
  · intro hT Γ hΓ hp
    exact hT (derives_mono hp hΓ)
  · intro hfin hp
    rcases derives_finite_support hp with ⟨Γ, hΓ, hproof⟩
    exact hfin Γ hΓ hproof
theorem consistent_of_model {M : Type*} [L.Structure M] [Nonempty M]
    {T : Set (L.Formula α)} (a : α → M) (hT : ∀ B ∈ T, B.Realize a) : Consistent T := by
  intro hp
  exact derives_sound hp a hT
theorem theory_consistent_of_model {M : Type*} [L.Structure M] [Nonempty M] {T : L.Theory}
    (hT : M ⊨ T) : Consistent T := by
  exact consistent_of_model (default : Empty → M) (fun B hB => hT.realize_of_mem B hB)
theorem empty_theory_consistent (L : Language.{u, v}) : Consistent (∅ : L.Theory) := by
  let : L.Structure Unit := ⟨fun _ _ => (), fun _ _ => False⟩
  exact consistent_of_model (M := Unit) Empty.elim (by simp)
theorem impliesOver_realize {M : Type*} [L.Structure M] [Nonempty M]
    {T : L.Theory} {A B : L.Sentence}
    (h : ImpliesOver T A B) (hT : M ⊨ T) (hA : M ⊨ A) : M ⊨ B := by
  apply derives_sound h (default : Empty → M)
  intro C hC
  rcases Set.mem_insert_iff.mp hC with rfl | hC
  · exact hA
  · exact hT.realize_of_mem C hC
theorem equivalentOver_realize {M : Type*} [L.Structure M] [Nonempty M]
    {T : L.Theory} {A B : L.Sentence}
    (h : EquivalentOver T A B) (hT : M ⊨ T) : (M ⊨ A ↔ M ⊨ B) := by
  exact ⟨fun hA => impliesOver_realize h.1 hT hA, fun hB => impliesOver_realize h.2 hT hB⟩
theorem inconsistent_equivalent {T : Set (L.Formula α)} (hT : ¬ Consistent T)
    (A B : L.Formula α) : EquivalentOver T A B := by
  classical
  have hf : Derives T ⊥ := Classical.not_not.mp hT
  exact ⟨derives_explosion (derives_mono hf (Set.subset_insert _ _)),
    derives_explosion (derives_mono hf (Set.subset_insert _ _))⟩
@[simp] private theorem subst_relabel {γ : Type*} (t : L.Term α)
    (f : α → β) (σ : β → L.Term γ) :
    (t.relabel f).subst σ = t.subst (fun x => σ (f x)) := by
  induction t with
  | var x => rfl
  | func f ts ih => simp [Term.relabel, Term.subst, ih]

@[simp] private theorem subst_vars (t : L.Term α) (f : α → β) :
    t.subst (fun x => .var (f x)) = t.relabel f := by
  induction t with
  | var x => rfl
  | func f ts ih => simp [Term.relabel, Term.subst, ih]

theorem Proof.equal_symmetry {Γ : Finset (L.Formula α)} {s t : L.Term α}
    (h : Proof L Γ (s.equal t)) : Proof L Γ (t.equal s) := by
  let φ : L.BoundedFormula α 1 := (.var (.inr 0) : L.Term (α ⊕ Fin 1)).bdEqual
    (s.relabel Sum.inl)
  have hs : instantiate φ s = s.equal s := by
    simp [φ, instantiate, BoundedFormula.toFormula, Term.bdEqual,
      BoundedFormula.subst, BoundedFormula.mapTermRel, Term.equal,
      Term.subst, Term.relabel]
  have ht : instantiate φ t = t.equal s := by
    simp [φ, instantiate, BoundedFormula.toFormula, Term.bdEqual,
      BoundedFormula.subst, BoundedFormula.mapTermRel, Term.equal,
      Term.subst, Term.relabel]
  rw [← ht]
  exact .equalElim φ s t h (hs ▸ .equalIntro s)
theorem Proof.equal_transitivity {Γ : Finset (L.Formula α)} {s t r : L.Term α}
    (hst : Proof L Γ (s.equal t)) (htr : Proof L Γ (t.equal r)) :
    Proof L Γ (s.equal r) := by
  let φ : L.BoundedFormula α 1 := (s.relabel Sum.inl).bdEqual (.var (.inr 0))
  have ht : instantiate φ t = s.equal t := by
    simp [φ, instantiate, BoundedFormula.toFormula, Term.bdEqual,
      BoundedFormula.subst, BoundedFormula.mapTermRel, Term.equal,
      Term.subst, Term.relabel]
  have hr : instantiate φ r = s.equal r := by
    simp [φ, instantiate, BoundedFormula.toFormula, Term.bdEqual,
      BoundedFormula.subst, BoundedFormula.mapTermRel, Term.equal,
      Term.subst, Term.relabel]
  rw [← hr]
  exact .equalElim φ t r htr (ht ▸ hst)

/-- A unary predicate applied to the distinguished quantified slot. -/
def unaryBody (P : L.Relations 1) : L.BoundedFormula α 1 :=
  P.boundedFormula₁ (.var (.inr 0))

theorem witness_implication (P Q : L.Relations 1) :
    Derives ({((unaryBody P).imp (unaryBody Q)).all, (unaryBody P).ex} : L.Theory)
      (unaryBody Q).ex := by
  let Γ : Finset L.Sentence := {((unaryBody P).imp (unaryBody Q)).all, (unaryBody P).ex}
  refine ⟨Γ, by simp [Γ], ?_⟩
  apply Proof.exElim (φ := unaryBody P)
  · exact .assumption (by simp [Γ])
  · let c : L.Term (Empty ⊕ Fin 1) := .var (.inr 0)
    let Δ := insert (unaryBody P).toFormula (liftContext Γ)
    have hAll : Proof L Δ (((unaryBody P : L.BoundedFormula (Empty ⊕ Fin 1) 1).imp
        (unaryBody Q)).all) := by
      have hp : Proof L Δ
          (Formula.relabel Sum.inl (((unaryBody P).imp (unaryBody Q)).all : L.Sentence)) :=
        .assumption (Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨((unaryBody P).imp (unaryBody Q)).all, by simp [Γ], rfl⟩))
      simpa [unaryBody, Formula.relabel, BoundedFormula.relabel,
        BoundedFormula.mapTermRel, BoundedFormula.relabelAux,
        Relations.boundedFormula₁, Relations.boundedFormula,
        Term.relabel, Function.comp_def, finSumFinEquiv,
        Matrix.cons_fin_one] using hp
    have hP : Proof L Δ (instantiate (unaryBody P) c) := by
      have hp : Proof L Δ (unaryBody P).toFormula := .assumption (by simp [Δ])
      simpa [unaryBody, instantiate, BoundedFormula.toFormula, BoundedFormula.subst,
        BoundedFormula.mapTermRel, Relations.boundedFormula₁, Relations.boundedFormula,
        Relations.formula, Term.subst, Term.relabel, c] using hp
    have hQ : Proof L Δ (instantiate (unaryBody Q) c) :=
      Proof.impElim (Proof.allElim c hAll) hP
    have hp := Proof.exIntro (φ := unaryBody Q) c hQ
    simpa [Δ, unaryBody, Formula.relabel, BoundedFormula.relabel, BoundedFormula.toFormula,
      BoundedFormula.mapTermRel, BoundedFormula.relabelAux, BoundedFormula.ex,
      BoundedFormula.not, Bot.bot, Relations.boundedFormula₁, Relations.boundedFormula, Relations.formula,
      Term.relabel, Function.comp_def, finSumFinEquiv,
        Matrix.cons_fin_one] using hp

theorem Proof.relationDiagonal_exists {Γ : Finset (L.Formula α)}
    (R : L.Relations 2) (c : L.Term α) (h : Proof L Γ (R.formula₂ c c)) :
    Proof L Γ (R.boundedFormula₂ (c.relabel Sum.inl) (.var (.inr 0)) :
      L.BoundedFormula α 1).ex := by
  apply Proof.exIntro c
  have he : instantiate (R.boundedFormula₂ (c.relabel Sum.inl) (.var (.inr 0)) :
      L.BoundedFormula α 1) c = R.formula₂ c c := by
    simp only [instantiate, BoundedFormula.toFormula, BoundedFormula.subst,
      BoundedFormula.mapTermRel, Relations.boundedFormula₂, Relations.boundedFormula,
      Relations.formula₂, Relations.formula]
    congr 1
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => nomatch j)) i
    · simp [Term.relabel]
    · simp [Term.subst, Term.relabel]
  rw [he]
  exact h

end
end Lemmatheca.MathematicalLogic.FirstOrderProofs
