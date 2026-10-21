import Lemmatheca.PreservationConverses.PreservationBasic

open Lemmatheca.MathematicalLogic

/-! Elementary and signed diagrams can be combined when existential tuple information agrees. -/
namespace Lemmatheca.ModelTheory.Preservation
open FirstOrder FirstOrder.Language
universe u v w w'
variable {L : Language.{u, v}}

private theorem qf_fold {α : Type*} (s : List (L.Formula α))
    (h : ∀ φ ∈ s, φ.IsQF) : (s.foldr (· ⊓ ·) ⊤).IsQF := by
  induction s with
  | nil => exact BoundedFormula.IsQF.top
  | cons φ s ih => exact (h _ (by simp)).inf (ih (fun ψ hψ => h ψ (by simp [hψ])))

private theorem realize_fold {α : Type*} {M : Type*} [L.Structure M]
    (s : List (L.Formula α)) (a : α → M) :
    (s.foldr (· ⊓ ·) ⊤).Realize a ↔ ∀ φ ∈ s, φ.Realize a := by
  induction s with
  | nil => simp
  | cons φ s ih => simp [ih]

private theorem existential_exs {α : Type*} {k : ℕ} {φ : L.BoundedFormula α k}
    (h : φ.IsExistential) : φ.exs.IsExistential := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih h.ex

private theorem qf_iExs {α β : Type*} [Finite β] {φ : L.Formula (α ⊕ β)}
    (h : φ.IsQF) : (φ.iExs β).IsExistential := by
  unfold Formula.iExs
  exact existential_exs (h.relabel _).isExistential

/-- A finite list of quantifier-free facts, including a prescribed tuple, transfers
along inclusion of existential information. Only the finitely occurring names are bound. -/
private theorem finite_partial_realization
    {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
    [Nonempty M] [Nonempty N] {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : existentialInformation (L := L) b ⊆ existentialInformation (L := L) a)
    (s : Finset (L.Formula N)) (hq : ∀ φ ∈ s, φ.IsQF)
    (ht : ∀ φ ∈ s, φ.Realize id) :
    ∃ f : N → M, (∀ i, f (b i) = a i) ∧ ∀ φ ∈ s, φ.Realize f := by
  classical
  let facts : List (L.Formula (Fin n ⊕ N)) := s.toList.map (Formula.relabel Sum.inr)
  let equalities : List (L.Formula (Fin n ⊕ N)) :=
    (Finset.univ : Finset (Fin n)).toList.map fun i =>
      (Term.var (Sum.inr (b i))).equal (Term.var (Sum.inl i))
  let φ := facts.foldr (· ⊓ ·) ⊤ ⊓ equalities.foldr (· ⊓ ·) ⊤
  have hφ : φ.IsQF := by
    apply BoundedFormula.IsQF.inf
    · apply qf_fold
      intro ψ hψ
      obtain ⟨θ, hθ, rfl⟩ := List.mem_map.mp hψ
      exact (hq θ (Finset.mem_toList.mp hθ)).relabel _
    · apply qf_fold
      intro ψ hψ
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hψ
      exact (BoundedFormula.IsAtomic.equal _ _).isQF
  have htrue : φ.Realize (Sum.elim b id) := by
    change (facts.foldr (· ⊓ ·) ⊤ ⊓ equalities.foldr (· ⊓ ·) ⊤).Realize _
    rw [Formula.realize_inf]
    refine ⟨?_, ?_⟩
    · rw [realize_fold]
      intro ψ hψ
      obtain ⟨θ, hθ, rfl⟩ := List.mem_map.mp hψ
      rw [Formula.realize_relabel]
      convert ht θ (Finset.mem_toList.mp hθ) using 1
      rfl
    · rw [realize_fold]
      intro ψ hψ
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hψ
      simp
  let t : Finset N := φ.freeVarFinset.biUnion (fun x => x.elim (fun _ => ∅) singleton)
  let e := Fintype.equivFin t
  let r : N → Fin (Fintype.card t + 1) := fun x =>
    if hx : x ∈ t then (e ⟨x, hx⟩).castSucc else Fin.last _
  let c : Fin (Fintype.card t + 1) → N :=
    Fin.snoc (Subtype.val ∘ e.symm) (Classical.choice (inferInstance : Nonempty N))
  have hcr (x : N) (hx : x ∈ t) : c (r x) = x := by
    simp [c, r, hx]
  let χ : L.Formula (Fin n) := (φ.relabel (Sum.map id r)).iExs (Fin (Fintype.card t + 1))
  have hχ : χ.IsExistential := qf_iExs (hφ.relabel _)
  have hχN : χ.Realize b := by
    apply Formula.realize_iExs.mpr
    refine ⟨c, ?_⟩
    rw [Formula.realize_relabel]
    apply (Lemmatheca.MathematicalLogic.FirstOrderSemantics.formula_realize_agree
      φ _ (Sum.elim b id) default ?_).mpr htrue
    intro x hx
    cases x with
    | inl i => rfl
    | inr x =>
      apply hcr
      exact Finset.mem_biUnion.mpr ⟨Sum.inr x, hx, Finset.mem_singleton_self x⟩
  obtain ⟨f, hf⟩ := Formula.realize_iExs.mp (h ⟨hχ, hχN⟩).2
  rw [Formula.realize_relabel] at hf
  change (facts.foldr (· ⊓ ·) ⊤ ⊓ equalities.foldr (· ⊓ ·) ⊤).Realize _ at hf
  rw [Formula.realize_inf] at hf
  refine ⟨f ∘ r, ?_, ?_⟩
  · intro i
    have heq := (realize_fold equalities _).mp hf.2
      ((Term.var (Sum.inr (b i))).equal (Term.var (Sum.inl i))) (by simp [equalities])
    simpa [Function.comp_def] using heq
  · intro θ hθ
    have hh := (realize_fold facts _).mp hf.1 (θ.relabel Sum.inr)
      (List.mem_map.mpr ⟨θ, Finset.mem_toList.mpr hθ, rfl⟩)
    simpa [Formula.realize_relabel, Function.comp_def] using hh

/-- The conclusion identifies the images of the specified tuples under the actual maps. -/
theorem compatible_diagrams {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
    [Nonempty M] [Nonempty N] {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : existentialInformation (L := L) b ⊆ existentialInformation (L := L) a) :
    ∃ (C : Type (max u v w w')) (_ : L.Structure C) (_ : Nonempty C)
      (j : M ↪ₑ[L] C) (f : N ↪[L] C), ∀ i, f (b i) = j (a i) := by
  classical
  let K := L[[M ⊕ N]]
  let name := fun φ : L.Formula (M ⊕ N) => Formula.equivSentence φ
  let E : K.Theory := {γ | ∃ φ : L.Formula M,
    φ.Realize id ∧ γ = name (φ.relabel Sum.inl)}
  let D : K.Theory := {γ | ∃ φ : L.Formula N,
    φ.IsQF ∧ φ.Realize id ∧ γ = name (φ.relabel Sum.inr)}
  let Q : K.Theory := Set.range fun i : Fin n => name
    ((Term.var (Sum.inr (b i))).equal (Term.var (Sum.inl (a i))))
  let T := E ∪ D ∪ Q
  let eraseM : M ⊕ N → N := Sum.elim (fun _ => Classical.choice (inferInstance : Nonempty N)) id
  let strip : K.Sentence → L.Formula N := fun γ =>
    (Formula.equivSentence.symm γ).relabel eraseM
  have hstrip (φ : L.Formula N) : strip (name (φ.relabel Sum.inr)) = φ := by
    simp only [strip, name, Equiv.symm_apply_apply]
    rw [Lemmatheca.MathematicalLogic.FirstOrderProofs.formula_relabel_relabel]
    change φ.relabel id = φ
    rw [← Lemmatheca.MathematicalLogic.FirstOrderProofs.formula_subst_vars]
    exact Lemmatheca.MathematicalLogic.FirstOrderProofs.formula_subst_var φ
  have hsat : T.IsSatisfiable := by
    apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    intro Γ hΓ
    let s := (Γ.filter (fun γ => γ ∈ D)).image strip
    have hs : ∀ φ ∈ s, φ.IsQF ∧ φ.Realize id := by
      intro φ hφ
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hφ
      obtain ⟨θ, hθ, htθ, rfl⟩ := (Finset.mem_filter.mp hγ).2
      simpa only [hstrip] using And.intro hθ htθ
    obtain ⟨f, hfb, hf⟩ := finite_partial_realization a b h s
      (fun φ hφ => (hs φ hφ).1) (fun φ hφ => (hs φ hφ).2)
    let : K.Structure M := Diagrams.namedExpansion (L := L) (Sum.elim id f)
    let : (L.lhomWithConstants (M ⊕ N)).IsExpansionOn M :=
      Diagrams.namedExpansion_isExpansion (Sum.elim id f)
    have hmodel : M ⊨ (↑Γ : K.Theory) := by
      constructor
      intro γ hγ
      rcases hΓ hγ with (hE | hD) | hQ
      · obtain ⟨φ, htφ, rfl⟩ := hE
        rw [Formula.realize_equivSentence, Formula.realize_relabel]
        convert htφ using 1
        rfl
      · obtain ⟨φ, hqφ, htφ, heq⟩ := hD
        have hm : strip γ ∈ s := Finset.mem_image.mpr
          ⟨γ, Finset.mem_filter.mpr ⟨hγ, ⟨φ, hqφ, htφ, heq⟩⟩, rfl⟩
        have hh := hf (strip γ) hm
        rw [heq, hstrip] at hh
        rw [heq]
        rw [Formula.realize_equivSentence, Formula.realize_relabel]
        convert hh using 1
        rfl
      · obtain ⟨i, rfl⟩ := hQ
        rw [Formula.realize_equivSentence]
        change f (b i) = a i
        exact hfb i
    let := hmodel
    exact Theory.Model.isSatisfiable M
  let C := hsat.some
  let : L.Structure C := (L.lhomWithConstants (M ⊕ N)).reduct C
  let : (L.lhomWithConstants (M ⊕ N)).IsExpansionOn C := LHom.isExpansionOn_reduct _ _
  let : L[[M]].Structure C := (L.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)).reduct C
  let : (L.lhomWithConstants M).IsExpansionOn C := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hEC : C ⊨ L.elementaryDiagram M := by
    constructor
    intro γ hγ
    let φ := Formula.equivSentence.symm γ
    have hm : φ.Realize id := (Formula.realize_equivSentence_symm_con M γ).mpr hγ
    have hh := hsat.some.is_model.realize_of_mem (name (φ.relabel Sum.inl))
      (Or.inl (Or.inl ⟨φ, hm, rfl⟩))
    have hr := (Formula.realize_equivSentence C (φ.relabel Sum.inl)).mp hh
    rw [Formula.realize_relabel] at hr
    apply (Formula.realize_equivSentence_symm_con C γ).mp
    exact hr
  let := hEC
  let j : M ↪ₑ[L] C := ElementaryEmbedding.ofModelsElementaryDiagram L M C
  let : L[[N]].Structure C := (L.lhomWithConstantsMap (Sum.inr : N → M ⊕ N)).reduct C
  let : (L.lhomWithConstants N).IsExpansionOn C := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hDC : C ⊨ Diagrams.quantifierFreeDiagram L N := by
    constructor
    intro γ hγ
    let φ := Formula.equivSentence.symm γ
    have hq : φ.IsQF := by
      dsimp only [φ]
      obtain ⟨k, θ, c, heq, _, hq⟩ := Diagrams.sentence_is_namedFormula γ
      have ht := hq.mp hγ.1
      rw [heq]
      simp only [Diagrams.namedFormula, Equiv.symm_apply_apply]
      exact ht.relabel _
    have hm : φ.Realize id := (Formula.realize_equivSentence_symm_con N γ).mpr hγ.2
    have hh := hsat.some.is_model.realize_of_mem (name (φ.relabel Sum.inr))
      (Or.inl (Or.inr ⟨φ, hq, hm, rfl⟩))
    have hr := (Formula.realize_equivSentence C (φ.relabel Sum.inr)).mp hh
    rw [Formula.realize_relabel] at hr
    apply (Formula.realize_equivSentence_symm_con C γ).mp
    exact hr
  obtain ⟨f, hf⟩ := Diagrams.model_signed_iff_canonical_embedding.mp
    (Diagrams.models_signed_iff_models_quantifierFree.mpr hDC)
  refine ⟨C, inferInstance, inferInstance, j, f, ?_⟩
  intro i
  have hh := hsat.some.is_model.realize_of_mem
    (name ((Term.var (Sum.inr (b i))).equal (Term.var (Sum.inl (a i)))))
    (Or.inr ⟨i, rfl⟩)
  rw [hf]
  change (L.con (b i) : C) = (L.con (a i) : C)
  exact (Formula.realize_equivSentence C _).mp hh

end Lemmatheca.ModelTheory.Preservation
