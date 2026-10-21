import Lemmatheca.InterpretingTheories.InterpretingTheories

namespace Lemmatheca.MathematicalLogic.InterpretingTheories
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v u' v' u'' v'' w z
noncomputable section
variable {L : Language.{u,v}} {K : Language.{u',v'}} {H : Language.{u'',v''}}
namespace InterpretationData

/-- Composition uses translated defining formulas and intersects the two guards. -/
def comp (I : InterpretationData L K) (J : InterpretationData K H) : InterpretationData L H where
  domain := J.domain ⊓ J.translate I.domain
  functionGraph f := J.translate (I.functionGraph f)
  relationFormula R := J.translate (I.relationFormula R)

variable (I : InterpretationData L K) (J : InterpretationData K H)
variable {M : Type w} [H.Structure M]

/-- The specified nested-subtype map keeps exactly the same ambient element. -/
def compDomainEquiv (hJ : J.GoodGraphs M) :
    letI := J.inducedStructure hJ
    (I.comp J).Domain M ≃ I.Domain (J.Domain M) := by
  letI := J.inducedStructure hJ
  refine {
    toFun := fun x => ?_
    invFun := fun x => ?_
    left_inv := ?_
    right_inv := ?_
  }
  · have hx : J.domain.Realize (fun _ => x.val) ∧
        (J.translate I.domain).Realize (fun _ => x.val) := Formula.realize_inf.mp x.property
    exact ⟨⟨x.val, hx.1⟩,
      (realize_translate hJ I.domain (fun _ => ⟨x.val, hx.1⟩)).mp hx.2⟩
  · exact ⟨x.val.val, Formula.realize_inf.mpr ⟨x.val.property,
      (realize_translate hJ I.domain (fun _ => x.val)).mpr x.property⟩⟩
  · intro x
    rfl
  · intro x
    rfl

theorem compDomainEquiv_value (hJ : J.GoodGraphs M) (x : (I.comp J).Domain M) :
    ((I.compDomainEquiv J hJ x).val).val = x.val := by
  rfl


private theorem outer_sum_values {β γ : Type*}
    (v : β → J.Domain M) (xs : γ → J.Domain M) :
    (fun a => (Sum.elim v xs a).val) =
      Sum.elim (fun a => (v a).val) (fun i => (xs i).val) := by
  funext a
  cases a <;> rfl

private theorem comp_graph_iff (hJ : J.GoodGraphs M) {n : ℕ} (f : L.Functions n)
    (x : Fin n → (I.comp J).Domain M) (y : J.Domain M) :
    letI := J.inducedStructure hJ
    ((I.comp J).guardedGraph f).Realize
      (Sum.elim (fun i => (x i).val) (fun _ => y.val)) ↔
      (I.guardedGraph f).Realize
        (Sum.elim (fun i => (I.compDomainEquiv J hJ (x i)).val) (fun _ => y)) := by
  let := J.inducedStructure hJ
  have hd := realize_translate hJ I.domain (fun _ : Unit => y)
  have hg := realize_translate hJ (I.functionGraph f)
    (Sum.elim (fun i => (I.compDomainEquiv J hJ (x i)).val) (fun _ : Unit => y))
  rw [outer_sum_values J] at hg
  have hv : (fun i => ((I.compDomainEquiv J hJ (x i)).val).val) =
      (fun i => (x i).val) := funext (fun i => I.compDomainEquiv_value J hJ (x i))
  rw [hv] at hg
  simp only [guardedGraph, comp, Formula.realize_inf, Formula.realize_relabel,
    Sum.elim_comp_inr]
  change ((J.domain.Realize (fun _ => y.val) ∧
    (J.translate I.domain).Realize (fun _ => y.val)) ∧
    (J.translate (I.functionGraph f)).Realize
      (Sum.elim (fun i => (x i).val) (fun _ => y.val))) ↔
    I.domain.Realize (fun _ => y) ∧ (I.functionGraph f).Realize
      (Sum.elim (fun i => (I.compDomainEquiv J hJ (x i)).val) (fun _ => y))
  rw [hd, hg]
  simp only [y.property, true_and]

theorem graphs_comp (hJ : J.GoodGraphs M)
    (hI : letI := J.inducedStructure hJ; I.GoodGraphs (J.Domain M)) :
    (I.comp J).GoodGraphs M := by
  let := J.inducedStructure hJ
  intro n f x
  obtain ⟨z, hz, hu⟩ := hI n f (fun i => I.compDomainEquiv J hJ (x i))
  refine ⟨z.val, (I.comp_graph_iff J hJ f x z).mpr hz, ?_⟩
  intro y hy
  have hD : (I.comp J).domain.Realize (fun _ => y) := by
    simpa only [Formula.realize_relabel, Sum.elim_comp_inr] using
      (Formula.realize_inf.mp hy).1
  let b : J.Domain M := ⟨y, (Formula.realize_inf.mp hD).1⟩
  have hb := (I.comp_graph_iff J hJ f x b).mp hy
  exact congrArg Subtype.val (hu b hb)

theorem good_comp (hJ : J.Good M)
    (hI : letI := J.inducedStructure hJ.2; I.Good (J.Domain M)) :
    (I.comp J).Good M := by
  let := J.inducedStructure hJ.2
  obtain ⟨x⟩ := hI.1
  exact ⟨⟨(I.compDomainEquiv J hJ.2).symm x⟩, I.graphs_comp J hJ.2 hI.2⟩

theorem comp_isomorphism (hJ : J.GoodGraphs M)
    (hI : letI := J.inducedStructure hJ; I.GoodGraphs (J.Domain M)) :
    letI := J.inducedStructure hJ
    letI := I.inducedStructure hI
    letI := (I.comp J).inducedStructure (I.graphs_comp J hJ hI)
    ∃ e : (I.comp J).Domain M ≃[L] I.Domain (J.Domain M),
      e.toEquiv = I.compDomainEquiv J hJ := by
  let := J.inducedStructure hJ
  let := I.inducedStructure hI
  let := (I.comp J).inducedStructure (I.graphs_comp J hJ hI)
  refine ⟨{
    toEquiv := I.compDomainEquiv J hJ
    map_fun' := ?_
    map_rel' := ?_
  }, rfl⟩
  · intro n f x
    apply Subtype.ext
    apply (I.induced_fun_graph hI f (fun i => I.compDomainEquiv J hJ (x i)) _).mp
    apply (I.comp_graph_iff J hJ f x
      (I.compDomainEquiv J hJ (Structure.funMap f x)).val).mp
    exact ((I.comp J).induced_fun_graph (I.graphs_comp J hJ hI) f x _).mpr rfl
  · intro n R x
    exact (realize_translate hJ (I.relationFormula R)
      (fun i => (I.compDomainEquiv J hJ (x i)).val)).symm

theorem comp_translation {α : Type z} (hJ : J.GoodGraphs M)
    (hI : letI := J.inducedStructure hJ; I.GoodGraphs (J.Domain M))
    (A : L.Formula α) (v : α → (I.comp J).Domain M) :
    ((I.comp J).translate A).Realize (fun a => (v a).val) ↔
      (J.translate (I.translate A)).Realize (fun a => (v a).val) := by
  let := J.inducedStructure hJ
  let := I.inducedStructure hI
  let := (I.comp J).inducedStructure (I.graphs_comp J hJ hI)
  obtain ⟨e, he⟩ := I.comp_isomorphism J hJ hI
  have hv : (fun a => ((e (v a)).val).val) = (fun a => (v a).val) := by
    funext a
    change ((e.toEquiv (v a)).val).val = (v a).val
    rw [he]
    rfl
  have hout := realize_translate hJ (I.translate A) (fun a => (e (v a)).val)
  rw [hv] at hout
  have hiso : A.Realize (fun a => e (v a)) ↔ A.Realize v :=
    StrongHomClass.realize_formula e A
  exact (realize_translate (I.graphs_comp J hJ hI) A v).trans
    (hiso.symm.trans ((realize_translate hI A (fun a => e (v a))).symm.trans hout.symm))


private theorem graph_sentence_of_graphs (d : InterpretationData L H) (hd : d.GoodGraphs M)
    {n : ℕ} (f : L.Functions n) : M ⊨ d.graphSentence f := by
  apply (d.realize_graphSentence f).mpr
  intro x hx
  exact hd n f (fun i => ⟨x i, hx i⟩)

theorem comp_interprets {T : L.Theory} {S : K.Theory} {U : H.Theory}
    (hI : I.Interprets T S) (hJ : J.Interprets S U) :
    (I.comp J).Interprets T U := by
  have hg (N : Type (max u'' v'')) [H.Structure N] [Nonempty N] [N ⊨ U] :
      (I.comp J).Good N := by
    have hj := J.good_of_admissible (M := N) hJ.1
    let := J.inducedStructure hj.2
    let : Nonempty (J.Domain N) := hj.1
    let : J.Domain N ⊨ S := J.models_induced hJ
    exact I.good_comp J hj (I.good_of_admissible (M := J.Domain N) hI.1)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply Lemmatheca.MathematicalLogic.ChangingLanguages.deductive_completeness
    rw [Theory.models_sentence_iff]
    intro N
    exact (I.comp J).realize_nonemptySentence.mpr (hg N).1
  · intro n f
    apply Lemmatheca.MathematicalLogic.ChangingLanguages.deductive_completeness
    rw [Theory.models_sentence_iff]
    intro N
    exact graph_sentence_of_graphs (I.comp J) (hg N).2 f
  · intro A hA
    apply Lemmatheca.MathematicalLogic.ChangingLanguages.deductive_completeness
    rw [Theory.models_sentence_iff]
    intro N
    have hj := J.good_of_admissible (M := N) hJ.1
    let := J.inducedStructure hj.2
    let : Nonempty (J.Domain N) := hj.1
    let : J.Domain N ⊨ S := J.models_induced hJ
    have hi := I.good_of_admissible (M := J.Domain N) hI.1
    let := I.inducedStructure hi.2
    let : Nonempty (I.Domain (J.Domain N)) := hi.1
    let : I.Domain (J.Domain N) ⊨ T := I.models_induced hI
    have ha : I.Domain (J.Domain N) ⊨ A := Theory.realize_sentence_of_mem T hA
    have hat := (realize_translateSentence hi.2 A).mpr ha
    have hatt := (realize_translateSentence hj.2 (I.translateSentence A)).mpr hat
    have hc := I.comp_translation J hj.2 hi.2 A (default : Empty → (I.comp J).Domain N)
    have hv : (fun a : Empty => ((default : Empty → (I.comp J).Domain N) a).val) =
        (default : Empty → N) := by funext a; exact a.elim
    rw [hv] at hc
    exact hc.mpr hatt

/-- The full-domain datum with actual equality graphs. -/
def identity (L : Language.{u,v}) : InterpretationData L L where
  domain := ⊤
  functionGraph f := (Term.var (.inr ())).equal (.func f (fun i => .var (.inl i)))
  relationFormula R := R.formula Term.var

variable {N : Type w} [L.Structure N]

theorem identity_graphs : (identity L).GoodGraphs N := by
  intro n f x
  simp only [guardedGraph, identity, Formula.realize_inf, Formula.realize_relabel,
    Formula.realize_top, true_and, Formula.realize_equal, Term.realize_var,
    Sum.elim_inr, Term.realize_func, Sum.elim_inl]
  exact existsUnique_eq

theorem identity_good [Nonempty N] : (identity L).Good N := by
  refine ⟨?_, identity_graphs⟩
  exact ⟨⟨Classical.arbitrary N, by simp [identity]⟩⟩

theorem identity_isomorphism :
    letI := (identity L).inducedStructure (identity_graphs (L := L) (N := N))
    ∃ e : (identity L).Domain N ≃[L] N, ∀ x, e x = x.val := by
  let := (identity L).inducedStructure (identity_graphs (L := L) (N := N))
  refine ⟨{
    toFun := Subtype.val
    invFun := fun x => ⟨x, by simp [identity]⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_fun' := ?_
    map_rel' := ?_
  }, fun _ => rfl⟩
  · intro n f x
    change (Structure.funMap f x).val =
      @Structure.funMap L N _ n f (fun i => (x i).val)
    have hg := ((identity L).induced_fun_graph identity_graphs f x _).mpr rfl
    simpa only [guardedGraph, identity, Formula.realize_inf, Formula.realize_relabel,
      Formula.realize_top, true_and, Formula.realize_equal, Term.realize_var,
      Sum.elim_inr, Term.realize_func, Sum.elim_inl, Function.comp_def] using hg
  · intro n R x
    rfl

theorem identity_translation {α : Type z} (A : L.Formula α) (v : α → N) :
    ((identity L).translate A).Realize v ↔ A.Realize v := by
  let := (identity L).inducedStructure (identity_graphs (L := L) (N := N))
  obtain ⟨e, he⟩ := identity_isomorphism (L := L) (N := N)
  let w : α → (identity L).Domain N := fun a => ⟨v a, by simp [identity]⟩
  have ht := realize_translate (identity_graphs (L := L) (N := N)) A w
  have hi := StrongHomClass.realize_formula e A (v := w)
  have hv : e ∘ w = v := by funext a; exact he (w a)
  rw [hv] at hi
  exact ht.trans hi.symm

theorem identity_interprets (T : L.Theory) : (identity L).Interprets T T := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply Lemmatheca.MathematicalLogic.ChangingLanguages.deductive_completeness
    rw [Theory.models_sentence_iff]
    intro M
    exact (identity L).realize_nonemptySentence.mpr identity_good.1
  · intro n f
    apply Lemmatheca.MathematicalLogic.ChangingLanguages.deductive_completeness
    rw [Theory.models_sentence_iff]
    intro M
    exact graph_sentence_of_graphs (identity L) identity_graphs f
  · intro A hA
    apply Lemmatheca.MathematicalLogic.ChangingLanguages.deductive_completeness
    rw [Theory.models_sentence_iff]
    intro M
    apply (identity_translation A (default : Empty → M)).mpr
    exact Theory.realize_sentence_of_mem T hA

end InterpretationData
end
end Lemmatheca.MathematicalLogic.InterpretingTheories
