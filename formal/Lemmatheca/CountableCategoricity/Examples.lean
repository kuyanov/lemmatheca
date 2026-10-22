import Lemmatheca.CountableCategoricity.Categoricity
import Lemmatheca.IsolatedTypes.Patterns
import Lemmatheca.BackAndForth.BackAndForthStrictTheory

/-! The previously classified pair patterns, now as actual automorphism orbits. -/
namespace Lemmatheca.Entry.CountableCategoricity

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.CountableCategoricity
open Lemmatheca.MathematicalLogic.FirstOrderSyntax

open Lemmatheca.ModelTheory
open Lemmatheca.ModelTheory.QuantifierElimination

private theorem type_eq_of_similar {o : Bool} {T : (Shared.Lang o).Theory}
    {M : Type} [(Shared.Lang o).Structure M] [Nonempty M] [M ⊨ T]
    (hqe : HasQuantifierElimination T) {n : ℕ} (a b : Fin n → M)
    (hs : Similar (o := o) (Shared.relation (o := o)) (Shared.relation (o := o)) a b) :
    T.typeOf a = T.typeOf b := by
  apply AtomicAndPrimeModels.typeOf_eq_iff a b |>.mpr
  intro φ
  obtain ⟨ψ, hψ, he⟩ := hqe n (Shared.pack φ)
  have h := (he.realize_bd_iff (M := M) (xs := a)).trans
    ((Shared.qf_transport hψ hs).trans (he.realize_bd_iff (M := M) (xs := b)).symm)
  simpa only [Shared.pack_realize] using h

/-- In a countable infinite equality structure, pair orbits are exactly equality versus inequality. -/
theorem equality_pair_orbits {M : Type} [Language.empty.Structure M]
    [Nonempty M] [Countable M] [Infinite M] (a b : Fin 2 → M) :
    SameOrbit (L := Language.empty) a b ↔ (a 0 = a 1 ↔ b 0 = b 1) := by
  let T := Language.empty.infiniteTheory
  let : M ⊨ T := Language.empty.model_infiniteTheory
  have he := type_eq_iff_sameOrbit (T := T) Shared.equality_isComplete
    ⟨Theory.ModelType.of T M, by change Infinite M; infer_instance⟩ (Cardinal.empty_theory_categorical _ _) a b
  rw [← he]
  constructor
  · intro h
    exact (AtomicAndPrimeModels.typeOf_eq_iff a b).mp h
      ((Term.var 0 : Language.empty.Term (Fin 2)).equal (Term.var 1))
  · intro h
    apply type_eq_of_similar (o := false) (T := T) Shared.equality_hasQuantifierElimination a b
    rintro (⟨i,j⟩ | ⟨r,_,_⟩)
    · change (a i = a j ↔ b i = b j)
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    · exact isEmptyElim r

/-- In a countable dense order, the three actual pair orbit conditions include equality. -/
theorem dlo_pair_orbits {M : Type} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] [Nonempty M] [Countable M] (a b : Fin 2 → M) :
    letI : binaryRelLanguage.Structure M :=
      Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M (fun x y => x < y)
    SameOrbit (L := binaryRelLanguage) a b ↔
      (a 0 = a 1 ∧ b 0 = b 1) ∨
      (a 0 < a 1 ∧ b 0 < b 1) ∨ (a 1 < a 0 ∧ b 1 < b 0) := by
  let : binaryRelLanguage.Structure M :=
    Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M (fun x y => x < y)
  let T := Shared.strictDloTheory
  let : M ⊨ T := Shared.model_strictDloTheory
  let : Infinite M := BackAndForth.strictDlo_models_infinite M
  have he := type_eq_iff_sameOrbit (T := T) Shared.strictDlo_isComplete
    ⟨Theory.ModelType.of T M, by change Infinite M; infer_instance⟩ BackAndForth.strictDlo_countably_categorical a b
  rw [← he]
  constructor
  · intro h
    have hsim : Similar (o := true) (fun x y : M => x < y) (fun x y : M => x < y) a b := by
      intro atom
      let ψ := Shared.atomToShared atom
      let χ : binaryRelLanguage.Formula (Fin 2) :=
        FirstOrder.Language.Formula.relabel (Sum.elim Empty.elim id) ψ.toFormula
      have hχ (x : Fin 2 → M) : χ.Realize x ↔ ψ.Realize Empty.elim x := by
        rw [FirstOrder.Language.Formula.realize_relabel, BoundedFormula.realize_toFormula]
        have h0 : ((x ∘ Sum.elim Empty.elim id) ∘ Sum.inl) = Empty.elim := Subsingleton.elim _ _
        have h2 : ((x ∘ Sum.elim Empty.elim id) ∘ Sum.inr) = x := by ext i; rfl
        rw [h0, h2]
      have hf := (AtomicAndPrimeModels.typeOf_eq_iff a b).mp h χ
      exact (Shared.atomToShared_realize atom a).symm.trans
        ((hχ a).symm.trans (hf.trans ((hχ b).trans (Shared.atomToShared_realize atom b))))
    have heq := hsim (Sum.inl (0, 1))
    have hlt := hsim (Sum.inr ((), 0, 1))
    have hgt := hsim (Sum.inr ((), 1, 0))
    change (a 0 = a 1 ↔ b 0 = b 1) at heq
    change (a 0 < a 1 ↔ b 0 < b 1) at hlt
    change (a 1 < a 0 ↔ b 1 < b 0) at hgt
    rcases lt_trichotomy (a 0) (a 1) with ha | ha | ha
    · exact Or.inr (Or.inl ⟨ha, hlt.mp ha⟩)
    · exact Or.inl ⟨ha, heq.mp ha⟩
    · exact Or.inr (Or.inr ⟨ha, hgt.mp ha⟩)
  · intro h
    apply type_eq_of_similar (o := true) (T := T) Shared.strictDlo_hasQuantifierElimination a b
    rintro (⟨i,j⟩ | ⟨r,i,j⟩)
    · change (a i = a j ↔ b i = b j)
      rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
        fin_cases i <;> fin_cases j <;> simp_all [eq_comm, ne_of_lt, ne_of_gt]
    · change (a i < a j ↔ b i < b j)
      rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
        fin_cases i <;> fin_cases j <;> simp_all [lt_asymm]

end Lemmatheca.Entry.CountableCategoricity
