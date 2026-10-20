import Lemmatheca.MathematicalLogic.PARecursionSentences

/-! Arbitrary definable graphs satisfying the same recursion equations agree.
Unlike congruence of our graph constructor, this uses PA induction. -/
namespace Lemmatheca.MathematicalLogic.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
noncomputable section
universe u

theorem same_recursion_model {n : ℕ} {M : Type u} [language.Structure M] [M ⊨ PA]
    (F G : language.Formula (Fin (n + 1) ⊕ Unit))
    (B : language.Formula (Fin n ⊕ Unit))
    (H : language.Formula (Fin (n + 2) ⊕ Unit))
    (hF0 : ∀ x y, F.Realize (extend (Fin.snoc x (zeroValue M)) y) ↔ B.Realize (extend x y))
    (hG0 : ∀ x y, G.Realize (extend (Fin.snoc x (zeroValue M)) y) ↔ B.Realize (extend x y))
    (hFS : ∀ x k y, F.Realize (extend (Fin.snoc x (succValue M k)) y) ↔
      ∃ a, F.Realize (extend (Fin.snoc x k) a) ∧ H.Realize (extend (Fin.snoc (Fin.snoc x k) a) y))
    (hGS : ∀ x k y, G.Realize (extend (Fin.snoc x (succValue M k)) y) ↔
      ∃ a, G.Realize (extend (Fin.snoc x k) a) ∧ H.Realize (extend (Fin.snoc (Fin.snoc x k) a) y)) :
    ∀ (x : Fin n → M) (k y : M), F.Realize (extend (Fin.snoc x k) y) ↔ G.Realize (extend (Fin.snoc x k) y) := by
  intro x
  let P : M → Prop := fun k => ∀ y,
    F.Realize (extend (Fin.snoc x k) y) ↔ G.Realize (extend (Fin.snoc x k) y)
  have hP : Set.univ.Definable₁ language {k | P k} := by
    change DPred (fun v : Fin 1 → M => ∀ y,
      F.Realize (extend (Fin.snoc x (v 0)) y) ↔ G.Realize (extend (Fin.snoc x (v 0)) y))
    apply dp_forall
    simp only [iff_iff_implies_and_implies]
    apply dp_and
    · apply dp_imp
      · apply dp_formula F
        intro j
        cases j with
        | inl j =>
            refine Fin.lastCases ?_ (fun i => ?_) j
            · simpa only [extend, Sum.elim_inl, Fin.snoc_last, Function.comp_def] using
                (df_proj (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Unit) :
                  Set.univ.DefinableFun language (fun v : Fin 1 ⊕ Unit → M => v (.inl 0)))
            · simpa only [extend, Sum.elim_inl, Fin.snoc_castSucc] using
                (df_const (x i) : Set.univ.DefinableFun language (fun _ : Fin 1 ⊕ Unit → M => x i))
        | inr j =>
            simpa only [extend, Sum.elim_inr] using
              (df_proj (Sum.inr () : Fin 1 ⊕ Unit) :
                Set.univ.DefinableFun language (fun v : Fin 1 ⊕ Unit → M => v (.inr ())))
      · apply dp_formula G
        intro j
        cases j with
        | inl j =>
            refine Fin.lastCases ?_ (fun i => ?_) j
            · simpa only [extend, Sum.elim_inl, Fin.snoc_last, Function.comp_def] using
                (df_proj (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Unit) :
                  Set.univ.DefinableFun language (fun v : Fin 1 ⊕ Unit → M => v (.inl 0)))
            · simpa only [extend, Sum.elim_inl, Fin.snoc_castSucc] using
                (df_const (x i) : Set.univ.DefinableFun language (fun _ : Fin 1 ⊕ Unit → M => x i))
        | inr j =>
            simpa only [extend, Sum.elim_inr] using
              (df_proj (Sum.inr () : Fin 1 ⊕ Unit) :
                Set.univ.DefinableFun language (fun v : Fin 1 ⊕ Unit → M => v (.inr ())))
    · apply dp_imp
      · apply dp_formula G
        intro j
        cases j with
        | inl j =>
            refine Fin.lastCases ?_ (fun i => ?_) j
            · simpa only [extend, Sum.elim_inl, Fin.snoc_last, Function.comp_def] using
                (df_proj (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Unit) :
                  Set.univ.DefinableFun language (fun v : Fin 1 ⊕ Unit → M => v (.inl 0)))
            · simpa only [extend, Sum.elim_inl, Fin.snoc_castSucc] using
                (df_const (x i) : Set.univ.DefinableFun language (fun _ : Fin 1 ⊕ Unit → M => x i))
        | inr j =>
            simpa only [extend, Sum.elim_inr] using
              (df_proj (Sum.inr () : Fin 1 ⊕ Unit) :
                Set.univ.DefinableFun language (fun v : Fin 1 ⊕ Unit → M => v (.inr ())))
      · apply dp_formula F
        intro j
        cases j with
        | inl j =>
            refine Fin.lastCases ?_ (fun i => ?_) j
            · simpa only [extend, Sum.elim_inl, Fin.snoc_last, Function.comp_def] using
                (df_proj (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Unit) :
                  Set.univ.DefinableFun language (fun v : Fin 1 ⊕ Unit → M => v (.inl 0)))
            · simpa only [extend, Sum.elim_inl, Fin.snoc_castSucc] using
                (df_const (x i) : Set.univ.DefinableFun language (fun _ : Fin 1 ⊕ Unit → M => x i))
        | inr j =>
            simpa only [extend, Sum.elim_inr] using
              (df_proj (Sum.inr () : Fin 1 ⊕ Unit) :
                Set.univ.DefinableFun language (fun v : Fin 1 ⊕ Unit → M => v (.inr ())))
  apply definable_induction P hP
  · intro y
    exact (hF0 x y).trans (hG0 x y).symm
  · intro k ih y
    rw [hFS, hGS]
    exact exists_congr (fun a => and_congr_left (fun _ => ih a))

/-- Same equations for arbitrary arithmetic graphs give a PA proof of equivalence. -/
theorem same_recursion_derives {n : ℕ}
    (F G : language.Formula (Fin (n + 1) ⊕ Unit))
    (B : language.Formula (Fin n ⊕ Unit))
    (H : language.Formula (Fin (n + 2) ⊕ Unit))
    (hF0 : Derives PA (allClose (recursionZeroFormula F B)))
    (hG0 : Derives PA (allClose (recursionZeroFormula G B)))
    (hFS : Derives PA (allClose (recursionSuccessorFormula F H)))
    (hGS : Derives PA (allClose (recursionSuccessorFormula G H))) :
    PAEquivalent F G := by
  apply derives_allClose_of_models
  intro M v
  rw [Formula.realize_iff]
  have sound {α : Type} [Fintype α] (φ : language.Formula α)
      (h : Derives PA (allClose φ)) (w : α → M) : φ.Realize w :=
    (realize_allClose _).mp (derives_sound h default
      (fun C hC => Theory.realize_sentence_of_mem PA hC)) w
  have hzero (R : language.Formula (Fin (n + 1) ⊕ Unit))
      (h : Derives PA (allClose (recursionZeroFormula R B))) (x : Fin n → M) (y : M) :=
    (realize_recursionZeroFormula R B x y).mp (sound _ h (extend x y))
  have hstep (R : language.Formula (Fin (n + 1) ⊕ Unit))
      (h : Derives PA (allClose (recursionSuccessorFormula R H))) (x : Fin n → M) (k y : M) :=
    (realize_recursionSuccessorFormula R H x k y).mp (sound _ h (extend (Fin.snoc x k) y))
  let x : Fin n → M := fun i => v (.inl i.castSucc)
  let k := v (.inl (Fin.last n))
  let y := v (.inr ())
  have hv : extend (Fin.snoc x k) y = v := by
    funext j
    cases j with
    | inl j => refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [extend, x, k]
    | inr j => cases j; rfl
  rw [← hv]
  exact same_recursion_model F G B H (hzero F hF0) (hzero G hG0) (hstep F hFS) (hstep G hGS) x k y

end
end Lemmatheca.MathematicalLogic.PAComputations
