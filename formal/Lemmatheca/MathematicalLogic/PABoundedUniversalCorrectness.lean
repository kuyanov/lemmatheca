import Lemmatheca.MathematicalLogic.PABoundedUniversalStep

namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.BoundedUniversalPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms InitialSegmentPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem append_zero_value {r : ℕ} (positive : Program (r + 1)) (x : Fin r → M) :
    (Program.comp positive (Fin.snoc (fun i => Program.proj i) (constant 0))).value x =
      positive.value (Fin.snoc x (zeroValue M)) := by
  rw [Program.value_comp]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, constant_value, numeral_value_zero]
  · simp only [Fin.snoc_castSucc, Program.value_proj]

theorem forallBoundedBuilder_zero_value {r : ℕ} (body : Program r)
    (positive : Program (r + 1)) (x : Fin r → M) :
    (forallBoundedBuilder body positive).value (Fin.snoc x (zeroValue M)) =
      baseCertificate.value ![positive.value (Fin.snoc x (zeroValue M)), body.value x] := by
  rw [forallBoundedBuilder, Program.value_rec_zero, binary_value, append_zero_value]

theorem forallBoundedBuilder_successor_value {r : ℕ} (body : Program r)
    (positive : Program (r + 1)) (x : Fin r → M) (k : M) :
    (forallBoundedBuilder body positive).value (Fin.snoc x (succValue M k)) =
      stepCertificate.value ![k, (forallBoundedBuilder body positive).value (Fin.snoc x k),
        positive.value (Fin.snoc x (succValue M k)), body.value x] := by
  have ht (u : M) :
      (Program.comp positive (Fin.snoc (fun i : Fin r => Program.proj (i.castAdd 2))
        (unary .succ (.proj (Fin.last r).castSucc)))).value (Fin.snoc (Fin.snoc x k) u) =
        positive.value (Fin.snoc x (succValue M k)) := by
    rw [Program.value_comp]
    congr 1
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, unary_value, Program.value_succ, Program.value_proj,
        Matrix.cons_val_zero, Fin.snoc_castSucc]
    · rw [Fin.snoc_castSucc, Program.value_proj]
      simp only [Fin.snoc_castSucc]
      change (Fin.snoc (Fin.snoc x k) u : Fin (r + 2) → M) j.castSucc.castSucc = x j
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
  have hb (u : M) :
      (Program.comp body (fun i : Fin r => Program.proj (i.castAdd 2))).value
        (Fin.snoc (Fin.snoc x k) u) = body.value x := by
    rw [Program.value_comp]
    congr 1
    funext i
    rw [Program.value_proj]
    change (Fin.snoc (Fin.snoc x k) u : Fin (r + 2) → M) i.castSucc.castSucc = x i
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
  change (Program.prec _ _).value _ = _
  rw [Program.value_rec_succ, value_comp_four, ht, hb, Program.value_proj,
    Program.value_proj, Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_last]
  rfl

/-- A genuine internal certificate loop. All premises concerning the body and
the one-step certificates are discharged by the shared-syntax compiler in the
structural bounded-formula theorem. No correctness of an opaque checker is
postulated: every iteration uses the concrete checked records above. -/
theorem forallBoundedBuilder_certified {r : ℕ} (body : Program r)
    (test positive : Program (r + 1)) (x : Fin r → M)
    (hb : FormulaBound 1 (body.value x))
    (hinst : NamedFormulaBound 0
      (instantiate.value ![body.value x, modelNode 8 [zeroValue M] ]))
    (hfresh : occursAux.value ![zeroValue M, body.value x] = zeroValue M)
    (hpositive : ∀ i : M, test.value (Fin.snoc x i) = numeralValue M 1 →
      Certified axiomVerifier (positive.value (Fin.snoc x i))
        (instantiate.value ![body.value x, ProofPrograms.numeral.value ![i] ]))
    (n : M) (hall : ∀ i : M, leValue M i n → test.value (Fin.snoc x i) = numeralValue M 1) :
    Certified axiomVerifier ((forallBoundedBuilder body positive).value (Fin.snoc x n))
      ((boundedCode body).value (Fin.snoc x n)) := by
  have h : ∀ n : M,
      (∀ i : M, leValue M i n → test.value (Fin.snoc x i) = numeralValue M 1) →
      Certified axiomVerifier ((forallBoundedBuilder body positive).value (Fin.snoc x n))
        ((boundedCode body).value (Fin.snoc x n)) := by
    apply definable_induction
    · change DPred (fun v : Fin 1 → M =>
        (∀ i : M, leValue M i (v 0) → test.value (Fin.snoc x i) = numeralValue M 1) →
        Certified axiomVerifier ((forallBoundedBuilder body positive).value (Fin.snoc x (v 0)))
          ((boundedCode body).value (Fin.snoc x (v 0))))
      unfold Certified
      pa_definable
    · intro hzero
      rw [forallBoundedBuilder_zero_value, boundedCode_model_value]
      exact certified_baseCertificate _ _ (hpositive _ (hzero _ (le_refl_value _))) hb hinst hfresh
    · intro k hk hnext
      rw [forallBoundedBuilder_successor_value, boundedCode_model_value]
      have hprev := hk (fun i hi => hnext i (le_trans_value hi (le_successor_value k)))
      rw [boundedCode_model_value] at hprev
      exact certified_stepCertificate k _ _ _ hprev
        (hpositive _ (hnext _ (le_refl_value _))) hb hinst hfresh
  exact h n hall

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.BoundedUniversalPrograms
