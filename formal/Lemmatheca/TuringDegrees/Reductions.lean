import Lemmatheca.OracleComputation.Substitution
import Mathlib.Computability.Reduce
import Mathlib.Order.Antisymmetrization

/-! Set reducibility through the actual finite Boolean-query program language. -/
namespace Lemmatheca.ComputabilityTheory.TuringDegrees

open OracleComputation UniversalComputation

noncomputable section

def Reduces (c : Code) (A B : Set ℕ) : Prop :=
  ∀ x, eval B c x = Part.some (indicator (fun n => n ∈ A) x)

def Reducible (A B : Set ℕ) : Prop := ∃ c : Code, Reduces c A B

abbrev Equivalent : Set ℕ → Set ℕ → Prop := AntisymmRel Reducible

theorem reducible_refl (A : Set ℕ) : Reducible A A := by
  exact ⟨.query, fun _ => rfl⟩

theorem subst_reduces {A B C : Set ℕ} (c d : Code)
    (hc : Reduces c A B) (hd : Reduces d B C) :
    Reduces (subst d c) A C := by
  intro x
  rw [subst_eval B C d hd c x]
  exact hc x

theorem reducible_trans {A B C : Set ℕ} (hAB : Reducible A B)
    (hBC : Reducible B C) : Reducible A C := by
  obtain ⟨c, hc⟩ := hAB
  obtain ⟨d, hd⟩ := hBC
  exact ⟨subst d c, subst_reduces c d hc hd⟩

theorem computable_uniform (A : Set ℕ) (hA : ComputablePred (fun n => n ∈ A)) :
    ∃ r : Nat.Partrec.Code,
      (∀ x, Nat.Partrec.Code.eval r x = Part.some (indicator (fun n => n ∈ A) x)) ∧
      ∀ B : Set ℕ, Reduces (embed r) A B := by
  obtain ⟨r, hr, _⟩ := computable_oracle_elimination A hA
  exact ⟨r, hr, fun B x => (eval_embed B r x).trans (hr x)⟩

theorem computable_of_reducible {A B : Set ℕ} (hAB : Reducible A B)
    (hB : ComputablePred (fun n => n ∈ B)) :
    ComputablePred (fun n => n ∈ A) := by
  obtain ⟨c, hc⟩ := hAB
  obtain ⟨r, _, hr⟩ := computable_oracle_elimination B hB
  have hchar : Computable (indicator (fun n => n ∈ A)) :=
    (Partrec.nat_iff.mpr (Nat.Partrec.Code.exists_code.mpr ⟨erase r c, rfl⟩)).of_eq_tot
      (fun x => by rw [hr c x, hc x]; exact Part.mem_some _)
  exact (decidable_iff_characteristic _).mpr ⟨_, hchar, fun _ => rfl⟩

theorem reducible_empty_iff (A : Set ℕ) :
    Reducible A ∅ ↔ ComputablePred (fun n => n ∈ A) := by
  constructor
  · intro h
    exact computable_of_reducible h ⟨inferInstance, Computable.const false⟩
  · intro h
    obtain ⟨r, _, hr⟩ := computable_uniform A h
    exact ⟨embed r, hr ∅⟩

def preprocess (r : Nat.Partrec.Code) : Code := .comp .query (embed r)

theorem preprocess_reduces {A B : Set ℕ} {f : ℕ → ℕ} (r : Nat.Partrec.Code)
    (hr : ∀ x, Nat.Partrec.Code.eval r x = Part.some (f x))
    (hf : ∀ x, x ∈ A ↔ f x ∈ B) :
    Reduces (preprocess r) A B := by
  classical
  intro x
  simp only [preprocess, eval, eval_embed, hr, Part.bind_some]
  congr 1
  simp only [indicator, hf x]

theorem manyOne_imp_reducible {A B : Set ℕ}
    (h : ManyOneReducible (fun n => n ∈ A) (fun n => n ∈ B)) :
    Reducible A B := by
  obtain ⟨f, hf, hAB⟩ := h
  obtain ⟨r, hr⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf.partrec)
  exact ⟨preprocess r, preprocess_reduces r (fun x => congrFun hr x) hAB⟩

theorem complement_equivalent (A : Set ℕ) : Equivalent A Aᶜ := by
  constructor
  · exact ⟨complementQuery, fun x => by simpa using complement_query_eval Aᶜ x⟩
  · exact ⟨complementQuery, complement_query_eval A⟩

theorem ce_complement_not_manyOne (B : Set ℕ)
    (hB : REPred (fun n => n ∈ B)) (hnot : ¬ ComputablePred (fun n => n ∈ B)) :
    ¬ ManyOneReducible (fun n => n ∈ Bᶜ) (fun n => n ∈ B) := by
  rintro ⟨f, hf, he⟩
  apply hnot
  apply ComputablePred.computable_iff_re_compl_re'.mpr
  have hcomp : REPred (fun x => f x ∈ B) := hB.comp hf
  exact ⟨hB, REPred.of_eq hcomp (fun x => (he x).symm)⟩

end
end Lemmatheca.ComputabilityTheory.TuringDegrees
