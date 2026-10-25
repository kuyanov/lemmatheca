import Lemmatheca.UniformSelfReference.Uniform

/-! Explicit effective translations between numerical function numberings. -/
namespace Lemmatheca.ComputabilityTheory.UniformSelfReference

open UniversalComputation RecursionTheorem

def IsNumbering (ψ : ℕ → ℕ → Part ℕ) : Prop :=
  (∀ n, Nat.Partrec (ψ n)) ∧
    ∀ f : ℕ → Part ℕ, Nat.Partrec f → ∃ n, ψ n = f

def IsComputableNumbering (ψ : ℕ → ℕ → Part ℕ) : Prop :=
  IsNumbering ψ ∧ Partrec₂ ψ

structure Compilers (ψ : ℕ → ℕ → Part ℕ) where
  forward : ℕ → ℕ
  backward : ℕ → ℕ
  forward_computable : Computable forward
  backward_computable : Computable backward
  forward_eval : ∀ n x, phi (forward n) x = ψ n x
  backward_eval : ∀ e x, ψ (backward e) x = phi e x

def Acceptable (ψ : ℕ → ℕ → Part ℕ) : Prop :=
  IsNumbering ψ ∧ Nonempty (Compilers ψ)

theorem standard_numbering : IsComputableNumbering phi := by
  refine ⟨⟨fun n => ?_, fun f hf => phi_complete hf⟩, phi_recursive⟩
  exact Partrec.nat_iff.mp (phi_recursive.comp (Computable.const n) Computable.id)

theorem compiler_to_standard {ψ : ℕ → ℕ → Part ℕ} (hψ : Partrec₂ ψ) :
    ∃ p, (∀ n x, phi p (Nat.pair n x) = ψ n x) ∧
      Primrec (selector p) ∧ ∀ n x, phi (selector p n) x = ψ n x := by
  obtain ⟨p, hp⟩ := phi_complete (Partrec₂.unpaired'.mpr hψ)
  have hp' : ∀ n x, phi p (Nat.pair n x) = ψ n x := by
    intro n x
    simpa only [Nat.unpaired, Nat.unpair_pair] using congrFun hp (Nat.pair n x)
  exact ⟨p, hp', selector_primitive p, fun n x => (specialize_eval p n x).trans (hp' n x)⟩

theorem compilers_recursive {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) :
    Partrec₂ ψ := by
  exact (phi_recursive.comp (C.forward_computable.comp Computable.fst) Computable.snd).of_eq
    (fun p => C.forward_eval p.1 p.2)

theorem compilers_numbering {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) :
    IsNumbering ψ := by
  refine ⟨fun n => ?_, fun f hf => ?_⟩
  · exact Partrec.nat_iff.mp ((compilers_recursive C).comp (Computable.const n) Computable.id)
  · obtain ⟨e, he⟩ := phi_complete hf
    exact ⟨C.backward e, funext fun x => (C.backward_eval e x).trans (congrFun he x)⟩

theorem compiler_round_trips {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) :
    (∀ n x, ψ (C.backward (C.forward n)) x = ψ n x) ∧
      ∀ e x, phi (C.forward (C.backward e)) x = phi e x := by
  exact ⟨fun n x => (C.backward_eval (C.forward n) x).trans (C.forward_eval n x),
    fun e x => (C.forward_eval (C.backward e) x).trans (C.backward_eval e x)⟩

def numberingSpecialize {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) (n a : ℕ) : ℕ :=
  C.backward (specialize (C.forward n) a)

theorem numbering_specialization {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) :
    Computable₂ (numberingSpecialize C) ∧
      ∀ n a x, ψ (numberingSpecialize C n a) x = ψ n (Nat.pair a x) := by
  refine ⟨C.backward_computable.comp
    (specialize_primitive.to_comp.comp (C.forward_computable.comp Computable.fst) Computable.snd), ?_⟩
  intro n a x
  exact (C.backward_eval _ x).trans ((specialize_eval _ a x).trans (C.forward_eval n _))

def translatedTransformation {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ)
    (F : ℕ → ℕ → ℕ) (e a : ℕ) : ℕ := C.forward (F (C.backward e) a)

def translatedSelector {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ)
    (h : ℕ → ℕ) (a : ℕ) : ℕ := C.backward (h a)

theorem translated_transformation_computable {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ)
    {F : ℕ → ℕ → ℕ} (hF : Computable₂ F) : Computable₂ (translatedTransformation C F) := by
  exact C.forward_computable.comp (hF.comp (C.backward_computable.comp Computable.fst) Computable.snd)

theorem specified_numbering_selector {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ)
    (F : ℕ → ℕ → ℕ) (h : ℕ → ℕ)
    (hh : IsUniformSelector (translatedTransformation C F) h) :
    Computable (translatedSelector C h) ∧
      ∀ a x, ψ (translatedSelector C h a) x = ψ (F (translatedSelector C h a) a) x := by
  refine ⟨C.backward_computable.comp hh.1, fun a x => ?_⟩
  exact (C.backward_eval _ x).trans ((hh.2 a x).trans (C.forward_eval _ x))

theorem numbering_uniform_recursion {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ)
    {F : ℕ → ℕ → ℕ} (hF : Computable₂ F) :
    ∃ r, AuxiliaryIndex (translatedTransformation C F) r ∧
      let h := selector (selfSpecialize r)
      Primrec h ∧ IsUniformSelector (translatedTransformation C F) h ∧
        Computable (translatedSelector C h) ∧
        ∀ a x, ψ (translatedSelector C h a) x = ψ (F (translatedSelector C h a) a) x := by
  obtain ⟨r, hr, hs, _, hh⟩ := parameterized_recursion (translated_transformation_computable C hF)
  exact ⟨r, hr, hs, hh, specified_numbering_selector C F _ hh⟩

end Lemmatheca.ComputabilityTheory.UniformSelfReference
