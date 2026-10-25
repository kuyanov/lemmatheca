import Lemmatheca.RecursionTheorem.RecursionTheorem

/-! Uniform semantic fixed points in the existing standard program numbering. -/
namespace Lemmatheca.ComputabilityTheory.UniformSelfReference

open UniversalComputation RecursionTheorem

def IsUniformSelector (F : ℕ → ℕ → ℕ) (h : ℕ → ℕ) : Prop :=
  Computable h ∧ ∀ a x, phi (h a) x = phi (F (h a) a) x

def auxiliary (F : ℕ → ℕ → ℕ) (e y : ℕ) : Part ℕ :=
  phi (F (specialize e y.unpair.1) y.unpair.1) y.unpair.2

def AuxiliaryIndex (F : ℕ → ℕ → ℕ) (r : ℕ) : Prop :=
  ∀ b y, phi r (Nat.pair b y) = auxiliary F (selfSpecialize b) y

def selector (q a : ℕ) : ℕ := specialize q a

theorem selector_primitive (q : ℕ) : Primrec (selector q) := by
  exact specialize_primitive.comp (Primrec.const q) Primrec.id

theorem auxiliary_recursive {F : ℕ → ℕ → ℕ} (hF : Computable₂ F) :
    Partrec₂ (auxiliary F) := by
  have h₁ : Computable (fun p : ℕ × ℕ => p.2.unpair.1) :=
    Computable.fst.comp (Computable.unpair.comp Computable.snd)
  have h₂ : Computable (fun p : ℕ × ℕ => p.2.unpair.2) :=
    Computable.snd.comp (Computable.unpair.comp Computable.snd)
  exact phi_recursive.comp
    (hF.comp (specialize_primitive.to_comp.comp Computable.fst h₁) h₁) h₂

theorem specified_uniform_selector (F : ℕ → ℕ → ℕ) (r : ℕ)
    (hr : AuxiliaryIndex F r) :
    let q := selfSpecialize r
    Primrec (selector q) ∧
      (∀ y, phi q y = auxiliary F q y) ∧ IsUniformSelector F (selector q) := by
  dsimp only
  have hq : ∀ y, phi (selfSpecialize r) y = auxiliary F (selfSpecialize r) y :=
    specified_fixed_point r hr
  refine ⟨selector_primitive _, hq, (selector_primitive _).to_comp, ?_⟩
  intro a x
  rw [show selector (selfSpecialize r) a = specialize (selfSpecialize r) a from rfl,
    specialize_eval, hq]
  simp only [auxiliary, Nat.unpair_pair]

theorem parameterized_recursion {F : ℕ → ℕ → ℕ} (hF : Computable₂ F) :
    ∃ r, AuxiliaryIndex F r ∧
      let q := selfSpecialize r
      Primrec (selector q) ∧
        (∀ y, phi q y = auxiliary F q y) ∧ IsUniformSelector F (selector q) := by
  obtain ⟨r, hr, _⟩ := recursion_theorem (auxiliary_recursive hF)
  exact ⟨r, hr, specified_uniform_selector F r hr⟩

def partialFamilyCompiler (p e a : ℕ) : ℕ := specialize (specialize p e) a

theorem partial_family_compiler_primitive (p : ℕ) :
    Primrec₂ (partialFamilyCompiler p) := by
  exact specialize_primitive.comp
    (specialize_primitive.comp (Primrec.const p) Primrec.fst) Primrec.snd

theorem partial_family_compiler_eval (p e a x : ℕ) :
    phi (partialFamilyCompiler p e a) x = phi p (Nat.pair e (Nat.pair a x)) := by
  simp only [partialFamilyCompiler, specialize_eval]

theorem partial_family_index {g : ℕ → ℕ → ℕ → Part ℕ}
    (hg : Partrec (fun p : ℕ × (ℕ × ℕ) => g p.1 p.2.1 p.2.2)) :
    ∃ p, ∀ e a x, phi p (Nat.pair e (Nat.pair a x)) = g e a x := by
  have hh : Partrec₂ (fun (e y : ℕ) => g e y.unpair.1 y.unpair.2) :=
    hg.comp (Computable.fst.pair (Computable.unpair.comp Computable.snd))
  obtain ⟨p, hp⟩ := phi_complete (Partrec₂.unpaired'.mpr hh)
  refine ⟨p, fun e a x => ?_⟩
  simpa only [Nat.unpaired, Nat.unpair_pair] using congrFun hp (Nat.pair e (Nat.pair a x))

theorem specified_partial_family_selector {g : ℕ → ℕ → ℕ → Part ℕ} (p : ℕ)
    (hp : ∀ e a x, phi p (Nat.pair e (Nat.pair a x)) = g e a x) :
    ∃ r, AuxiliaryIndex (partialFamilyCompiler p) r ∧
      Primrec (selector (selfSpecialize r)) ∧
      ∀ a x, phi (selector (selfSpecialize r) a) x = g (selector (selfSpecialize r) a) a x := by
  obtain ⟨r, hr, hs, _, hh⟩ := parameterized_recursion (partial_family_compiler_primitive p).to_comp
  refine ⟨r, hr, hs, fun a x => ?_⟩
  exact (hh.2 a x).trans ((partial_family_compiler_eval p _ a x).trans (hp _ a x))

/-- The public partial-output interface retains one total computable parameter map. -/
theorem parameterized_partial_recursion {g : ℕ → ℕ → ℕ → Part ℕ}
    (hg : Partrec (fun p : ℕ × (ℕ × ℕ) => g p.1 p.2.1 p.2.2)) :
    ∃ h : ℕ → ℕ, Primrec h ∧ ∀ a x, phi (h a) x = g (h a) a x := by
  obtain ⟨p, hp⟩ := partial_family_index hg
  obtain ⟨r, _, hs, hh⟩ := specified_partial_family_selector p hp
  exact ⟨selector (selfSpecialize r), hs, hh⟩

end Lemmatheca.ComputabilityTheory.UniformSelfReference
