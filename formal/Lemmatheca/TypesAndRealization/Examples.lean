import Lemmatheca.TypesAndRealization.Types
import Lemmatheca.ArithmeticTheories.ArithmeticTheories

namespace Lemmatheca.Entry.TypesAndRealization

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Types
open Lemmatheca.ModelTheory.ArithmeticTheories

private def avoidNumeral {α : Type*} (i : α) (k : ℕ) : language.Formula α :=
  ((Term.var i).equal ((numeral k).relabel Empty.elim)).not

private theorem realize_avoidNumeral {α M : Type*} [language.Structure M]
    (i : α) (k : ℕ) (a : α → M) :
    (avoidNumeral i k).Realize a ↔ a i ≠ numeralValue M k := by
  simp only [avoidNumeral, Formula.realize_not, Formula.realize_equal,
    Term.realize_var, Term.realize_relabel]
  rw [Subsingleton.elim (a ∘ Empty.elim) (Empty.elim : Empty → M)]
  rfl

private theorem finite_avoidNumerals {α : Type*} (i : α) (v : ℕ → α → ℕ)
    (hv : ∀ b, v b i = b) (s : Finset (language.Formula α))
    (hs : (↑s : Set _) ⊆ Set.range (avoidNumeral i)) :
    ∃ b, ∀ φ ∈ s, φ.Realize (v b) := by
  classical
  let pick (φ : s) : ℕ := Classical.choose (hs φ.prop)
  have hpick (φ : s) : avoidNumeral i (pick φ) = φ := Classical.choose_spec (hs φ.prop)
  let t := s.attach.image pick
  let b := t.sup id + 1
  refine ⟨b, fun φ hφ => ?_⟩
  let φ' : s := ⟨φ, hφ⟩
  have ht : pick φ' ∈ t := Finset.mem_image.mpr ⟨φ', Finset.mem_attach _ _, rfl⟩
  have hlt : pick φ' < b := Nat.lt_succ_of_le (Finset.le_sup (f := id) ht)
  have hr : (avoidNumeral i (pick φ')).Realize (v b) := by
    apply (realize_avoidNumeral i (pick φ') (v b)).mpr
    rw [hv, numeral_value_nat]
    exact (Nat.ne_of_lt hlt).symm
  rw [hpick φ'] at hr
  exact hr

/-- The request that one variable differ from every numeral. -/
def nonstandardConditions : Set (language.Formula (Fin 1)) :=
  Set.range fun k => ((Term.var (0 : Fin 1)).equal
    ((numeral k).relabel Empty.elim)).not

/-- Any finite list of the numeral exclusions has a standard solution. -/
theorem nonstandard_finitely_realized : FinitelyRealized ℕ nonstandardConditions := by
  intro s hs
  obtain ⟨b, hb⟩ := finite_avoidNumerals (0 : Fin 1) (fun b _ => b) (fun _ => rfl) s hs
  exact ⟨fun _ => b, hb⟩

/-- No standard tuple solves all the exclusions. -/
theorem nonstandard_omitted : ¬ ∃ a : Fin 1 → ℕ, Realizes nonstandardConditions a := by
  rintro ⟨a, ha⟩
  have h := (realize_avoidNumeral (0 : Fin 1) (a 0) a).mp
    (ha _ (Set.mem_range_self (a 0)))
  exact h (numeral_value_nat (a 0)).symm

/-- The example is a partial type over true arithmetic. -/
theorem nonstandard_partial : IsPartial trueArithmetic nonstandardConditions := by
  exact (partial_iff_finitelyRealized_completeTheory (M := ℕ) _).mpr
    nonstandard_finitely_realized

/-- An elementary extension of the specified standard arithmetic structure has a nonstandard point. -/
theorem nonstandard_elementary_realization :
    ∃ (N : Type) (_ : language.Structure N) (_ : Nonempty N),
      ∃ (_f : ℕ ↪ₑ[language] N) (b : N), ∀ k, b ≠ numeralValue N k := by
  let p : Set (language.Formula (ℕ ⊕ Fin 1)) := Set.range (avoidNumeral (Sum.inr 0))
  have hp : ∀ s : Finset (language.Formula (ℕ ⊕ Fin 1)), (↑s : Set _) ⊆ p →
      ∃ a : Fin 1 → ℕ, Realizes (↑s : Set (language.Formula (ℕ ⊕ Fin 1)))
        (Sum.elim id a) := by
    intro s hs
    obtain ⟨b, hb⟩ := finite_avoidNumerals (Sum.inr (0 : Fin 1))
      (fun b => Sum.elim id (fun _ => b)) (fun _ => rfl) s hs
    exact ⟨fun _ => b, hb⟩
  obtain ⟨N, SN, hN, f, b, hb⟩ := exists_elementary_realization p hp
  let := SN
  let := hN
  exact ⟨N, SN, hN, f, b 0, fun k =>
    (realize_avoidNumeral (Sum.inr 0) k (Sum.elim f b)).mp
      (hb _ (Set.mem_range_self k))⟩

end Lemmatheca.Entry.TypesAndRealization
