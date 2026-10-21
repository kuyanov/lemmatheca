import Lemmatheca.PaComputations.PAComputations
import Mathlib.ModelTheory.Definability

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
noncomputable section
universe u

theorem Program.graph_existsUnique_model {n : ℕ} (p : Program n)
    {M : Type u} [language.Structure M] [M ⊨ PA] (x : Fin n → M) :
    ∃! y : M, p.graph.Realize (extend x y) := by
  let : Nonempty M := ⟨zeroValue M⟩
  have ht : M ⊨ totalUnique p.graph :=
    derives_sound p.graph_total_unique default
      (fun _ h => Theory.realize_sentence_of_mem PA h)
  exact (realize_totalUnique p.graph).mp ht x

def Program.value {n : ℕ} (p : Program n) {M : Type u}
    [language.Structure M] [M ⊨ PA] (x : Fin n → M) : M :=
  Classical.choose (p.graph_existsUnique_model x)

theorem Program.value_graph {n : ℕ} (p : Program n) {M : Type u}
    [language.Structure M] [M ⊨ PA] (x : Fin n → M) :
    p.graph.Realize (extend x (p.value x)) := by
  exact (Classical.choose_spec (p.graph_existsUnique_model x)).1

theorem Program.value_iff {n : ℕ} (p : Program n) {M : Type u}
    [language.Structure M] [M ⊨ PA] (x : Fin n → M) (y : M) :
    p.graph.Realize (extend x y) ↔ y = p.value x := by
  constructor
  · exact (Classical.choose_spec (p.graph_existsUnique_model x)).2 y
  · intro hy
    exact hy ▸ p.value_graph x

theorem Program.value_numerals {n : ℕ} (p : Program n) {M : Type u}
    [language.Structure M] [M ⊨ PA] (x : Fin n → ℕ) :
    p.value (fun i => numeralValue M (x i)) = numeralValue M (p.eval x) := by
  let : Nonempty M := ⟨zeroValue M⟩
  let : M ⊨ Q := PA_models_Q M
  exact (stronglyRepresents_modelwise p.graph_numeralwise x _).mp (p.value_graph _)

theorem Program.value_nat {n : ℕ} (p : Program n) (x : Fin n → ℕ)
    [ℕ ⊨ PA] : p.value x = p.eval x := by
  simpa only [numeral_value_nat] using p.value_numerals (M := ℕ) x

theorem Program.value_comp {m n : ℕ} (f : Program m) (g : Fin m → Program n)
    {M : Type u} [language.Structure M] [M ⊨ PA] (x : Fin n → M) :
    (Program.comp f g).value x = f.value (fun i => (g i).value x) := by
  symm
  apply ((Program.comp f g).value_iff x _).mp
  rw [Program.graph, realize_compositionGraph]
  exact ⟨fun i => (g i).value x, fun i => (g i).value_graph x, f.value_graph _⟩

theorem Program.value_comp_one {n : ℕ} (f : Program 1) (g : Program n)
    {M : Type u} [language.Structure M] [M ⊨ PA] (x : Fin n → M) :
    (Program.comp f ![g]).value x = f.value ![g.value x] := by
  rw [Program.value_comp]
  congr 1
  funext i
  fin_cases i
  rfl

theorem Program.value_comp_two {n : ℕ} (f : Program 2) (g h : Program n)
    {M : Type u} [language.Structure M] [M ⊨ PA] (x : Fin n → M) :
    (Program.comp f ![g, h]).value x = f.value ![g.value x, h.value x] := by
  rw [Program.value_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem Program.value_comp_three {n : ℕ} (f : Program 3) (g h k : Program n)
    {M : Type u} [language.Structure M] [M ⊨ PA] (x : Fin n → M) :
    (Program.comp f ![g, h, k]).value x = f.value ![g.value x, h.value x, k.value x] := by
  rw [Program.value_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem Program.value_zero {M : Type u} [language.Structure M] [M ⊨ PA]
    (x : Fin 0 → M) : Program.zero.value x = zeroValue M := by
  have h := Program.zero.value_graph x
  simpa [Program.graph, termGraph, extend] using h

theorem Program.value_succ {M : Type u} [language.Structure M] [M ⊨ PA]
    (x : Fin 1 → M) : Program.succ.value x = succValue M (x 0) := by
  have h := Program.succ.value_graph x
  simpa [Program.graph, termGraph, extend] using h

theorem Program.value_proj {n : ℕ} (i : Fin n) {M : Type u}
    [language.Structure M] [M ⊨ PA] (x : Fin n → M) :
    (Program.proj i).value x = x i := by
  have h := (Program.proj i).value_graph x
  simpa [Program.graph, termGraph, extend] using h

theorem Program.value_rec_zero {n : ℕ} (f : Program n) (g : Program (n + 2))
    {M : Type u} [language.Structure M] [M ⊨ PA] (x : Fin n → M) :
    (Program.prec f g).value (Fin.snoc x (zeroValue M)) = f.value x := by
  symm
  apply ((Program.prec f g).value_iff _ _).mp
  exact ((Program.recursion_equations f g x (zeroValue M) (f.value x)).1).mpr (f.value_graph x)

theorem Program.value_rec_succ {n : ℕ} (f : Program n) (g : Program (n + 2))
    {M : Type u} [language.Structure M] [M ⊨ PA] (x : Fin n → M) (k : M) :
    (Program.prec f g).value (Fin.snoc x (succValue M k)) =
      g.value (Fin.snoc (Fin.snoc x k) ((Program.prec f g).value (Fin.snoc x k))) := by
  symm
  apply ((Program.prec f g).value_iff _ _).mp
  apply ((Program.recursion_equations f g x k _).2).mpr
  exact ⟨(Program.prec f g).value (Fin.snoc x k),
    (Program.prec f g).value_graph _, g.value_graph _⟩

@[fun_prop] theorem Program.value_definable {n : ℕ} (p : Program n)
    {M : Type u} [language.Structure M] [M ⊨ PA] :
    (Set.univ : Set M).DefinableFun language (fun x : Fin n → M => p.value x) := by
  apply Set.DefinableFun.of_empty
  rw [Set.empty_definableFun_iff]
  refine ⟨p.graph.relabel (Sum.elim some (fun _ => none)), ?_⟩
  ext v
  simp only [Function.tupleGraph, Set.mem_ofPred_eq, Formula.realize_relabel]
  have hv : v ∘ Sum.elim some (fun _ : Unit => none) = extend (v ∘ some) (v none) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => rfl
  rw [hv, p.value_iff]
  exact eq_comm

end
end Lemmatheca.ProofTheory.PAComputations
