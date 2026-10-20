import Lemmatheca.MathematicalLogic.PAInternalFreshnessSentences
import Lemmatheca.MathematicalLogic.PAHistoryLookup

/-! PA derivations of the equations for the specified native list programs. -/
namespace Lemmatheca.MathematicalLogic.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open ProofPrograms
noncomputable section

private theorem vec1 {M : Type*} (x : Fin 1 → M) : x = ![x 0] := by
  funext i; fin_cases i; rfl
private theorem vec2 {M : Type*} (x : Fin 2 → M) : x = ![x 0, x 1] := by
  funext i; fin_cases i <;> rfl
theorem pair_left_derives : PAEquivalent
    (Program.comp unpairLeft ![squarePair]).graph (Program.proj (0 : Fin 2)).graph := by
  apply Program.equivalent_of_values
  intro M x
  rw [vec2 x]
  simpa [Program.value_comp_one, Program.value_proj] using unpairLeft_pair_value (x 0) (x 1)

theorem pair_right_derives : PAEquivalent
    (Program.comp unpairRight ![squarePair]).graph (Program.proj (1 : Fin 2)).graph := by
  apply Program.equivalent_of_values
  intro M x
  rw [vec2 x]
  simpa [Program.value_comp_one, Program.value_proj] using unpairRight_pair_value (x 0) (x 1)

theorem pair_reconstruction_derives : PAEquivalent
    (Program.comp squarePair ![unpairLeft, unpairRight]).graph (Program.proj (0 : Fin 1)).graph := by
  apply Program.equivalent_of_values
  intro M x
  rw [vec1 x]
  simpa [Program.value_comp_two, Program.value_proj] using pair_unpair_value (x 0)

theorem fold_zero_derives (h : Program 2) : PAEquivalent
    (Program.comp (foldInto h) ![constant 0, .proj 0]).graph (Program.proj (0 : Fin 1)).graph := by
  apply Program.equivalent_of_values
  intro M x
  simpa [Program.value_comp_two, Program.value_proj, constant_value,
    numeral_value_zero] using foldInto_zero_value h (x 0)

theorem fold_cons_derives (h : Program 2) : PAEquivalent
    (Program.comp (foldInto h) ![.comp listCons ![.proj 0, .proj 1], .proj (2 : Fin 3)]).graph
    (Program.comp (foldInto h) ![.proj 1, .comp h ![.proj (0 : Fin 3), .proj 2] ]).graph := by
  apply Program.equivalent_of_values
  intro M x
  simpa [Program.value_comp_two, Program.value_proj] using foldInto_cons_value h (x 0) (x 1) (x 2)

theorem parameterized_fold_zero_derives (h : Program 3) : PAEquivalent
    (Program.comp (paramFold h) ![.proj 0, constant 0, .proj (1 : Fin 2)]).graph
    (Program.proj (1 : Fin 2)).graph := by
  apply Program.equivalent_of_values
  intro M x
  simpa [Program.value_comp_three, Program.value_proj, constant_value,
    numeral_value_zero] using paramFold_zero_value h (x 0) (x 1)

theorem parameterized_fold_cons_derives (h : Program 3) : PAEquivalent
    (Program.comp (paramFold h) ![.proj 0, .comp listCons ![.proj 1, .proj 2], .proj (3 : Fin 4)]).graph
    (Program.comp (paramFold h) ![.proj 0, .proj 2, .comp h ![.proj (0 : Fin 4), .proj 1, .proj 3] ]).graph := by
  apply Program.equivalent_of_values
  intro M x
  simpa [Program.value_comp_three, Program.value_comp_two, Program.value_proj] using
    paramFold_cons_value h (x 0) (x 1) (x 2) (x 3)

theorem parameterized_fold_parameter_derives (h : Program 3) : PAEquivalent
    (Program.comp unpairLeft ![.comp (foldInto (paramFoldStep h))
      ![.proj 1, .comp squarePair ![.proj (0 : Fin 3), .proj 2] ] ]).graph
    (Program.proj (0 : Fin 3)).graph := by
  apply Program.equivalent_of_values
  intro M x
  simpa [Program.value_comp_one, Program.value_comp_two, Program.value_proj] using
    paramFold_parameter_value h (x 1) (x 0) (x 2)

theorem length_zero_derives : PAEquivalent
    (Program.comp listLength ![constant 0]).graph (constant (r := 0) 0).graph := by
  apply Program.equivalent_of_values
  intro M x
  simpa [Program.value_comp_one, constant_value, numeral_value_zero] using
    (listLength_zero_value (M := M))

theorem length_cons_derives : PAEquivalent
    (Program.comp listLength ![listCons]).graph
    (Program.comp .succ ![.comp listLength ![.proj (1 : Fin 2)] ]).graph := by
  apply Program.equivalent_of_values
  intro M x
  rw [vec2 x]
  simpa [Program.value_comp_one, Program.value_succ, Program.value_proj] using
    listLength_cons_value (x 0) (x 1)

theorem entry_cons_zero_derives : PAEquivalent
    (Program.comp listEntry ![listCons, constant 0]).graph (Program.proj (0 : Fin 2)).graph := by
  apply Program.equivalent_of_values
  intro M x
  rw [vec2 x]
  simpa [Program.value_comp_two, Program.value_proj, constant_value,
    numeral_value_zero] using listEntry_cons_zero_value (x 0) (x 1)

theorem entry_cons_successor_derives : PAEquivalent
    (Program.comp listEntry ![.comp listCons ![.proj 0, .proj 1], .comp .succ ![.proj (2 : Fin 3)] ]).graph
    (Program.comp listEntry ![.proj (1 : Fin 3), .proj 2]).graph := by
  apply Program.equivalent_of_values
  intro M x
  simpa [Program.value_comp_two, Program.value_comp_one, Program.value_succ,
    Program.value_proj] using listEntry_cons_successor_value (x 0) (x 1) (x 2)

theorem history_zero_derives {n : ℕ} (h : Program (n + 2)) : PAEquivalent
    (Program.comp (history h) (Fin.snoc (fun i : Fin n => Program.proj i) (constant 0))).graph
    (constant (r := n) 0).graph := by
  apply Program.equivalent_of_values
  intro M x
  rw [Program.value_comp, constant_value]
  have he : (fun i : Fin (n + 1) => ((Fin.snoc (fun i : Fin n => Program.proj i) (constant 0) : Fin (n + 1) → Program n) i).value x) =
      Fin.snoc x (zeroValue M) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Program.value_proj, constant_value, numeral_value_zero]
  rw [he, history_zero_value, numeral_value_zero]

theorem history_successor_derives {n : ℕ} (h : Program (n + 2)) : PAEquivalent
    (Program.comp (history h) (Fin.snoc
      (fun i : Fin n => Program.proj i.castSucc)
      (.comp .succ ![.proj (Fin.last n)]))).graph
    (Program.comp listAppend ![history h,
      .comp listCons ![.comp h (Fin.snoc (fun i : Fin (n + 1) => Program.proj i) (history h)), constant 0] ]).graph := by
  apply Program.equivalent_of_values
  intro M x
  rw [Program.value_comp, Program.value_comp_two]
  have he : (fun i : Fin (n + 1) => ((Fin.snoc
      (fun i : Fin n => Program.proj i.castSucc)
      (Program.comp .succ ![.proj (Fin.last n)]) : Fin (n + 1) → Program (n + 1)) i).value x) =
      Fin.snoc (fun i => x i.castSucc) (succValue M (x (Fin.last n))) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Program.value_proj, Program.value_comp_one, Program.value_succ]
  have hf : (fun i : Fin (n + 2) => ((Fin.snoc (fun i : Fin (n + 1) => Program.proj i) (history h) : Fin (n + 2) → Program (n + 1)) i).value x) =
      Fin.snoc x ((history h).value x) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Program.value_proj]
  rw [he, Program.value_comp_two, Program.value_comp, hf, constant_value, numeral_value_zero]
  have hx : Fin.snoc (fun i : Fin n => x i.castSucc) (x (Fin.last n)) = x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  convert history_successor_value h (fun i => x i.castSucc) (x (Fin.last n)) using 1
  rw [hx]

theorem history_length_derives {n : ℕ} (h : Program (n + 2)) : PAEquivalent
    (Program.comp listLength ![history h]).graph (Program.proj (Fin.last n)).graph := by
  apply Program.equivalent_of_values
  intro M x
  rw [Program.value_comp_one, Program.value_proj]
  have hx : Fin.snoc (fun i : Fin n => x i.castSucc) (x (Fin.last n)) = x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  have hval := history_length_value h (fun i => x i.castSucc) (x (Fin.last n))
  rw [hx] at hval
  exact hval


def courseValueSentence {n : ℕ} (h : Program (n + 2)) : language.Sentence :=
  let x : Fin (n + 1) → language.Term ((Fin (n + 1) ⊕ Unit) ⊕ Unit) :=
    fun i => .var (.inl (.inl i))
  let c : language.Term ((Fin (n + 1) ⊕ Unit) ⊕ Unit) := .var (.inl (.inr ()))
  let y : language.Term ((Fin (n + 1) ⊕ Unit) ⊕ Unit) := .var (.inr ())
  allClose ((graphAt (history h).graph x c).imp
    ((graphAt (courseValue h).graph x y).iff (graphAt h.graph (Fin.snoc x c) y)))

/-- The course value is the step's value at the actual decoded history output;
the conclusion relates three different graph formulas with an explicit history variable. -/
theorem course_value_derives {n : ℕ} (h : Program (n + 2)) :
    Derives PA (courseValueSentence h) := by
  apply derives_allClose_of_models
  intro M v
  simp only [Formula.realize_imp, Formula.realize_iff, realize_graphAt, Term.realize_var]
  let x : Fin (n + 1) → M := fun i => v (.inl (.inl i))
  let c := v (.inl (.inr ()))
  let y := v (.inr ())
  have he : (fun i : Fin (n + 2) =>
      ((Fin.snoc (fun j : Fin (n + 1) => Term.var (.inl (.inl j)))
        (Term.var (.inl (.inr ()))) : Fin (n + 2) →
          language.Term ((Fin (n + 1) ⊕ Unit) ⊕ Unit)) i).realize v) = Fin.snoc x c := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [x, c]
  rw [he]
  change (history h).graph.Realize (extend x c) →
    ((courseValue h).graph.Realize (extend x y) ↔ h.graph.Realize (extend (Fin.snoc x c) y))
  intro hh
  have hc := ((history h).value_iff x c).mp hh
  rw [Program.value_iff, Program.value_iff, hc]
  have hx : Fin.snoc (fun i : Fin n => x i.castSucc) (x (Fin.last n)) = x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  have hv := courseValue_value h (fun i => x i.castSucc) (x (Fin.last n))
  rw [hx] at hv
  rw [hv]

theorem numeral_no_free_names_derives : PAEquivalent
    (Program.comp (SyntaxPrograms.part 2) ![.comp SyntaxPrograms.stats ![numeral] ]).graph
    (constant (r := 1) 0).graph := by
  apply Program.equivalent_of_values
  intro M x
  rw [vec1 x]
  simp [Program.value_comp_one, SyntaxPrograms.numeral_stats_value,
    SyntaxPrograms.modelSummary_part_value, constant_value, numeral_value_zero]

private theorem snoc_value {m r : ℕ} (p : Fin m → Program r) (q : Program r)
    (M : Theory.ModelType.{0,0,0} PA) (v : Fin r → M) :
    (fun i : Fin (m + 1) => ((Fin.snoc p q : Fin (m + 1) → Program r) i).value v) =
      Fin.snoc (fun i => (p i).value v) (q.value v) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

def historyEntrySentence {n : ℕ} (h : Program (n + 2)) : language.Sentence :=
  let p : Fin n → Program (n + 2) := fun i => .proj i.castSucc.castSucc
  let e : Program (n + 2) := .proj (Fin.last n).castSucc
  let i : Program (n + 2) := .proj (Fin.last (n + 1))
  allClose ((ltFormula (.var (Fin.last (n + 1))) (.var (Fin.last n).castSucc)).imp
    (programEquation (.comp listEntry ![.comp (history h) (Fin.snoc p e), i])
      (.comp (courseValue h) (Fin.snoc p i))))

theorem history_entry_derives {n : ℕ} (h : Program (n + 2)) :
    Derives PA (historyEntrySentence h) := by
  apply derives_allClose_of_models
  intro M v
  simp only [Formula.realize_imp, ltFormula, realize_leFormula, realize_succTerm,
    Term.realize_var, realize_programEquation, Program.value_comp_two]
  simp only [Program.value_comp, snoc_value, Program.value_proj]
  exact history_entry_value h (fun i => v i.castSucc.castSucc)
    (v (Fin.last n).castSucc) (v (Fin.last (n + 1)))

end
end Lemmatheca.MathematicalLogic.PAComputations
