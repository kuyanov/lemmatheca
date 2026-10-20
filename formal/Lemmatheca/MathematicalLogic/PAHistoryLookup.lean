import Lemmatheca.MathematicalLogic.PAHistoryPrograms

/-! Lookup invariants for the concrete increasing-order course-of-values
histories. All list and history induction predicates are arithmetic-definable,
so the claims include nonstandard internally finite histories. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

@[fun_prop] theorem program_snoc_definable {α : Type} {n : ℕ} (p : Program (n + 1))
    (f : (α → M) → Fin n → M) (g : (α → M) → M)
    (hf : ∀ i, (Set.univ : Set M).DefinableFun language (fun v => f v i))
    (hg : (Set.univ : Set M).DefinableFun language g) :
    (Set.univ : Set M).DefinableFun language (fun v => p.value (Fin.snoc (f v) (g v))) := by
  apply p.value_definable.comp
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using hg
  · simpa only [Fin.snoc_castSucc] using hf j

/-- Constructor induction on arithmetic-definable predicates at actual model
list codes, using the strictly smaller tail rather than external finiteness. -/
theorem list_code_induction (P : M → Prop)
    (hP : Set.univ.Definable₁ language {c | P c})
    (hzero : P (zeroValue M))
    (hcons : ∀ a c, P c → P (listCons.value ![a, c])) : ∀ c, P c := by
  apply definable_strong_induction P hP
  intro c ih
  by_cases hc : c = zeroValue M
  · simpa only [hc] using hzero
  · have hs := hcons (listHead.value ![c]) (listTail.value ![c])
      (ih _ (tail_smaller_value c hc))
    rwa [cons_head_tail_value c hc] at hs

theorem listLength_append_value (c d : M) :
    listLength.value ![listAppend.value ![c, d] ] =
      addValue M (listLength.value ![c]) (listLength.value ![d]) := by
  have hs : ∀ c : M, ∀ d : M,
      listLength.value ![listAppend.value ![c, d] ] =
        addValue M (listLength.value ![c]) (listLength.value ![d]) := by
    apply list_code_induction
    · change DPred (fun v : Fin 1 → M => ∀ d : M,
        listLength.value ![listAppend.value ![v 0, d] ] =
          addValue M (listLength.value ![v 0]) (listLength.value ![d]))
      pa_definable
    · intro d
      rw [listAppend_zero_value, listLength_zero_value, zero_add_value]
    · intro a c ih d
      rw [listAppend_cons_value, listLength_cons_value, listLength_cons_value, ih,
        successor_add_value]
  exact hs c d

theorem listEntry_append_left_value (c d i : M)
    (hi : leValue M (succValue M i) (listLength.value ![c])) :
    listEntry.value ![listAppend.value ![c, d], i] = listEntry.value ![c, i] := by
  have hs : ∀ c : M, ∀ d i : M,
      leValue M (succValue M i) (listLength.value ![c]) →
        listEntry.value ![listAppend.value ![c, d], i] = listEntry.value ![c, i] := by
    apply list_code_induction
    · change DPred (fun v : Fin 1 → M => ∀ d i : M,
        leValue M (succValue M i) (listLength.value ![v 0]) →
          listEntry.value ![listAppend.value ![v 0, d], i] = listEntry.value ![v 0, i])
      pa_definable
    · intro d i hi
      rw [listLength_zero_value] at hi
      exact False.elim (((successor_le_iff_lt i _).mp hi).2 (zero_le_value i))
    · intro a c ih d i hi
      by_cases hz : i = zeroValue M
      · rw [hz, listAppend_cons_value, listEntry_cons_zero_value, listEntry_cons_zero_value]
      · obtain ⟨j, rfl⟩ := PAComputations.predecessor i hz
        rw [listLength_cons_value] at hi
        rw [listAppend_cons_value, listEntry_cons_successor_value,
          listEntry_cons_successor_value]
        exact ih d j ((successor_le_successor_value_iff _ _).mp hi)
  exact hs c d i hi

theorem listEntry_append_at_value (c a : M) :
    listEntry.value ![listAppend.value ![c, listCons.value ![a, zeroValue M] ],
      listLength.value ![c] ] = a := by
  have hs : ∀ c : M, ∀ a : M,
      listEntry.value ![listAppend.value ![c, listCons.value ![a, zeroValue M] ],
        listLength.value ![c] ] = a := by
    apply list_code_induction
    · change DPred (fun v : Fin 1 → M => ∀ a : M,
        listEntry.value ![listAppend.value ![v 0, listCons.value ![a, zeroValue M] ],
          listLength.value ![v 0] ] = a)
      pa_definable
    · intro a
      rw [listAppend_zero_value, listLength_zero_value, listEntry_cons_zero_value]
    · intro b c ih a
      rw [listAppend_cons_value, listLength_cons_value, listEntry_cons_successor_value, ih]
  exact hs c a

theorem history_length_value {n : ℕ} (h : Program (n + 2)) (x : Fin n → M) (e : M) :
    listLength.value ![(history h).value (Fin.snoc x e)] = e := by
  apply definable_induction
    (fun e => listLength.value ![(history h).value (Fin.snoc x e)] = e)
  · change DPred (fun v : Fin 1 → M =>
      listLength.value ![(history h).value (Fin.snoc x (v 0))] = v 0)
    pa_definable
  · rw [history_zero_value, listLength_zero_value]
  · intro e he
    rw [history_successor_value, listLength_append_value, listLength_cons_value,
      listLength_zero_value, he, add_one_value]

theorem history_entry_value {n : ℕ} (h : Program (n + 2)) (x : Fin n → M) (e i : M)
    (hi : leValue M (succValue M i) e) :
    listEntry.value ![(history h).value (Fin.snoc x e), i] =
      (courseValue h).value (Fin.snoc x i) := by
  have hs : ∀ e : M, ∀ i : M, leValue M (succValue M i) e →
      listEntry.value ![(history h).value (Fin.snoc x e), i] =
        (courseValue h).value (Fin.snoc x i) := by
    apply definable_induction
    · change DPred (fun v : Fin 1 → M => ∀ i : M,
        leValue M (succValue M i) (v 0) →
          listEntry.value ![(history h).value (Fin.snoc x (v 0)), i] =
            (courseValue h).value (Fin.snoc x i))
      pa_definable
    · intro i hi
      exact False.elim (((successor_le_iff_lt i _).mp hi).2 (zero_le_value i))
    · intro e he i hi
      have hie : leValue M i e := (successor_le_successor_value_iff _ _).mp hi
      by_cases hieq : i = e
      · rw [hieq, history_successor_value]
        simpa only [history_length_value, courseValue_value] using
          listEntry_append_at_value ((history h).value (Fin.snoc x e))
            (h.value (Fin.snoc (Fin.snoc x e) ((history h).value (Fin.snoc x e))))
      · let := modelLinearOrder M
        have hil : leValue M (succValue M i) e :=
          (successor_le_iff_lt i e).mpr (lt_of_le_of_ne hie hieq)
        rw [history_successor_value, listEntry_append_left_value]
        · exact he i hil
        · rwa [history_length_value]
  exact hs e i hi

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms
