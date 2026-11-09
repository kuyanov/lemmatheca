import Lemmatheca.IncomparableTuringDegrees.Prefixes
import Lemmatheca.TuringDegrees.Reductions
import Mathlib.Order.KonigLemma

/-! Finite Boolean prefix tables and successful-record use bounds. -/
namespace Lemmatheca.ComputabilityTheory.StrongReductions

open OracleComputation OracleProgramNumberings UniversalComputation PostsTheorem

noncomputable section


structure TableData where
  bound : ℕ → ℕ
  table : ℕ → ℕ → ℕ

def IsScheme (s : TableData) : Prop :=
  Computable s.bound ∧ Computable (fun p : ℕ × ℕ => s.table p.1 p.2) ∧
    ∀ x w, s.table x w = 0 ∨ s.table x w = 1

def Presents (s : TableData) (A B : Set ℕ) : Prop :=
  IsScheme s ∧ ∀ x, s.table x (prefixCode B (s.bound x)) = indicator (fun n => n ∈ A) x

def TruthTableReducible (A B : Set ℕ) : Prop := ∃ s : TableData, Presents s A B

def binaryRows : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (binaryRows n).flatMap (fun l => [l ++ [0], l ++ [1]])

def rowLookup (rows : List (ℕ × ℕ)) (w : ℕ) : ℕ :=
  ((rows.find? (fun p => p.1 == w)).map Prod.snd).getD 0

def tableRows (s : TableData) (x : ℕ) : List (ℕ × ℕ) :=
  (binaryRows (s.bound x)).map (fun l => (FiniteSequenceCoding.code l, s.table x (FiniteSequenceCoding.code l)))

def rowData (u : ℕ → ℕ) (r : ℕ → List (ℕ × ℕ)) : TableData :=
  ⟨u, fun x w => rowLookup (r x) w⟩

def IsRowPresentation (u : ℕ → ℕ) (r : ℕ → List (ℕ × ℕ)) : Prop :=
  Computable u ∧ Computable r ∧
    (∀ x, (r x).map Prod.fst = (binaryRows (u x)).map FiniteSequenceCoding.code) ∧
    ∀ x p, p ∈ r x → p.2 = 0 ∨ p.2 = 1

theorem binaryRows_spec (n : ℕ) :
    (∀ l, l ∈ binaryRows n ↔ IncomparableTuringDegrees.BinaryWord l ∧ l.length = n) ∧
      (binaryRows n).length = 2 ^ n ∧ (binaryRows n).Nodup := by
  induction n with
  | zero =>
    constructor
    · intro l
      simp only [binaryRows, List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨by simp [IncomparableTuringDegrees.BinaryWord], rfl⟩
      · rintro ⟨_, hl⟩
        exact List.length_eq_zero_iff.mp hl
    · simp [binaryRows]
  | succ n ih =>
    constructor
    · intro l
      simp only [binaryRows, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨a, ha, rfl | rfl⟩
        all_goals
          obtain ⟨hb, hn⟩ := (ih.1 a).mp ha
          refine ⟨?_, by simp [hn]⟩
          intro b h
          simp only [List.mem_append, List.mem_singleton] at h
          rcases h with h | rfl
          · exact hb b h
          · simp
      · rintro ⟨hb, hn⟩
        rcases List.eq_nil_or_concat' l with rfl | ⟨a, b, rfl⟩
        · simp at hn
        have ha : a ∈ binaryRows n := (ih.1 a).mpr
          ⟨fun z hz => hb z (List.mem_append_left _ hz), by simpa using hn⟩
        have hbit := hb b (by simp)
        rcases hbit with rfl | rfl
        · exact ⟨a, ha, Or.inl rfl⟩
        · exact ⟨a, ha, Or.inr rfl⟩
    · constructor
      · have hlen (ls : List (List ℕ)) :
            (ls.flatMap (fun l => [l ++ [0], l ++ [1]])).length = 2 * ls.length := by
          induction ls with
          | nil => simp
          | cons a ls h => simp [h, Nat.mul_add]
        rw [binaryRows, hlen, ih.2.1, pow_succ]
        omega
      · apply List.nodup_flatMap.mpr
        constructor
        · intro a _
          simp
        · apply ih.2.2.imp
          intro a b hab
          apply List.disjoint_left.mpr
          intro z hz hz'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz hz'
          rcases hz with rfl | rfl <;> rcases hz' with he | he
          all_goals
            apply hab
            simpa using congrArg List.dropLast he

theorem binaryRows_primrec : Primrec binaryRows := by
  have hs : Primrec (fun ls : List (List ℕ) =>
      ls.flatMap (fun l => [l ++ [0], l ++ [1]])) :=
    Primrec.list_flatMap Primrec.id
      ((Primrec.list_cons.comp (Primrec.list_concat.comp Primrec.snd (Primrec.const 0))
        (Primrec.list_cons.comp (Primrec.list_concat.comp Primrec.snd (Primrec.const 1))
          (Primrec.const []))).to₂)
  exact (Primrec.nat_rec₁ [[]] (hs.comp Primrec.snd).to₂).of_eq (fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp only [binaryRows, ih])

theorem computable_list_map {α β σ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable σ] [Inhabited β] {f : α → List β} {g : α → β → σ}
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a => (f a).map (g a)) := by
  let step (a : α) (p : ℕ × List σ) :=
    p.2 ++ [g a (((f a)[p.1]?).getD default)]
  have hstep : Computable₂ step :=
    (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hg.comp Computable.fst (Computable.option_getD
        (Computable.list_getElem?.comp (hf.comp Computable.fst)
          (Computable.fst.comp Computable.snd)) (Computable.const default)))).to₂
  have hc := Computable.nat_rec (Computable.list_length.comp hf) (Computable.const []) hstep
  apply hc.of_eq
  intro a
  have hi (n : ℕ) (hn : n ≤ (f a).length) :
      Nat.rec [] (fun j v => step a (j,v)) n = ((f a).take n).map (g a) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hlt : n < (f a).length := by omega
      simp only [step, ih (by omega),
        List.take_succ_eq_append_getElem hlt, List.map_append, List.map_singleton,
        List.getElem?_eq_getElem hlt, Option.getD_some]
  simpa using hi (f a).length le_rfl

theorem rowLookup_primrec : Primrec (fun p : List (ℕ × ℕ) × ℕ => rowLookup p.1 p.2) := by
  have hfind : Primrec (fun p : List (ℕ × ℕ) × ℕ =>
      p.1.findIdx (fun row => row.1 == p.2)) :=
    Primrec.list_findIdx Primrec.fst
      ((Primrec.beq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)).to₂)
  have hget := Primrec.list_getElem?.comp Primrec.fst hfind
  have hmap := Primrec.option_map hget (Primrec.snd.comp Primrec.snd).to₂
  exact (Primrec.option_getD.comp hmap (Primrec.const 0)).of_eq
    (fun p => by simp only [rowLookup, List.find?_eq_getElem?_findIdx])

private theorem rowLookup_mem (rows : List (ℕ × ℕ)) (w v : ℕ)
    (hd : (rows.map Prod.fst).Nodup) (hm : (w,v) ∈ rows) : rowLookup rows w = v := by
  induction rows with
  | nil => simp at hm
  | cons p rows ih =>
    simp only [List.map_cons, List.nodup_cons] at hd
    rcases List.mem_cons.mp hm with he | hm
    · subst p
      simp [rowLookup]
    · have hne : p.1 ≠ w := by
        intro he
        apply hd.1
        rw [he]
        exact List.mem_map.mpr ⟨(w,v),hm,rfl⟩
      simpa [rowLookup, List.find?_cons, hne] using ih hd.2 hm

theorem finite_row_representation (s : TableData) (hs : IsScheme s) :
    IsRowPresentation s.bound (tableRows s) ∧
      ∀ x l, IncomparableTuringDegrees.BinaryWord l → l.length = s.bound x →
        rowLookup (tableRows s x) (FiniteSequenceCoding.code l) = s.table x (FiniteSequenceCoding.code l) := by
  have hc : Computable (tableRows s) := computable_list_map
    (binaryRows_primrec.to_comp.comp hs.1)
    ((Primrec.encode.to_comp.comp Computable.snd).pair
      (hs.2.1.comp (Computable.fst.pair
        (Primrec.encode.to_comp.comp Computable.snd))))
  have hd (x : ℕ) : ((tableRows s x).map Prod.fst).Nodup := by
    simpa only [tableRows, List.map_map, Function.comp_def] using
      (binaryRows_spec (s.bound x)).2.2.map FiniteSequenceCoding.code_bijective.injective
  constructor
  · refine ⟨hs.1, hc, ?_, ?_⟩
    · intro x
      simp [tableRows, Function.comp_def]
    · intro x p hp
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hp
      exact hs.2.2 x (FiniteSequenceCoding.code l)
  · intro x l hl hn
    apply rowLookup_mem _ _ _ (hd x)
    exact List.mem_map.mpr ⟨l, (binaryRows_spec _).1 l |>.mpr ⟨hl,hn⟩, rfl⟩

theorem row_presentation_scheme (u : ℕ → ℕ) (r : ℕ → List (ℕ × ℕ))
    (hr : IsRowPresentation u r) :
    IsScheme (rowData u r) ∧
      ∀ x p, p ∈ r x → (rowData u r).table x p.1 = p.2 := by
  have hlook : Computable (fun p : List (ℕ × ℕ) × ℕ => rowLookup p.1 p.2) :=
    rowLookup_primrec.to_comp
  have hin : Computable (fun p : ℕ × ℕ => (r p.1, p.2)) :=
    (hr.2.1.comp Computable.fst).pair Computable.snd
  have hc : Computable (fun p : ℕ × ℕ => rowLookup (r p.1) p.2) :=
    Computable.comp (f := fun p : List (ℕ × ℕ) × ℕ => rowLookup p.1 p.2)
      (g := fun p : ℕ × ℕ => (r p.1, p.2)) hlook hin
  constructor
  · change Computable u ∧ Computable (fun p : ℕ × ℕ => rowLookup (r p.1) p.2) ∧ _
    refine ⟨hr.1, hc, ?_⟩
    intro x w
    change rowLookup (r x) w = 0 ∨ rowLookup (r x) w = 1
    unfold rowLookup
    cases he : (r x).find? (fun p => p.1 == w) with
    | none => simp
    | some p =>
      simpa using hr.2.2.2 x p (List.mem_of_find?_eq_some he)
  · intro x p hp
    apply rowLookup_mem (r x) p.1 p.2 _ hp
    rw [hr.2.2.1 x]
    exact (binaryRows_spec (u x)).2.2.map FiniteSequenceCoding.code_bijective.injective

def BoundedReduction (c : Code) (u : ℕ → ℕ) (A B : Set ℕ) : Prop :=
  Computable u ∧ ∀ x, ∃ τ : QueryRecord,
    Derives c x τ (indicator (fun n => n ∈ A) x) ∧ Consistent B τ ∧ useBound τ ≤ u x

def WeakTruthTableReducible (A B : Set ℕ) : Prop :=
  ∃ c : Code, ∃ u : ℕ → ℕ, BoundedReduction c u A B

theorem useBound_le_iff (τ : QueryRecord) (m : ℕ) :
    useBound τ ≤ m ↔ ∀ q ∈ querySet τ, q < m := by
  constructor
  · intro h q hq
    exact lt_of_lt_of_le ((useBound_spec τ).1 q hq) h
  · intro h
    exact Finset.sup_le (fun q hq => Nat.succ_le_of_lt (h q hq))

theorem bounded_replay {A B C : Set ℕ} {c : Code} {u : ℕ → ℕ}
    (h : BoundedReduction c u A B) (x : ℕ)
    (hC : ∀ q < u x, indicator (fun n => n ∈ C) q = indicator (fun n => n ∈ B) q) :
    eval C c x = Part.some (indicator (fun n => n ∈ A) x) := by
  obtain ⟨τ, hτ, hB, hu⟩ := h.2 x
  apply Part.eq_some_iff.mpr
  apply trace_sound hτ
  intro q b hb
  have hq : q ∈ querySet τ := by
    simp only [querySet, List.mem_toFinset, List.mem_map]
    exact ⟨(q,b), hb, rfl⟩
  exact (hB q b hb).trans (hC q ((useBound_le_iff τ (u x)).mp hu q hq)).symm

def AllOracleTotal (c : Code) : Prop := ∀ C : Set ℕ, ∀ x, (eval C c x).Dom

def BoundedAllowance (e : ℕ) (h : ℕ → ℕ) (A B : Set ℕ) : Prop :=
  Computable h ∧ ∀ x, boundedValue B (h x) e x = indicator (fun n => n ∈ A) x + 1

end
end Lemmatheca.ComputabilityTheory.StrongReductions
