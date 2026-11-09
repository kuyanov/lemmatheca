import Lemmatheca.ArithmeticalHierarchy.Examples

/-! Two concrete search families in the established ordinary program numbering. -/
namespace Lemmatheca.ComputabilityTheory.IndexSetCompleteness

open UniversalComputation

set_option backward.isDefEq.respectTransparency false

abbrev Matrix := ℕ → ℕ → ℕ → Bool

def MatrixComputable (r : Matrix) : Prop :=
  Computable (fun p : (ℕ × ℕ) × ℕ => r p.1.1 p.1.2 p.2)

private def allLT {α : Type} (b : α → ℕ → Bool) (a : α) (n : ℕ) : Bool :=
  Nat.rec true (fun i acc => acc && b a i) n

private def anyLT {α : Type} (b : α → ℕ → Bool) (a : α) (n : ℕ) : Bool :=
  Nat.rec false (fun i acc => acc || b a i) n

def refutations (r : Matrix) (x n t : ℕ) : Bool :=
  allLT (fun p y => anyLT (fun q z => !(r q.1 q.2 z)) (p.1, y) p.2) (x,t) (n+1)

def Permanent (r : Matrix) (x a : ℕ) : Prop := ∀ z, r x a z = true

def totalSearch (r : Matrix) (x y : ℕ) : Part ℕ :=
  Nat.rfind (fun z => Part.some (r x y z))

def finiteSearch (r : Matrix) (x n : ℕ) : Part ℕ :=
  (Nat.rfind (fun t => Part.some (refutations r x n t))).map (fun _ => 0)

private theorem allLT_spec {α : Type} (b : α → ℕ → Bool) (a : α) (n : ℕ) :
    allLT b a n = true ↔ ∀ i < n, b a i = true := by
  induction n with
  | zero => simp [allLT]
  | succ n ih =>
    change (allLT b a n && b a n) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      by_cases hin : i < n
      · exact h i hin
      · have : i = n := by omega
        simpa [this] using hn
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

private theorem anyLT_spec {α : Type} (b : α → ℕ → Bool) (a : α) (n : ℕ) :
    anyLT b a n = true ↔ ∃ i < n, b a i = true := by
  induction n with
  | zero => simp [anyLT]
  | succ n ih =>
    change (anyLT b a n || b a n) = true ↔ _
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i,hi,hb⟩ | hb)
      · exact ⟨i,by omega,hb⟩
      · exact ⟨n,by omega,hb⟩
    · rintro ⟨i,hi,hb⟩
      by_cases hin : i < n
      · exact Or.inl ⟨i,hin,hb⟩
      · have : i = n := by omega
        exact Or.inr (this ▸ hb)

private theorem allLT_computable {α : Type} [Primcodable α]
    (b : α → ℕ → Bool) (hb : Computable₂ b) : Computable₂ (allLT b) := by
  have hs : Computable (fun p : (α × ℕ) × (ℕ × Bool) => p.2.2 && b p.1.1 p.2.1) :=
    Primrec.and.to_comp.comp (Computable.snd.comp Computable.snd)
      (hb.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))
  exact (Computable.nat_rec Computable.snd (Computable.const true) hs.to₂).of_eq
    (fun _ => rfl)

private theorem anyLT_computable {α : Type} [Primcodable α]
    (b : α → ℕ → Bool) (hb : Computable₂ b) : Computable₂ (anyLT b) := by
  have hs : Computable (fun p : (α × ℕ) × (ℕ × Bool) => p.2.2 || b p.1.1 p.2.1) :=
    Primrec.or.to_comp.comp (Computable.snd.comp Computable.snd)
      (hb.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))
  exact (Computable.nat_rec Computable.snd (Computable.const false) hs.to₂).of_eq
    (fun _ => rfl)

private theorem total_rfind_domain (b : ℕ → Bool) :
    (Nat.rfind (fun n => Part.some (b n))).Dom ↔ ∃ n, b n = true := by
  constructor
  · intro h
    obtain ⟨n,hn,_⟩ := Nat.rfind_dom.mp h
    exact ⟨n,(Part.mem_some_iff.mp hn).symm⟩
  · rintro ⟨n,hn⟩
    apply Nat.rfind_dom.mpr
    exact ⟨n,Part.mem_some_iff.mpr hn.symm,fun {_} _ => trivial⟩

theorem refutations_spec (r : Matrix) (x n t : ℕ) :
    refutations r x n t = true ↔ ∀ y ≤ n, ∃ z < t, r x y z = false := by
  simp only [refutations, allLT_spec, anyLT_spec, Bool.not_eq_true', Nat.lt_succ_iff]

theorem refutations_computable (r : Matrix) (hr : MatrixComputable r) :
    Computable (fun p : (ℕ × ℕ) × ℕ => refutations r p.1.1 p.1.2 p.2) := by
  have hn : Computable₂ (fun (q : ℕ × ℕ) z => !(r q.1 q.2 z)) :=
    Primrec.not.to_comp.comp hr
  have ha := anyLT_computable (fun (q : ℕ × ℕ) z => !(r q.1 q.2 z)) hn
  have hy : Computable₂ (fun (p : ℕ × ℕ) y =>
      anyLT (fun (q : ℕ × ℕ) z => !(r q.1 q.2 z)) (p.1,y) p.2) :=
    ha.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)
      (Computable.snd.comp Computable.fst)
  have hall := allLT_computable _ hy
  exact (hall.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)
    (Computable.succ.comp (Computable.snd.comp Computable.fst))).of_eq (fun _ => rfl)

theorem refutations_bound (r : Matrix) (x n : ℕ) :
    (∃ t, refutations r x n t = true) ↔ ∀ y ≤ n, ∃ z, r x y z = false := by
  constructor
  · rintro ⟨t,ht⟩ y hy
    obtain ⟨z,_,hz⟩ := (refutations_spec r x n t).mp ht y hy
    exact ⟨z,hz⟩
  · intro h
    have collect : ∀ m, (∀ y < m, ∃ z, r x y z = false) →
        ∃ t, ∀ y < m, ∃ z < t, r x y z = false := by
      intro m
      induction m with
      | zero => exact fun _ => ⟨0,fun y hy => False.elim (Nat.not_lt_zero y hy)⟩
      | succ m ih =>
        intro hm
        obtain ⟨t,ht⟩ := ih (fun y hy => hm y (by omega))
        obtain ⟨z,hz⟩ := hm m (by omega)
        refine ⟨max t (z+1),fun y hy => ?_⟩
        by_cases hym : y < m
        · obtain ⟨v,hv,hr⟩ := ht y hym
          exact ⟨v,hv.trans_le (le_max_left _ _),hr⟩
        · have : y = m := by omega
          subst y
          exact ⟨z,Nat.lt_of_lt_of_le (by omega) (le_max_right t (z+1)),hz⟩
    obtain ⟨t,ht⟩ := collect (n+1) (fun y hy => h y (by omega))
    exact ⟨t,(refutations_spec r x n t).mpr (fun y hy => ht y (by omega))⟩

theorem totalSearch_partial (r : Matrix) (hr : MatrixComputable r) :
    Nat.Partrec (Nat.unpaired (totalSearch r)) := by
  have hb : Partrec₂ (fun (p : ℕ × ℕ) z => Part.some (r p.1 p.2 z)) := hr
  exact Partrec.nat_iff.mp ((Partrec.rfind hb).comp Computable.unpair)

theorem totalSearch_domain (r : Matrix) (x y : ℕ) :
    (totalSearch r x y).Dom ↔ ∃ z, r x y z = true := by
  exact total_rfind_domain _

theorem totalSearch_least (r : Matrix) (x y z : ℕ) :
    z ∈ totalSearch r x y ↔ r x y z = true ∧ ∀ u < z, r x y u = false := by
  simp only [totalSearch, Nat.mem_rfind, Part.mem_some_iff, eq_comm]

theorem finiteSearch_partial (r : Matrix) (hr : MatrixComputable r) :
    Nat.Partrec (Nat.unpaired (finiteSearch r)) := by
  have hb : Partrec₂ (fun (p : ℕ × ℕ) t => Part.some (refutations r p.1 p.2 t)) :=
    refutations_computable r hr
  have hs := (Partrec.rfind hb).map (Computable.const (0 : ℕ)).to₂
  exact Partrec.nat_iff.mp (hs.comp Computable.unpair)

theorem finiteSearch_domain (r : Matrix) (x n : ℕ) :
    (finiteSearch r x n).Dom ↔ ∀ y ≤ n, ∃ z, r x y z = false := by
  change (Nat.rfind (fun t => Part.some (refutations r x n t))).Dom ↔ _
  rw [total_rfind_domain]
  exact refutations_bound r x n

theorem finiteSearch_output (r : Matrix) (x n y : ℕ) :
    y ∈ finiteSearch r x n ↔ y = 0 ∧ ∀ a ≤ n, ∃ z, r x a z = false := by
  constructor
  · intro hy
    obtain ⟨t,ht,hv⟩ := (Part.mem_map_iff _).mp hy
    exact ⟨hv.symm,(finiteSearch_domain r x n).mp hy.1⟩
  · rintro ⟨rfl,h⟩
    have hd := (finiteSearch_domain r x n).mpr h
    exact ⟨hd,rfl⟩

noncomputable def totalProgram (r : Matrix) (hr : MatrixComputable r) : ℕ :=
  Classical.choose (phi_complete (totalSearch_partial r hr))

noncomputable def totalMap (r : Matrix) (hr : MatrixComputable r) (x : ℕ) : ℕ :=
  specialize (totalProgram r hr) x

noncomputable def finiteProgram (r : Matrix) (hr : MatrixComputable r) : ℕ :=
  Classical.choose (phi_complete (finiteSearch_partial r hr))

noncomputable def finiteMap (r : Matrix) (hr : MatrixComputable r) (x : ℕ) : ℕ :=
  specialize (finiteProgram r hr) x

theorem totalProgram_eval (r : Matrix) (hr : MatrixComputable r) :
    phi (totalProgram r hr) = Nat.unpaired (totalSearch r) := by
  exact Classical.choose_spec (phi_complete (totalSearch_partial r hr))

theorem finiteProgram_eval (r : Matrix) (hr : MatrixComputable r) :
    phi (finiteProgram r hr) = Nat.unpaired (finiteSearch r) := by
  exact Classical.choose_spec (phi_complete (finiteSearch_partial r hr))

theorem totalMap_primitive (r : Matrix) (hr : MatrixComputable r) :
    Primrec (totalMap r hr) := by
  exact specialize_primitive.comp (Primrec.const _) Primrec.id

theorem finiteMap_primitive (r : Matrix) (hr : MatrixComputable r) :
    Primrec (finiteMap r hr) := by
  exact specialize_primitive.comp (Primrec.const _) Primrec.id

theorem totalMap_eval (r : Matrix) (hr : MatrixComputable r) (x y : ℕ) :
    phi (totalMap r hr x) y = totalSearch r x y := by
  rw [totalMap, specialize_eval, totalProgram_eval]
  simp only [Nat.unpaired, Nat.unpair_pair]

theorem finiteMap_eval (r : Matrix) (hr : MatrixComputable r) (x n : ℕ) :
    phi (finiteMap r hr x) n = finiteSearch r x n := by
  rw [finiteMap, specialize_eval, finiteProgram_eval]
  simp only [Nat.unpaired, Nat.unpair_pair]

theorem totalMap_correct (r : Matrix) (hr : MatrixComputable r) (x : ℕ) :
    totalMap r hr x ∈ Lemmatheca.Entry.ArithmeticalHierarchy.Totality ↔
      ∀ y, ∃ z, r x y z = true := by
  change (∀ y, (phi (totalMap r hr x) y).Dom) ↔ _
  simp only [totalMap_eval, totalSearch_domain]

theorem finiteMap_domain (r : Matrix) (hr : MatrixComputable r) (x n : ℕ) :
    n ∈ EffectiveEnumerations.indexSet (finiteMap r hr x) ↔
      ∀ y ≤ n, ∃ z, r x y z = false := by
  change (phi (finiteMap r hr x) n).Dom ↔ _
  rw [finiteMap_eval, finiteSearch_domain]

theorem finiteMap_initial_segment (r : Matrix) (hr : MatrixComputable r) (x a : ℕ)
    (ha : Permanent r x a) (hmin : ∀ y < a, ¬ Permanent r x y) :
    EffectiveEnumerations.indexSet (finiteMap r hr x) = Set.Iio a := by
  classical
  ext n
  rw [finiteMap_domain]
  change (∀ y ≤ n, ∃ z, r x y z = false) ↔ n < a
  constructor
  · intro h
    by_contra hn
    obtain ⟨z,hz⟩ := h a (by omega)
    have := ha z
    simp_all
  · intro hn y hy
    have hnp := hmin y (by omega)
    simp only [Permanent, not_forall] at hnp
    obtain ⟨z,hz⟩ := hnp
    exact ⟨z,Bool.eq_false_iff.mpr hz⟩

theorem finiteMap_empty (r : Matrix) (hr : MatrixComputable r) (x : ℕ)
    (h : Permanent r x 0) : EffectiveEnumerations.indexSet (finiteMap r hr x) = ∅ := by
  simpa using finiteMap_initial_segment r hr x 0 h (fun y hy => by omega)

theorem finiteMap_universal (r : Matrix) (hr : MatrixComputable r) (x : ℕ)
    (h : ¬∃ a, Permanent r x a) :
    EffectiveEnumerations.indexSet (finiteMap r hr x) = Set.univ := by
  classical
  ext n
  simp only [Set.mem_univ, iff_true]
  apply (finiteMap_domain r hr x n).mpr
  intro y _
  have hn : ¬ Permanent r x y := fun hy => h ⟨y,hy⟩
  simp only [Permanent, not_forall] at hn
  obtain ⟨z,hz⟩ := hn
  exact ⟨z,Bool.eq_false_iff.mpr hz⟩

theorem finiteMap_correct (r : Matrix) (hr : MatrixComputable r) (x : ℕ) :
    finiteMap r hr x ∈ Lemmatheca.Entry.ArithmeticalHierarchy.Finiteness ↔
      ∃ a, Permanent r x a := by
  classical
  constructor
  · intro hf
    by_contra h
    have he := finiteMap_universal r hr x h
    have hfin : (EffectiveEnumerations.indexSet (finiteMap r hr x)).Finite := hf
    rw [he] at hfin
    exact Set.infinite_univ hfin
  · intro h
    have ha := Nat.find_spec h
    have hm : ∀ y < Nat.find h, ¬ Permanent r x y := fun y hy => Nat.find_min h hy
    change (EffectiveEnumerations.indexSet (finiteMap r hr x)).Finite
    rw [finiteMap_initial_segment r hr x (Nat.find h) ha hm]
    exact Set.finite_Iio _

end Lemmatheca.ComputabilityTheory.IndexSetCompleteness
