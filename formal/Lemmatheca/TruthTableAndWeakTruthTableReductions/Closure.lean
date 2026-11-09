import Lemmatheca.TruthTableAndWeakTruthTableReductions.Characterization

/-! Substitution with bounded records, finite table composition, and Boolean closure. -/
namespace Lemmatheca.ComputabilityTheory.StrongReductions

open OracleComputation OracleProgramNumberings UniversalComputation PostsTheorem

noncomputable section

def compositionBound (u v : ℕ → ℕ) (x : ℕ) : ℕ := (Finset.range (u x)).sup v

def takeWord (w n : ℕ) : ℕ := FiniteSequenceCoding.code ((FiniteSequenceCoding.decode w).take n)

def compositeData (s t : TableData) : TableData :=
  ⟨compositionBound s.bound t.bound, fun x w =>
    if FiniteSequenceCoding.length w = compositionBound s.bound t.bound x then
      s.table x (FiniteSequenceCoding.code ((List.range (s.bound x)).map
        (fun i => t.table i (takeWord w (t.bound i)))))
    else 0⟩

theorem composition_bound_computable (u v : ℕ → ℕ) (hu : Computable u) (hv : Computable v) :
    Computable (compositionBound u v) := by
  have hlist : Computable (fun x => (List.range (u x)).map v) :=
    computable_list_map (Primrec.list_range.to_comp.comp hu) (hv.comp Computable.snd).to₂
  have hmax : Primrec (fun l : List ℕ => l.foldr max 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact (hmax.to_comp.comp hlist).of_eq (fun x => by
    change (List.map v (List.range (u x))).foldr (fun a b : ℕ => a ⊔ b) ⊥ = _
    rw [List.foldr_sup_eq_sup_toFinset]
    apply le_antisymm
    · apply Finset.sup_le
      intro z hz
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
      exact Finset.le_sup (f := v) (by simpa using hi)
    · apply Finset.sup_le
      intro i hi
      apply Finset.le_sup (f := id)
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨i, by simpa using hi, rfl⟩))

theorem takeWord_primrec : Primrec₂ takeWord := by
  exact (Primrec.encode.comp (Primrec.list_take.comp Primrec.snd
    ((Primrec.ofNat (List ℕ)).comp Primrec.fst))).to₂

theorem takeWord_prefix (B : Set ℕ) (m n : ℕ) (h : n ≤ m) :
    takeWord (prefixCode B m) n = prefixCode B n := by
  simp [takeWord, prefixCode, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem table_prefix_computable (s : TableData) (hs : IsScheme s) :
    Computable (fun p : ℕ × ℕ => s.table p.1 (takeWord p.2 (s.bound p.1))) := by
  exact hs.2.1.comp (Computable.fst.pair
    (takeWord_primrec.to_comp.comp Computable.snd (hs.1.comp Computable.fst)))

theorem composite_scheme {A B C : Set ℕ} {s t : TableData}
    (hs : Presents s A B) (ht : Presents t B C) :
    Presents (compositeData s t) A C := by
  have hw := composition_bound_computable s.bound t.bound hs.1.1 ht.1.1
  have hi : Computable (fun p : (ℕ × ℕ) × ℕ => t.table p.2
      (takeWord p.1.2 (t.bound p.2))) :=
    (table_prefix_computable t ht.1).comp
      (Computable.snd.pair (Computable.snd.comp Computable.fst))
  have hm : Computable (fun p : ℕ × ℕ => (List.range (s.bound p.1)).map
      (fun i => t.table i (takeWord p.2 (t.bound i)))) :=
    computable_list_map (Primrec.list_range.to_comp.comp (hs.1.1.comp Computable.fst)) hi.to₂
  have ho : Computable (fun p : ℕ × ℕ => s.table p.1 (FiniteSequenceCoding.code
      ((List.range (s.bound p.1)).map (fun i => t.table i (takeWord p.2 (t.bound i)))))) :=
    hs.1.2.1.comp (Computable.fst.pair (Computable.encode.comp hm))
  have hg : Computable (fun p : ℕ × ℕ => decide
      (FiniteSequenceCoding.length p.2 = compositionBound s.bound t.bound p.1)) :=
    Primrec.eq.decide.to_comp.comp
      (FiniteSequenceCoding.primrec_length.to_comp.comp Computable.snd) (hw.comp Computable.fst)
  have hc : Computable (fun p : ℕ × ℕ => (compositeData s t).table p.1 p.2) :=
    (Computable.cond hg ho (Computable.const 0)).of_eq
      (fun p => by simp only [Bool.cond_decide]; rfl)
  refine ⟨⟨hw, hc, ?_⟩, ?_⟩
  · intro x w
    change (if _ then _ else 0) = 0 ∨ (if _ then _ else 0) = 1
    split_ifs
    · exact hs.1.2.2 x _
    · exact Or.inl rfl
  · intro x
    dsimp only [compositeData]
    rw [(prefixCode_spec C _).1, ite_eq_left rfl]
    have he : (List.range (s.bound x)).map
        (fun i => t.table i (takeWord (prefixCode C (compositionBound s.bound t.bound x)) (t.bound i))) =
        (List.range (s.bound x)).map (indicator (fun n => n ∈ B)) := by
      apply List.map_congr_left
      intro i hi
      have hv : t.bound i ≤ compositionBound s.bound t.bound x :=
        Finset.le_sup (s := Finset.range (s.bound x)) (f := t.bound) (by simpa using hi)
      rw [takeWord_prefix C (compositionBound s.bound t.bound x) (t.bound i) hv]
      exact ht.2 i
    rw [he]
    exact hs.2 x

theorem tt_reflexive (A : Set ℕ) : TruthTableReducible A A := by
  exact ⟨manyOneData id, manyOne_scheme id Computable.id (fun _ => Iff.rfl)⟩

theorem tt_transitive {A B C : Set ℕ} (hAB : TruthTableReducible A B)
    (hBC : TruthTableReducible B C) : TruthTableReducible A C := by
  obtain ⟨s,hs⟩ := hAB
  obtain ⟨t,ht⟩ := hBC
  exact ⟨compositeData s t, composite_scheme hs ht⟩

theorem querySet_append (τ ρ : QueryRecord) : querySet (τ ++ ρ) = querySet τ ∪ querySet ρ := by
  simp [querySet, List.toFinset_append]

private theorem append_query_bound (v : ℕ → ℕ) (τ₀ τ₁ ρ₀ ρ₁ : QueryRecord)
    (h₀ : ∀ r ∈ querySet ρ₀, ∃ q ∈ querySet τ₀, r < v q)
    (h₁ : ∀ r ∈ querySet ρ₁, ∃ q ∈ querySet τ₁, r < v q) :
    ∀ r ∈ querySet (ρ₀ ++ ρ₁), ∃ q ∈ querySet (τ₀ ++ τ₁), r < v q := by
  simp only [querySet_append, Finset.mem_union]
  intro r hr
  rcases hr with hr | hr
  · obtain ⟨q,hq,h⟩ := h₀ r hr
    exact ⟨q,Or.inl hq,h⟩
  · obtain ⟨q,hq,h⟩ := h₁ r hr
    exact ⟨q,Or.inr hq,h⟩

theorem substituted_records {B C : Set ℕ} {c d : Code} {v : ℕ → ℕ}
    (hd : BoundedReduction d v B C) {x y : ℕ} {τ : QueryRecord}
    (hτ : Derives c x τ y) (hB : Consistent B τ) :
    ∃ ρ, Derives (subst d c) x ρ y ∧ Consistent C ρ ∧
      ∀ r ∈ querySet ρ, ∃ q ∈ querySet τ, r < v q := by
  revert hB
  induction hτ with
  | zero x =>
    intro _
    exact ⟨[], .zero x, by simp [Consistent], by simp [querySet]⟩
  | succ x =>
    intro _
    exact ⟨[], .succ x, by simp [Consistent], by simp [querySet]⟩
  | left x =>
    intro _
    exact ⟨[], .left x, by simp [Consistent], by simp [querySet]⟩
  | right x =>
    intro _
    exact ⟨[], .right x, by simp [Consistent], by simp [querySet]⟩
  | query q b hb =>
    intro hB
    have he : b = indicator (fun n => n ∈ B) q := hB q b (by simp)
    obtain ⟨ρ,hρ,hC,hu⟩ := hd.2 q
    refine ⟨ρ, by simpa only [subst,he] using hρ, hC, ?_⟩
    intro r hr
    exact ⟨q,by simp [querySet],(useBound_le_iff ρ _).mp hu r hr⟩
  | pair h₀ h₁ ih₀ ih₁ =>
    intro hB
    obtain ⟨hB₀,hB₁⟩ := (consistent_append_iff _ _ _).mp hB
    obtain ⟨ρ₀,hρ₀,hC₀,hq₀⟩ := ih₀ hB₀
    obtain ⟨ρ₁,hρ₁,hC₁,hq₁⟩ := ih₁ hB₁
    exact ⟨ρ₀ ++ ρ₁, .pair hρ₀ hρ₁,
      (consistent_append_iff _ _ _).mpr ⟨hC₀,hC₁⟩,
      append_query_bound _ _ _ _ _ hq₀ hq₁⟩
  | comp h₀ h₁ ih₀ ih₁ =>
    intro hB
    obtain ⟨hB₀,hB₁⟩ := (consistent_append_iff _ _ _).mp hB
    obtain ⟨ρ₀,hρ₀,hC₀,hq₀⟩ := ih₀ hB₀
    obtain ⟨ρ₁,hρ₁,hC₁,hq₁⟩ := ih₁ hB₁
    exact ⟨ρ₀ ++ ρ₁, .comp hρ₀ hρ₁,
      (consistent_append_iff _ _ _).mpr ⟨hC₀,hC₁⟩,
      append_query_bound _ _ _ _ _ hq₀ hq₁⟩
  | prec_succ h₀ h₁ ih₀ ih₁ =>
    intro hB
    obtain ⟨hB₀,hB₁⟩ := (consistent_append_iff _ _ _).mp hB
    obtain ⟨ρ₀,hρ₀,hC₀,hq₀⟩ := ih₀ hB₀
    obtain ⟨ρ₁,hρ₁,hC₁,hq₁⟩ := ih₁ hB₁
    exact ⟨ρ₀ ++ ρ₁, .prec_succ hρ₀ hρ₁,
      (consistent_append_iff _ _ _).mpr ⟨hC₀,hC₁⟩,
      append_query_bound _ _ _ _ _ hq₀ hq₁⟩
  | prec_zero h ih =>
    intro hB
    obtain ⟨ρ,hρ,hC,hq⟩ := ih hB
    exact ⟨ρ,.prec_zero hρ,hC,hq⟩
  | find_zero h ih =>
    intro hB
    obtain ⟨ρ,hρ,hC,hq⟩ := ih hB
    exact ⟨ρ,.find_zero hρ,hC,hq⟩
  | find_succ h₀ hv h₁ ih₀ ih₁ =>
    intro hB
    obtain ⟨hB₀,hB₁⟩ := (consistent_append_iff _ _ _).mp hB
    obtain ⟨ρ₀,hρ₀,hC₀,hq₀⟩ := ih₀ hB₀
    obtain ⟨ρ₁,hρ₁,hC₁,hq₁⟩ := ih₁ hB₁
    exact ⟨ρ₀ ++ ρ₁, .find_succ hρ₀ hv hρ₁,
      (consistent_append_iff _ _ _).mpr ⟨hC₀,hC₁⟩,
      append_query_bound _ _ _ _ _ hq₀ hq₁⟩

theorem substituted_bounded_reduction {A B C : Set ℕ} {c d : Code} {u v : ℕ → ℕ}
    (hc : BoundedReduction c u A B) (hd : BoundedReduction d v B C) :
    BoundedReduction (subst d c) (compositionBound u v) A C := by
  refine ⟨composition_bound_computable u v hc.1 hd.1, fun x => ?_⟩
  obtain ⟨τ,hτ,hB,hu⟩ := hc.2 x
  obtain ⟨ρ,hρ,hC,hq⟩ := substituted_records hd hτ hB
  refine ⟨ρ,hρ,hC,(useBound_le_iff ρ _).mpr (fun r hr => ?_)⟩
  obtain ⟨q,hqτ,hrq⟩ := hq r hr
  exact hrq.trans_le (Finset.le_sup (f := v)
    (Finset.mem_range.mpr ((useBound_le_iff τ _).mp hu q hqτ)))

theorem wtt_reflexive_program (A : Set ℕ) :
    BoundedReduction .query Nat.succ A A := by
  refine ⟨Computable.succ, fun x => ?_⟩
  refine ⟨[(x,indicator (fun n => n ∈ A) x)], .query _ _ (indicator_bits A x), ?_, ?_⟩
  · simp [Consistent]
  · simp [useBound, querySet]

theorem wtt_reflexive (A : Set ℕ) : WeakTruthTableReducible A A := by
  exact ⟨.query,Nat.succ,wtt_reflexive_program A⟩

theorem wtt_transitive {A B C : Set ℕ} (hAB : WeakTruthTableReducible A B)
    (hBC : WeakTruthTableReducible B C) : WeakTruthTableReducible A C := by
  obtain ⟨c,u,hc⟩ := hAB
  obtain ⟨d,v,hd⟩ := hBC
  exact ⟨subst d c, compositionBound u v, substituted_bounded_reduction hc hd⟩

def constantData (f : ℕ → ℕ) : TableData := ⟨fun _ => 0, fun x _ => f x⟩

def complementData (s : TableData) : TableData := ⟨s.bound, fun x w => 1 - s.table x w⟩

def BooleanOperation (op : ℕ → ℕ → ℕ) : Prop :=
  Computable (fun p : ℕ × ℕ => op p.1 p.2) ∧
    ∀ i j, (i = 0 ∨ i = 1) → (j = 0 ∨ j = 1) → op i j = 0 ∨ op i j = 1

def booleanData (op : ℕ → ℕ → ℕ) (s t : TableData) : TableData :=
  ⟨fun x => max (s.bound x) (t.bound x),
    fun x w => op (s.table x (takeWord w (s.bound x))) (t.table x (takeWord w (t.bound x)))⟩

def complementProgram (c : Code) : Code := .comp (embed zeroTest) c

def booleanProgram (op : ℕ → ℕ → ℕ) (hop : BooleanOperation op) (c d : Code) : Code :=
  .comp (embed (totalCode (fun p => op p.unpair.1 p.unpair.2)
    (hop.1.comp Computable.unpair))) (.pair c d)

theorem computable_scheme (A B : Set ℕ) (hA : ComputablePred (fun n => n ∈ A)) :
    Presents (constantData (indicator (fun n => n ∈ A))) A B := by
  classical
  have hc : Computable (indicator (fun n => n ∈ A)) := by
    exact ((Primrec.dom_bool₂ (fun b (_ : Bool) => if b then 1 else 0)).to_comp.comp
      hA.decide (Computable.const false)).of_eq (fun x => by simp [indicator])
  exact ⟨⟨Computable.const 0, hc.comp Computable.fst, fun x _ => indicator_bits A x⟩,
    fun _ => rfl⟩

theorem complement_scheme {A B : Set ℕ} {s : TableData} (hs : Presents s A B) :
    Presents (complementData s) Aᶜ B := by
  refine ⟨⟨hs.1.1, Primrec.nat_sub.to_comp.comp (Computable.const 1) hs.1.2.1, ?_⟩, ?_⟩
  · intro x w
    rcases hs.1.2.2 x w with h | h <;> simp [complementData,h]
  · intro x
    change 1 - s.table x (prefixCode B (s.bound x)) = _
    rw [hs.2 x]
    classical
    by_cases h : x ∈ A <;> simp [indicator,h]

theorem boolean_scheme {A D E B : Set ℕ} {s t : TableData} {op : ℕ → ℕ → ℕ}
    (hs : Presents s A B) (ht : Presents t D B) (hop : BooleanOperation op)
    (hE : ∀ x, op (indicator (fun n => n ∈ A) x) (indicator (fun n => n ∈ D) x) =
      indicator (fun n => n ∈ E) x) : Presents (booleanData op s t) E B := by
  have hc : Computable (fun p : ℕ × ℕ =>
      op (s.table p.1 (takeWord p.2 (s.bound p.1)))
        (t.table p.1 (takeWord p.2 (t.bound p.1)))) :=
    hop.1.comp ((table_prefix_computable s hs.1).pair (table_prefix_computable t ht.1))
  refine ⟨⟨Primrec.nat_max.to_comp.comp hs.1.1 ht.1.1, hc, ?_⟩, ?_⟩
  · intro x w
    exact hop.2 _ _ (hs.1.2.2 x _) (ht.1.2.2 x _)
  · intro x
    change op (s.table x (takeWord (prefixCode B (max (s.bound x) (t.bound x))) (s.bound x)))
      (t.table x (takeWord (prefixCode B (max (s.bound x) (t.bound x))) (t.bound x))) = _
    rw [takeWord_prefix B _ _ (le_max_left _ _), takeWord_prefix B _ _ (le_max_right _ _),
      hs.2 x, ht.2 x]
    exact hE x

theorem complement_bounded_reduction {A B : Set ℕ} {c : Code} {u : ℕ → ℕ}
    (h : BoundedReduction c u A B) : BoundedReduction (complementProgram c) u Aᶜ B := by
  refine ⟨h.1, fun x => ?_⟩
  obtain ⟨τ,hτ,hB,hu⟩ := h.2 x
  have hz : Nat.Partrec.Code.eval zeroTest (indicator (fun n => n ∈ A) x) =
      Part.some (indicator (fun n => n ∈ Aᶜ) x) := by
    rw [zeroTest_eval]
    classical
    by_cases hx : x ∈ A <;> simp [indicator,hx]
  refine ⟨τ, ?_,hB,hu⟩
  simpa only [complementProgram,List.append_nil] using
    Derives.comp hτ ((embed_empty_trace _ _ _).mp (Part.eq_some_iff.mp hz))

theorem boolean_bounded_reduction {A D E B : Set ℕ} {c d : Code} {u v : ℕ → ℕ}
    {op : ℕ → ℕ → ℕ} (hc : BoundedReduction c u A B) (hd : BoundedReduction d v D B)
    (hop : BooleanOperation op)
    (hE : ∀ x, op (indicator (fun n => n ∈ A) x) (indicator (fun n => n ∈ D) x) =
      indicator (fun n => n ∈ E) x) :
    BoundedReduction (booleanProgram op hop c d) (fun x => max (u x) (v x)) E B := by
  refine ⟨Primrec.nat_max.to_comp.comp hc.1 hd.1, fun x => ?_⟩
  obtain ⟨τ,hτ,hBτ,hu⟩ := hc.2 x
  obtain ⟨ρ,hρ,hBρ,hv⟩ := hd.2 x
  have hl : Derives (embed (totalCode (fun p => op p.unpair.1 p.unpair.2)
      (hop.1.comp Computable.unpair)))
      (Nat.pair (indicator (fun n => n ∈ A) x) (indicator (fun n => n ∈ D) x)) []
      (indicator (fun n => n ∈ E) x) := by
    apply (embed_empty_trace _ _ _).mp
    apply Part.eq_some_iff.mp
    simpa only [Nat.unpair_pair, hE x] using totalCode_eval
      (fun p => op p.unpair.1 p.unpair.2) (hop.1.comp Computable.unpair)
      (Nat.pair (indicator (fun n => n ∈ A) x) (indicator (fun n => n ∈ D) x))
  refine ⟨τ ++ ρ, ?_, (consistent_append_iff _ _ _).mpr ⟨hBτ,hBρ⟩, ?_⟩
  · simpa only [booleanProgram, List.append_nil] using Derives.comp (Derives.pair hτ hρ) hl
  · rw [useBound_append]
    exact max_le_max hu hv

def BooleanClosed (F : Set ℕ → Prop) : Prop :=
  (∀ A, ComputablePred (fun n => n ∈ A) → F A) ∧
  (∀ A, F A → F Aᶜ) ∧ ∀ A D, F A → F D → F (A ∪ D) ∧ F (A ∩ D)

private theorem max_boolean : BooleanOperation max := by
  refine ⟨Primrec.nat_max.to_comp, ?_⟩
  intro i j hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp

private theorem min_boolean : BooleanOperation min := by
  refine ⟨Primrec.nat_min.to_comp, ?_⟩
  intro i j hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp

private theorem union_indicator (A D : Set ℕ) (x : ℕ) :
    max (indicator (fun n => n ∈ A) x) (indicator (fun n => n ∈ D) x) =
      indicator (fun n => n ∈ A ∪ D) x := by
  classical
  by_cases ha : x ∈ A <;> by_cases hd : x ∈ D <;> simp [indicator,ha,hd]

private theorem intersection_indicator (A D : Set ℕ) (x : ℕ) :
    min (indicator (fun n => n ∈ A) x) (indicator (fun n => n ∈ D) x) =
      indicator (fun n => n ∈ A ∩ D) x := by
  classical
  by_cases ha : x ∈ A <;> by_cases hd : x ∈ D <;> simp [indicator,ha,hd]

theorem tt_boolean_closed (B : Set ℕ) : BooleanClosed (fun A => TruthTableReducible A B) := by
  refine ⟨fun A hA => ⟨constantData _,computable_scheme A B hA⟩, ?_, ?_⟩
  · rintro A ⟨s,hs⟩
    exact ⟨complementData s,complement_scheme hs⟩
  · rintro A D ⟨s,hs⟩ ⟨t,ht⟩
    exact ⟨⟨booleanData max s t,boolean_scheme hs ht max_boolean (union_indicator A D)⟩,
      ⟨booleanData min s t,boolean_scheme hs ht min_boolean (intersection_indicator A D)⟩⟩

theorem wtt_boolean_closed (B : Set ℕ) : BooleanClosed (fun A => WeakTruthTableReducible A B) := by
  refine ⟨fun A hA => tt_imp_wtt ⟨constantData _,computable_scheme A B hA⟩, ?_, ?_⟩
  · rintro A ⟨c,u,hc⟩
    exact ⟨complementProgram c,u,complement_bounded_reduction hc⟩
  · rintro A D ⟨c,u,hc⟩ ⟨d,v,hd⟩
    exact ⟨⟨booleanProgram max max_boolean c d,fun x => max (u x) (v x),
        boolean_bounded_reduction hc hd max_boolean (union_indicator A D)⟩,
      ⟨booleanProgram min min_boolean c d,fun x => max (u x) (v x),
        boolean_bounded_reduction hc hd min_boolean (intersection_indicator A D)⟩⟩

end
end Lemmatheca.ComputabilityTheory.StrongReductions
