import Lemmatheca.ComparingEnumerableSets.Classification
import Lemmatheca.RicesTheorem.RicesTheorem

namespace Lemmatheca.ComputabilityTheory.ComparingEnumerableSets
open UniversalComputation EffectiveEnumerations ArithmeticalHierarchy IndexSetCompleteness

local notation "TOT" => Lemmatheca.Entry.ArithmeticalHierarchy.Totality

local notation "FunctionEquality" => RicesTheorem.equivalentPrograms
def FunctionInequality : Set ℕ := FunctionEqualityᶜ

theorem function_equality_implies_domains (d e : ℕ) (h : phi d = phi e) :
    indexSet d = indexSet e := by
  ext x
  change (phi d x).Dom ↔ (phi e x).Dom
  rw [h]

def outputMatchTest (d e x k s : ℕ) : Prop :=
  k ≤ s ∧ (boundedValue k d x = 0 ∨ boundedValue s e x = boundedValue k d x) ∧
    (boundedValue k e x = 0 ∨ boundedValue s d x = boundedValue k e x)

theorem output_match_test_primitive : PrimrecPred (fun v : Tuple 5 =>
    outputMatchTest (v 0) (v 1) (v 2) (v 3) (v 4)) := by
  have c (i : Fin 5) : Primrec (fun v : Tuple 5 => v i) :=
    Primrec.fin_app.comp Primrec.id (Primrec.const i)
  have b (i j : Fin 5) : Primrec (fun v : Tuple 5 => boundedValue (v i) (v j) (v 2)) :=
    boundedValue_primitive.comp (((c i).pair (c j)).pair (c 2))
  exact (Primrec.nat_le.comp (c 3) (c 4)).and
    (((Primrec.eq.comp (b 3 0) (Primrec.const 0)).or (Primrec.eq.comp (b 4 1) (b 3 0))).and
      ((Primrec.eq.comp (b 3 1) (Primrec.const 0)).or (Primrec.eq.comp (b 4 0) (b 3 1))))

private theorem bounded_output_later {k s e x y : ℕ} (hks : k ≤ s)
    (h : boundedValue k e x = y + 1) : boundedValue s e x = y + 1 := by
  apply (boundedValue_output s e x y).mpr
  exact Nat.Partrec.Code.evaln_mono hks ((boundedValue_output k e x y).mp h)

private theorem eventual_output_match (d e x k : ℕ) (h : phi d x = phi e x) :
    ∃ t, ∀ s, t ≤ s → boundedValue k d x = 0 ∨ boundedValue s e x = boundedValue k d x := by
  by_cases hz : boundedValue k d x = 0
  · exact ⟨0, fun _ _ => Or.inl hz⟩
  · have hc : boundedValue k d x = (boundedValue k d x - 1) + 1 := by omega
    have hm : boundedValue k d x - 1 ∈ phi e x := h ▸ (phi_output d x _).mpr ⟨k, hc⟩
    obtain ⟨t, ht⟩ := (phi_output e x _).mp hm
    exact ⟨t, fun s hs => Or.inr ((bounded_output_later hs ht).trans hc.symm)⟩

theorem function_equality_normal_form (d e : ℕ) :
    phi d = phi e ↔ ∀ x k, ∃ s, outputMatchTest d e x k s := by
  constructor
  · intro h x k
    obtain ⟨u, hu⟩ := eventual_output_match d e x k (congrFun h x)
    obtain ⟨v, hv⟩ := eventual_output_match e d x k (congrFun h.symm x)
    refine ⟨max k (max u v), le_max_left _ _, hu _ ?_, hv _ ?_⟩
    · exact (le_max_left u v).trans (le_max_right k (max u v))
    · exact (le_max_right u v).trans (le_max_right k (max u v))
  · intro h
    funext x
    apply Part.ext
    intro y
    constructor
    · intro hy
      obtain ⟨k, hk⟩ := (phi_output d x y).mp hy
      obtain ⟨s, _, hm, _⟩ := h x k
      exact (phi_output e x y).mpr ⟨s, (hm.resolve_left (by omega)).trans hk⟩
    · intro hy
      obtain ⟨k, hk⟩ := (phi_output e x y).mp hy
      obtain ⟨s, _, _, hm⟩ := h x k
      exact (phi_output d x y).mpr ⟨s, (hm.resolve_left (by omega)).trans hk⟩

theorem function_equality_pi_two : Pi ∅ 2 FunctionEquality := by
  let R : ℕ → ℕ → ℕ → Prop := fun w a t =>
    outputMatchTest w.unpair.1 w.unpair.2 a.unpair.1 a.unpair.2 t
  have c (i : Fin 3) : Primrec (fun v : Tuple 3 => v i) :=
    Primrec.fin_app.comp Primrec.id (Primrec.const i)
  have hf : Primrec (fun v : Tuple 3 =>
      (![ (v 0).unpair.1, (v 0).unpair.2, (v 1).unpair.1,
        (v 1).unpair.2, v 2] : Tuple 5)) := by
    have h : ∀ i : Fin 5, Primrec (fun v : Tuple 3 =>
        (![ (v 0).unpair.1, (v 0).unpair.2, (v 1).unpair.1,
          (v 1).unpair.2, v 2] : Tuple 5) i) := by
      intro i
      fin_cases i
      · exact Primrec.fst.comp (Primrec.unpair.comp (c 0))
      · exact Primrec.snd.comp (Primrec.unpair.comp (c 0))
      · exact Primrec.fst.comp (Primrec.unpair.comp (c 1))
      · exact Primrec.snd.comp (Primrec.unpair.comp (c 1))
      · exact c 2
    exact Primrec.fin_curry.mpr (Primrec.fin_curry₁.mpr h).swap
  have hR : PrimrecPred (fun v : Tuple 3 => R (v 0) (v 1) (v 2)) :=
    output_match_test_primitive.comp hf
  have he (w : ℕ) : w ∈ FunctionEquality ↔ ∀ a, ∃ t, R w a t := by
    change phi w.unpair.1 = phi w.unpair.2 ↔ _
    rw [function_equality_normal_form]
    constructor
    · intro h a
      exact h a.unpair.1 a.unpair.2
    · intro h x k
      simpa [R] using h (Nat.pair x k)
  apply (unary_finite_bridge ∅ 2 false _).mp
  apply (finite_matrix_normal_form ∅ 2 false _).mpr
  refine ⟨fun v => R (v 0) (v 1) (v 2),
    (finite_decidable_empty_iff _).mpr hR.computablePred, ?_⟩
  intro x
  have hx := he (x 0)
  change FunctionEquality (x 0) ↔ _ at hx
  simpa [quantify, appendTuple, Fin.append, Fin.addCases] using hx

theorem function_inequality_sigma_two : Sigma ∅ 2 FunctionInequality := by
  exact (level_complement ∅ 2 false FunctionEquality).mp function_equality_pi_two

/-- Strictly run the input program, then erase its returned value. -/
def zeroOutputIndex (e : ℕ) : ℕ :=
  Encodable.encode (Nat.Partrec.Code.comp (Nat.Partrec.Code.const 0)
    (Denumerable.ofNat Nat.Partrec.Code e))

def functionTotalityMap (e : ℕ) : ℕ := Nat.pair (zeroOutputIndex e) wholeIndex

theorem zero_output_index_primitive : Primrec zeroOutputIndex := by
  exact Primrec.encode.comp
    (Nat.Partrec.Code.primrec₂_comp.comp (Primrec.const (Nat.Partrec.Code.const 0))
      (Primrec.ofNat Nat.Partrec.Code))

theorem zero_output_index_eval (e x : ℕ) :
    phi (zeroOutputIndex e) x = (phi e x).map (fun _ => 0) := by
  simp only [phi, zeroOutputIndex, Denumerable.ofNat_encode]
  change ((Denumerable.ofNat Nat.Partrec.Code e).eval x).bind (fun _ => Part.some 0) =
    ((Denumerable.ofNat Nat.Partrec.Code e).eval x).map (fun _ => 0)
  apply Part.ext
  intro y
  simp only [Part.mem_bind_iff, Part.mem_some_iff, Part.mem_map_iff]
  constructor <;> rintro ⟨a, ha, h⟩ <;> exact ⟨a, ha, h.symm⟩

theorem zero_output_index_spec (e x : ℕ) :
    (0 ∈ phi (zeroOutputIndex e) x ↔ (phi e x).Dom) ∧
      (∀ y, y ∈ phi (zeroOutputIndex e) x → y = 0) := by
  rw [zero_output_index_eval]
  constructor
  · simp only [Part.mem_map_iff, exists_and_right, Part.dom_iff_mem]
    simp
  · intro y hy
    obtain ⟨_, _, he⟩ := (Part.mem_map_iff _).mp hy
    exact he.symm

theorem function_totality_map_primitive : Primrec functionTotalityMap := by
  exact Primrec₂.natPair.comp zero_output_index_primitive (Primrec.const wholeIndex)

theorem function_totality_map_correct (e : ℕ) :
    functionTotalityMap e ∈ FunctionEquality ↔ e ∈ TOT := by
  simp only [functionTotalityMap, RicesTheorem.equivalentPrograms, Set.mem_ofPred_eq, Nat.unpair_pair]
  change phi (zeroOutputIndex e) = phi wholeIndex ↔ ∀ x, (phi e x).Dom
  constructor
  · intro h x
    apply (zero_output_index_spec e x).1.mp
    rw [congrFun h x, whole_index_output]
    exact Part.mem_some 0
  · intro h
    funext x
    rw [whole_index_output]
    exact Part.eq_some_iff.mpr ((zero_output_index_spec e x).1.mpr (h x))

noncomputable def functionComparisonMap (r : Matrix) (hr : MatrixComputable r) (x : ℕ) : ℕ :=
  functionTotalityMap (totalMap r hr x)

theorem function_comparison_primitive_hardness (A : Set ℕ) (hA : Pi ∅ 2 A) :
    ∃ r : Matrix, ∃ hr : MatrixComputable r,
      Primrec (functionComparisonMap r hr) ∧
      ∀ x, x ∈ A ↔ functionComparisonMap r hr x ∈ FunctionEquality := by
  obtain ⟨r, hr, _, he⟩ := totality_primitive_hardness A hA
  refine ⟨r, hr, function_totality_map_primitive.comp (totalMap_primitive r hr), fun x => ?_⟩
  exact (he x).trans (function_totality_map_correct (totalMap r hr x)).symm

theorem function_inequality_primitive_hardness (A : Set ℕ) (hA : Sigma ∅ 2 A) :
    ∃ r : Matrix, ∃ hr : MatrixComputable r,
      Primrec (functionComparisonMap r hr) ∧
      ∀ x, x ∈ A ↔ functionComparisonMap r hr x ∈ FunctionInequality := by
  classical
  have hc : Pi ∅ 2 (Aᶜ : Set ℕ) := (level_complement ∅ 2 true A).mp hA
  obtain ⟨r, hr, hp, he⟩ := function_comparison_primitive_hardness Aᶜ hc
  refine ⟨r, hr, hp, fun x => ?_⟩
  simpa only [FunctionInequality, Set.mem_compl_iff, not_not] using not_congr (he x)

theorem function_equality_complete : PiComplete FunctionEquality := by
  refine ⟨function_equality_pi_two, fun A hA => ?_⟩
  obtain ⟨r, hr, hp, he⟩ := function_comparison_primitive_hardness A hA
  exact ⟨functionComparisonMap r hr, hp.to_comp, he⟩

theorem function_inequality_complete : PostsTheorem.SigmaComplete ∅ 2 FunctionInequality := by
  refine ⟨function_inequality_sigma_two, fun A hA => ?_⟩
  obtain ⟨r, hr, hp, he⟩ := function_inequality_primitive_hardness A hA
  exact ⟨functionComparisonMap r hr, hp.to_comp, he⟩

theorem function_exact_levels :
    ¬ Sigma ∅ 2 FunctionEquality ∧ ¬ Pi ∅ 2 FunctionInequality := by
  constructor
  · intro hs
    apply (PostsTheorem.polarity_incomparable ∅ 2 (by decide)).2
    intro A hA
    exact manyOne_preimage ∅ 2 true A FunctionEquality (function_equality_complete.2 A hA) hs
  · exact (PostsTheorem.complete_boundaries ∅ 2 (by decide) FunctionInequality
      function_inequality_complete).1

theorem function_first_level_exclusions (H : Set ℕ)
    (hH : H = FunctionEquality ∨ H = FunctionInequality) :
    ¬ REPred H ∧ ¬ REPred (fun x => x ∉ H) ∧ ¬ ComputablePred H := by
  have hn : (¬ Sigma ∅ 2 H) ∨ (¬ Pi ∅ 2 H) := by
    rcases hH with rfl | rfl
    · exact Or.inl function_exact_levels.1
    · exact Or.inr function_exact_levels.2
  have hr : ¬ REPred H := by
    intro h
    have hs := (ordinary_sigma_one_iff_re H).mpr h
    rcases hn with hn | hn
    · exact hn (level_padding ∅ 1 true true H hs)
    · exact hn (level_padding ∅ 1 true false H hs)
  have hc : ¬ REPred (fun x => x ∉ H) := by
    intro h
    have hs := (ordinary_sigma_one_iff_re (fun x => x ∉ H)).mpr h
    have hp : Pi ∅ 1 H := (level_complement ∅ 1 false H).mpr hs
    rcases hn with hn | hn
    · exact hn (level_padding ∅ 1 false true H hp)
    · exact hn (level_padding ∅ 1 false false H hp)
  exact ⟨hr, hc, fun h => hr h.to_re⟩

end Lemmatheca.ComputabilityTheory.ComparingEnumerableSets
