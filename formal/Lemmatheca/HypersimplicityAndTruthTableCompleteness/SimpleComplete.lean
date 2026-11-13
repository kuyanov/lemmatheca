import Lemmatheca.HypersimplicityAndTruthTableCompleteness.Incompleteness
import Lemmatheca.DekkerDeficiencyAndHypersimpleSets.PostContrast

namespace Lemmatheca.ComputabilityTheory.HypersimplicityAndTruthTableCompleteness
open UniversalComputation EffectiveEnumerations StrongReductions HyperimmuneDegrees
open SimpleSets DekkerDeficiencyAndHypersimpleSets

/-- The specified recurrence leaves a Post-complement point in every finite block. -/
def codingEndpoints : ℕ → ℕ := Nat.rec 0 (fun _ n => 2 * n + 1)

def codingBlock (k : ℕ) : Finset ℕ := Finset.Ico (codingEndpoints k) (codingEndpoints (k + 1))

/-- Bounded search for the unique block containing this input. -/
def blockSelector (x : ℕ) : ℕ :=
  ((List.range (x + 1)).find? (fun k => decide (x < codingEndpoints (k + 1)))).getD 0

theorem coding_endpoints :
    Primrec codingEndpoints ∧ StrictMono codingEndpoints ∧ ∀ k, k ≤ codingEndpoints k := by
  have hp : Primrec codingEndpoints :=
    Primrec.nat_rec₁ 0 (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (Primrec.const 1))
  have hm : StrictMono codingEndpoints := strictMono_nat_of_lt_succ (fun k => by
    change codingEndpoints k < 2 * codingEndpoints k + 1
    omega)
  exact ⟨hp, hm, fun _ => hm.le_apply⟩

theorem block_selector :
    Primrec blockSelector ∧ ∀ x, blockSelector x ≤ x ∧
      x ∈ codingBlock (blockSelector x) ∧ ∀ k, x ∈ codingBlock k ↔ blockSelector x = k := by
  have hp := coding_endpoints.1
  have hr : Primrec (fun x : ℕ => List.range (x + 1)) :=
    Primrec.list_range.comp (Primrec.succ)
  have ht : Primrec (fun p : ℕ × ℕ => decide (p.1 < codingEndpoints (p.2 + 1))) :=
    (Primrec.nat_lt.comp Primrec.fst (hp.comp (Primrec.succ.comp Primrec.snd))).decide
  have hfind := Primrec.list_findIdx hr ht.to₂
  have hselector : Primrec blockSelector :=
    ((Primrec.option_getD.comp (Primrec.list_getElem?.comp hr hfind) (Primrec.const 0))).of_eq
      (fun x => by simp only [blockSelector, List.find?_eq_getElem?_findIdx])
  refine ⟨hselector, ?_⟩
  intro x
  let p : ℕ → Bool := fun k => decide (x < codingEndpoints (k + 1))
  let j := (List.range (x + 1)).findIdx p
  have hex : ∃ k ∈ List.range (x + 1), p k := by
    refine ⟨x, by simp, ?_⟩
    have h := coding_endpoints.2.2 (x + 1)
    simpa [p] using (show x < codingEndpoints (x + 1) by omega)
  have hjlt : j < (List.range (x + 1)).length := List.findIdx_lt_length_of_exists hex
  have hs : blockSelector x = j := by
    unfold blockSelector
    rw [List.find?_eq_getElem?_findIdx]
    change ((List.range (x + 1))[j]?).getD 0 = j
    rw [List.getElem?_eq_getElem hjlt, List.getElem_range, Option.getD_some]
  have hj : j ≤ x := by simpa using (Nat.le_of_lt_succ (by simpa using hjlt))
  have hu : x < codingEndpoints (j + 1) := by
    have ht' := @List.findIdx_getElem ℕ p (List.range (x + 1)) hjlt
    simpa [p, List.getElem_range] using ht'
  have hl : codingEndpoints j ≤ x := by
    cases hj0 : j with
    | zero => simp [codingEndpoints]
    | succ k =>
        have hn : k < (List.range (x + 1)).findIdx p := by change k < j; omega
        have hf := List.not_of_lt_findIdx hn
        have hnot : ¬ x < codingEndpoints (k + 1) := by
          simpa [p, List.getElem_range] using hf
        simpa [hj0] using Nat.le_of_not_gt hnot
  have hblock : x ∈ codingBlock (blockSelector x) := by
    rw [hs]
    exact Finset.mem_Ico.mpr ⟨hl, hu⟩
  refine ⟨hs ▸ hj, hblock, ?_⟩
  intro k
  constructor
  · intro hx
    have hk := Finset.mem_Ico.mp hx
    have hh := Finset.mem_Ico.mp hblock
    apply le_antisymm
    · by_contra hn
      have hle : codingEndpoints (k + 1) ≤ codingEndpoints (blockSelector x) :=
        coding_endpoints.2.1.monotone (by omega)
      omega
    · by_contra hn
      have hle : codingEndpoints (blockSelector x + 1) ≤ codingEndpoints k :=
        coding_endpoints.2.1.monotone (by omega)
      omega
  · intro hk
    simpa only [hk] using hblock

noncomputable def postOmission (k : ℕ) : ℕ :=
  increasingList postSetᶜ post_complement_infinite (codingEndpoints k)

theorem post_block_omission (k : ℕ) :
    postOmission k ∈ codingBlock k ∧ postOmission k ∉ postSet := by
  have hmono := (increasing_list_correct postSetᶜ post_complement_infinite).1.1
  have hmem : postOmission k ∈ postSetᶜ := by
    rw [← (increasing_list_correct postSetᶜ post_complement_infinite).1.2]
    exact ⟨codingEndpoints k, rfl⟩
  refine ⟨Finset.mem_Ico.mpr ⟨(show codingEndpoints k ≤ postOmission k from hmono.le_apply), ?_⟩, hmem⟩
  have hb := post_complement_principal_bound (codingEndpoints k)
  change postOmission k < 2 * codingEndpoints k + 1
  exact Nat.lt_succ_of_le hb

/-- The same Post set is enlarged, filling precisely the halting-indexed blocks. -/
def codingSet : Set ℕ := postSet ∪ {x | blockSelector x ∈ haltingDiagonal}

theorem coding_set_union :
    codingSet = postSet ∪ ⋃ k ∈ haltingDiagonal, (↑(codingBlock k) : Set ℕ) := by
  ext x
  simp only [codingSet, Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe]
  constructor
  · rintro (hx | hx)
    · exact Or.inl hx
    · exact Or.inr ⟨blockSelector x, hx, (block_selector.2 x).2.1⟩
  · rintro (hx | ⟨k, hk, hx⟩)
    · exact Or.inl hx
    · exact Or.inr (((block_selector.2 x).2.2 k).mp hx ▸ hk)

noncomputable def codingRecognizer (b x : ℕ) : Part ℕ := by
  classical
  exact (Nat.rfind (fun s => Part.some (decide
    (certificate b x s ∨ certificate (blockSelector x) (blockSelector x) s)))).map (fun _ => 0)

def CodingRecognizerIndex (v : ℕ) : Prop :=
  ∀ b x, phi v (Nat.pair b x) = codingRecognizer b x

def codingProgram (v b : ℕ) : ℕ := specialize v b

theorem coding_recognizer_partial : Partrec₂ codingRecognizer := by
  classical
  have hs : Primrec (fun t : (ℕ × ℕ) × ℕ => blockSelector t.1.2) :=
    block_selector.1.comp (Primrec.snd.comp Primrec.fst)
  have hR : PrimrecPred (fun t : (ℕ × ℕ) × ℕ =>
      certificate t.1.1 t.1.2 t.2 ∨
        certificate (blockSelector t.1.2) (blockSelector t.1.2) t.2) :=
    certificate_primitive.or (certificate_primitive.comp ((hs.pair hs).pair Primrec.snd))
  exact ((Partrec.rfind hR.decide.to_comp.partrec.to₂).map
    (Computable.const 0).to₂).of_eq (fun _ => rfl)

theorem coding_recognizer_index : ∃ v, CodingRecognizerIndex v := by
  obtain ⟨v, hv⟩ := phi_complete (Partrec₂.unpaired'.mpr coding_recognizer_partial)
  refine ⟨v, fun b x => ?_⟩
  simpa only [Nat.unpaired, Nat.unpair_pair] using congrFun hv (Nat.pair b x)

private theorem coding_recognizer_domain (b x : ℕ) :
    (codingRecognizer b x).Dom ↔ (phi b x).Dom ∨
      (phi (blockSelector x) (blockSelector x)).Dom := by
  classical
  change (Nat.rfind (fun s => Part.some (decide
    (certificate b x s ∨ certificate (blockSelector x) (blockSelector x) s)))).Dom ↔ _
  rw [phi_domain, phi_domain]
  constructor
  · intro h
    obtain ⟨s, hs, _⟩ := Nat.rfind_dom.mp h
    have hs' : certificate b x s ∨ certificate (blockSelector x) (blockSelector x) s := by
      simpa using hs
    exact hs'.elim (fun h => Or.inl ⟨s, h⟩) (fun h => Or.inr ⟨s, h⟩)
  · rintro (⟨s, hs⟩ | ⟨s, hs⟩)
    · exact Nat.rfind_dom.mpr ⟨s, by simp [hs], fun _ => trivial⟩
    · exact Nat.rfind_dom.mpr ⟨s, by simp [hs], fun _ => trivial⟩

theorem coding_program_correct (v : ℕ) (hv : CodingRecognizerIndex v) (b : ℕ)
    (hb : indexSet b = postSet) :
    indexSet (codingProgram v b) = codingSet ∧
      ∀ x y, y ∈ phi (codingProgram v b) x → y = 0 := by
  have heval (x : ℕ) : phi (codingProgram v b) x = codingRecognizer b x :=
    (specialize_eval v b x).trans (hv b x)
  constructor
  · ext x
    change (phi (codingProgram v b) x).Dom ↔ x ∈ codingSet
    rw [heval, coding_recognizer_domain]
    change x ∈ indexSet b ∨ blockSelector x ∈ haltingDiagonal ↔ x ∈ codingSet
    rw [hb]
    rfl
  · intro x y hy
    rw [heval] at hy
    obtain ⟨_, _, rfl⟩ := (Part.mem_map_iff (fun _ : ℕ => 0)).mp hy
    rfl

theorem coding_enumerable : REPred codingSet := by
  obtain ⟨b, hb⟩ := (enumerable_iff_index postSet).mp post_enumerable
  obtain ⟨v, hv⟩ := coding_recognizer_index
  have hset : indexSet b = postSet := Set.ext (fun x => (hb x).symm)
  have hc := (phi_recursive.comp (Computable.const (codingProgram v b)) Computable.id).dom_re
  change REPred (indexSet (codingProgram v b)) at hc
  rw [(coding_program_correct v hv b hset).1] at hc
  exact hc

/-- A total finite Boolean lookup, with zero on malformed or wrong-length words. -/
def codingTable (k word : ℕ) : ℕ :=
  if (FiniteSequenceCoding.decode word).length == codingEndpoints (k + 1) &&
      (FiniteSequenceCoding.decode word).all (fun bit => bit == 0 || bit == 1) &&
      (List.range' (codingEndpoints k) (codingEndpoints (k + 1) - codingEndpoints k)).all
        (fun x => FiniteSequenceCoding.entry word x == 1) then 1 else 0

def codingScheme : TableData := ⟨fun k => codingEndpoints (k + 1), codingTable⟩

private theorem block_list_all_primitive {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {g : α → β → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).all (g a)) := by
  have hfold := Primrec.list_foldr hf (Primrec.const true)
    (Primrec.and.comp (hg.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  apply hfold.of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b l ih => simp only [List.foldr_cons, List.all_cons, ih]

private theorem coding_table_primitive : Primrec (fun p : ℕ × ℕ => codingTable p.1 p.2) := by
  have he₀ : Primrec (fun p : ℕ × ℕ => codingEndpoints p.1) := coding_endpoints.1.comp Primrec.fst
  have he₁ : Primrec (fun p : ℕ × ℕ => codingEndpoints (p.1 + 1)) :=
    coding_endpoints.1.comp (Primrec.succ.comp Primrec.fst)
  have hdecode := (Primrec.ofNat (List ℕ)).comp (Primrec.snd : Primrec (Prod.snd : ℕ × ℕ → ℕ))
  have hlen := Primrec.beq.comp (Primrec.list_length.comp hdecode) he₁
  have hbits := block_list_all_primitive hdecode
    (Primrec.or.comp (Primrec.beq.comp Primrec.snd (Primrec.const 0))
      (Primrec.beq.comp Primrec.snd (Primrec.const 1))).to₂
  have hr : Primrec (fun p : ℕ × ℕ => List.range' p.1 p.2) := by
    simpa only [List.range'_eq_map_range] using
      (Primrec.list_map (Primrec.list_range.comp Primrec.snd)
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)
  have hblock := hr.comp (he₀.pair (Primrec.nat_sub.comp he₁ he₀))
  have hall := block_list_all_primitive hblock
    (Primrec.beq.comp
      (FiniteSequenceCoding.primrec_entry.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.const 1)).to₂
  have htest := Primrec.and.comp (Primrec.and.comp hlen hbits) hall
  exact (Primrec.cond htest (Primrec.const 1) (Primrec.const 0)).of_eq
    (fun p => by simp only [codingTable, Bool.cond_eq_ite])

theorem coding_table_scheme : IsScheme codingScheme ∧ ∀ A : Set ℕ, ∀ k,
    codingScheme.table k (PostsTheorem.prefixCode A (codingScheme.bound k)) =
      indicator (fun j => (↑(codingBlock j) : Set ℕ) ⊆ A) k := by
  classical
  constructor
  · refine ⟨(coding_endpoints.1.comp Primrec.succ).to_comp, coding_table_primitive.to_comp, ?_⟩
    intro k word
    change codingTable k word = 0 ∨ codingTable k word = 1
    unfold codingTable
    split_ifs <;> simp
  · intro A k
    let word := PostsTheorem.prefixCode A (codingEndpoints (k + 1))
    have hlen : (FiniteSequenceCoding.decode word).length = codingEndpoints (k + 1) :=
      (PostsTheorem.prefixCode_spec A _).1
    have hbinary := ComputableTreesAndPaths.prefix_code_valid A (codingEndpoints (k + 1))
    have hbits : (FiniteSequenceCoding.decode word).all (fun bit => bit == 0 || bit == 1) = true := by
      apply List.all_eq_true.mpr
      intro bit hb
      rcases hbinary bit hb with rfl | rfl <;> decide
    have hentry (x : ℕ) (hx : x < codingEndpoints (k + 1)) :
        FiniteSequenceCoding.entry word x = indicator (fun y => y ∈ A) x := by
      simp [word, PostsTheorem.prefixCode, FiniteSequenceCoding.entry, List.getElem?_range hx]
    have hn : codingEndpoints k ≤ codingEndpoints (k + 1) :=
      coding_endpoints.2.1.monotone (Nat.le_succ k)
    have hrange (x : ℕ) : x ∈ List.range' (codingEndpoints k)
        (codingEndpoints (k + 1) - codingEndpoints k) ↔ x ∈ codingBlock k := by
      simp only [List.mem_range'_1, codingBlock, Finset.mem_Ico]
      omega
    have hconj : (List.range' (codingEndpoints k)
        (codingEndpoints (k + 1) - codingEndpoints k)).all
          (fun x => FiniteSequenceCoding.entry word x == 1) = true ↔
        (↑(codingBlock k) : Set ℕ) ⊆ A := by
      rw [List.all_eq_true]
      constructor
      · intro h x hx
        have hbit : FiniteSequenceCoding.entry word x = 1 := by
          simpa only [beq_iff_eq] using h x ((hrange x).mpr hx)
        rw [hentry x (Finset.mem_Ico.mp hx).2] at hbit
        by_contra hnot
        simp [indicator, hnot] at hbit
      · intro h x hx
        rw [hentry x (Finset.mem_Ico.mp ((hrange x).mp hx)).2]
        simp [indicator, h ((hrange x).mp hx)]
    change codingTable k word = _
    unfold codingTable
    rw [show ((FiniteSequenceCoding.decode word).length == codingEndpoints (k + 1)) = true by simp [hlen], hbits]
    simp only [Bool.true_and]
    by_cases hsub : (↑(codingBlock k) : Set ℕ) ⊆ A
    · rw [hconj.mpr hsub]
      simp [indicator, hsub]
    · have hf : (List.range' (codingEndpoints k)
          (codingEndpoints (k + 1) - codingEndpoints k)).all
            (fun x => FiniteSequenceCoding.entry word x == 1) = false :=
        Bool.eq_false_iff.mpr (fun h => hsub (hconj.mp h))
      rw [hf]
      simp [indicator, hsub]

theorem coding_halting_iff (k : ℕ) :
    k ∈ haltingDiagonal ↔ (↑(codingBlock k) : Set ℕ) ⊆ codingSet := by
  constructor
  · intro hk x hx
    apply Or.inr
    change blockSelector x ∈ haltingDiagonal
    rw [((block_selector.2 x).2.2 k).mp hx]
    exact hk
  · intro h
    have hx := h (post_block_omission k).1
    rcases hx with hx | hx
    · exact False.elim ((post_block_omission k).2 hx)
    · have hb := ((block_selector.2 (postOmission k)).2.2 k).mp (post_block_omission k).1
      exact hb ▸ hx

theorem coding_table_correct : Presents codingScheme haltingDiagonal codingSet := by
  classical
  refine ⟨coding_table_scheme.1, ?_⟩
  intro k
  rw [coding_table_scheme.2 codingSet k]
  apply congrArg (fun p : Prop => if p then 1 else 0)
  exact propext (coding_halting_iff k).symm

theorem post_omission_membership (k : ℕ) : postOmission k ∈ codingSet ↔ k ∈ haltingDiagonal := by
  constructor
  · intro hx
    rcases hx with hx | hx
    · exact False.elim ((post_block_omission k).2 hx)
    · exact (((block_selector.2 (postOmission k)).2.2 k).mp (post_block_omission k).1) ▸ hx
  · intro hk
    exact (coding_halting_iff k).mp hk (post_block_omission k).1

theorem coding_complement_infinite : codingSetᶜ.Infinite := by
  have hK : haltingDiagonalᶜ.Infinite := by
    intro hf
    exact haltingDiagonal_complement_not_enumerable (finite_decidable hf).to_re
  have hi : Function.Injective postOmission :=
    (((increasing_list_correct postSetᶜ post_complement_infinite).1.1).comp
      coding_endpoints.2.1).injective
  apply (hK.image hi.injOn).mono
  rintro x ⟨k, hk, rfl⟩
  exact fun h => hk ((post_omission_membership k).mp h)

theorem coding_simple : Simple codingSet := by
  refine ⟨coding_enumerable, coding_complement_infinite, ?_⟩
  intro X hX hsub
  apply post_simple.2.2 X hX
  intro x hx hxB
  exact hsub hx (Or.inl hxB)

theorem simple_truth_table_complete :
    Simple codingSet ∧ TruthTableReducible codingSet haltingDiagonal ∧
      Presents codingScheme haltingDiagonal codingSet ∧
      ¬(haltingDiagonal ≤₀ codingSet) ∧ ¬Hypersimple codingSet := by
  refine ⟨coding_simple, ?_, coding_table_correct,
    simple_not_diagonal_reducible coding_simple, ?_⟩
  · exact manyOne_imp_tt (ProductiveAndCreativeSets.diagonal_complete coding_enumerable)
  · intro hhyper
    exact (hypersimple_incomplete codingSet hhyper).2 ⟨codingScheme, coding_table_correct⟩

end Lemmatheca.ComputabilityTheory.HypersimplicityAndTruthTableCompleteness
