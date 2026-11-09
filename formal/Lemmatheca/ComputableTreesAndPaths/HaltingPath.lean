import Lemmatheca.ComputableTreesAndPaths.Basic
import Lemmatheca.PaddingAndInjectiveReductions.Halting
import Lemmatheca.TuringJump.Core

/-! A fixed dying-cone recognizer, ordinary diagonal-halting queries and a specified oracle program. -/
namespace Lemmatheca.ComputabilityTheory.ComputableTreesAndPaths

open IncomparableTuringDegrees PostsTheorem UniversalComputation
open ProductiveAndCreativeSets PaddingAndInjectiveReductions OracleComputation
open OracleProgramNumberings

set_option backward.isDefEq.respectTransparency false

noncomputable section

def EmptyExtension (T : Set ℕ) (u m : ℕ) : Prop :=
  ∀ v ∈ binaryLevel (wordLength u + m), v ∈ T → ¬ Prefix u v

def Extendible (T : Set ℕ) (u : ℕ) : Prop := ∀ m, ¬ EmptyExtension T u m

def emptyTest (T : Set ℕ) (u m : ℕ) : Bool := by
  classical
  exact decide (EmptyExtension T u m)

theorem empty_extension_spec (T : Set ℕ) (hT : IsBinaryTree T) (u m : ℕ) :
    EmptyExtension T u m ↔
      ¬ ∃ v ∈ T, wordLength v = wordLength u + m ∧ Prefix u v := by
  constructor
  · rintro h ⟨v, hv, hl, hp⟩
    exact h v ((binary_level_spec _ _).mpr ⟨hT.1 _ hv, hl⟩) hv hp
  · intro h v hv hvt hp
    exact h ⟨v, hvt, ((binary_level_spec _ _).mp hv).2, hp⟩

theorem empty_test_computable (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T)) :
    Computable₂ (emptyTest T) := by
  classical
  have hb : Computable₂ (fun u v => decide (v ∈ T ∧ Prefix u v)) := by
    have h := (Primrec.dom_bool₂ Bool.and).to_comp.comp
      (hc.decide.comp Computable.snd) prefix_primitive.decide.to_comp
    exact h.to₂.of_eq (fun _ => by simp only [Bool.decide_and])
  have hl : Computable (fun p : ℕ × ℕ => binaryLevel (wordLength p.1 + p.2)) :=
    binary_level_primitive.to_comp.comp
      (Primrec.nat_add.to_comp.comp (FiniteSequenceCoding.primrec_length.to_comp.comp
        Computable.fst) Computable.snd)
  have hm := (computable_list_map (fun u v => decide (v ∈ T ∧ Prefix u v)) hb).comp
    Computable.fst hl
  have hp : ComputablePred (fun p : ℕ × ℕ => ∀ b ∈
      (binaryLevel (wordLength p.1 + p.2)).map
        (fun v => decide (v ∈ T ∧ Prefix p.1 v)), b = false) :=
    (((Primrec.eq.comp (Primrec.id : Primrec (fun b : Bool => b))
      (Primrec.const false)).forall_mem_list).decide.to_comp.comp hm).computablePred
  have he : ComputablePred (fun p : ℕ × ℕ => EmptyExtension T p.1 p.2) :=
    hp.of_eq (fun _ => by simp [EmptyExtension])
  exact he.decide

theorem empty_extension_persists (T : Set ℕ) (hT : IsBinaryTree T)
    (u m k : ℕ) (hm : EmptyExtension T u m) :
    EmptyExtension T u (m + k) := by
  rw [empty_extension_spec T hT] at hm ⊢
  rintro ⟨v, hv, hl, hp⟩
  let w := takeCode (wordLength u + m) v
  have hvalid := hT.1 v hv
  have hwp : Prefix w v := (take_spec _ _ hvalid).2
  have hwT : w ∈ T := hT.2 _ _ (take_valid _ _ hvalid) hv hwp
  have hwl : wordLength w = wordLength u + m := by
    rw [(take_spec _ _ hvalid).1, hl, min_eq_left (by omega)]
  exact hm ⟨w, hwT, hwl, prefix_take u v _ hvalid hp (by omega)⟩

def deadSearch (T : Set ℕ) (u : ℕ) : Part ℕ := by
  classical
  exact if ValidCode u then
    (Nat.rfind fun m => Part.some (emptyTest T u m)).map (fun _ => 0)
  else Part.none

theorem dead_search_recursive (T : Set ℕ)
    (hc : ComputablePred (fun u => u ∈ T)) : Nat.Partrec (deadSearch T) := by
  classical
  have hs := (Partrec.rfind (empty_test_computable T hc).partrec₂).map
    (Computable.const 0).to₂
  have hh := Partrec.cond valid_code_primitive.decide.to_comp hs Partrec.none
  apply Partrec.nat_iff.mp
  apply hh.of_eq
  intro u
  have he : (↑(emptyTest T u) : ℕ →. Bool) =
      (fun m => Part.some (emptyTest T u m)) := funext (PFun.coe_val _)
  simp only [Bool.cond_decide, deadSearch, he]

def deadCode (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T)) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp (dead_search_recursive T hc))

def deadIndex (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T)) : ℕ :=
  Encodable.encode (deadCode T hc)

def constantRunIndex : ℕ := Classical.choose constant_run_index_exists

def deadQuery (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T)) (u : ℕ) : ℕ :=
  enumerableMap constantRunIndex (deadIndex T hc) u

theorem dead_code_eval (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T)) (u : ℕ) :
    UniversalComputation.phi (deadIndex T hc) u = deadSearch T u := by
  unfold UniversalComputation.phi deadIndex
  rw [Denumerable.ofNat_encode]
  exact congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp (dead_search_recursive T hc))) u

theorem dead_search_domain (T : Set ℕ) (u : ℕ) :
    (deadSearch T u).Dom ↔ ValidCode u ∧ ∃ m, EmptyExtension T u m := by
  classical
  by_cases hu : ValidCode u
  · simp [deadSearch, hu, emptyTest]
  · simp [deadSearch, hu]

theorem dead_query_primitive (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T)) :
    Primrec (deadQuery T hc) := by
  exact enumerableMap_primitive _ _

theorem dead_query_correct (T : Set ℕ) (hc : ComputablePred (fun u => u ∈ T))
    (u : ℕ) (hu : ValidCode u) :
    deadQuery T hc u ∈ haltingDiagonal ↔ ∃ m, EmptyExtension T u m := by
  have hv : ConstantRunIndex constantRunIndex := Classical.choose_spec constant_run_index_exists
  rw [deadQuery, ← enumerableMap_membership _ hv]
  change (UniversalComputation.phi (deadIndex T hc) u).Dom ↔ _
  rw [dead_code_eval, dead_search_domain]
  simp [hu]

theorem one_child_survives (T : Set ℕ) (hT : IsBinaryTree T) (u : ℕ)
    (_hu : ValidCode u) (he : Extendible T u) :
    Extendible T (appendBit u 0) ∨ Extendible T (appendBit u 1) := by
  classical
  by_contra hn
  have hn0 : ¬ Extendible T (appendBit u 0) := fun h => hn (Or.inl h)
  have hn1 : ¬ Extendible T (appendBit u 1) := fun h => hn (Or.inr h)
  simp only [Extendible, not_forall, not_not] at hn0 hn1
  obtain ⟨m0, hm0⟩ := hn0
  obtain ⟨m1, hm1⟩ := hn1
  let l := max m0 m1
  have hm0' : EmptyExtension T (appendBit u 0) l := by
    convert empty_extension_persists T hT _ m0 (l - m0) hm0 using 1
    dsimp [l]
    omega
  have hm1' : EmptyExtension T (appendBit u 1) l := by
    convert empty_extension_persists T hT _ m1 (l - m1) hm1 using 1
    dsimp [l]
    omega
  obtain ⟨v, hvT, hvl, hp⟩ :
      ∃ v ∈ T, wordLength v = wordLength u + (1 + l) ∧ Prefix u v := by
    simpa only [empty_extension_spec T hT, not_not] using he (1 + l)
  have hlt : wordLength u < wordLength v := by omega
  have impossible (b : ℕ) (hb : wordBit v (wordLength u) = b)
      (hbb : b = 0 ∨ b = 1) (hempty : EmptyExtension T (appendBit u b) l) : False := by
    apply (empty_extension_spec T hT _ _).mp hempty
    refine ⟨v, hvT, ?_, append_prefix _ _ _ hp hlt hb hbb⟩
    rw [(appendBit_spec _ _).1]
    omega
  rcases beta_bits v (wordLength u) with h0 | h1
  · exact impossible 0 h0 (Or.inl rfl) hm0'
  · exact impossible 1 h1 (Or.inr rfl) hm1'

def leftInput (δ : ℕ → ℕ) (u : ℕ) : ℕ := δ (appendBit u 0)

def selectedWord (δ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => appendBit (selectedWord δ n)
      (indicator (fun e => e ∈ haltingDiagonal) (leftInput δ (selectedWord δ n)))

def selectedBit (δ : ℕ → ℕ) (n : ℕ) : ℕ :=
  indicator (fun e => e ∈ haltingDiagonal) (leftInput δ (selectedWord δ n))

def selectedPath (δ : ℕ → ℕ) : Set ℕ := {n | selectedBit δ n = 1}

theorem left_input_primitive (δ : ℕ → ℕ) (hδ : Primrec δ) :
    Primrec (leftInput δ) := by
  exact hδ.comp (appendBit_primitive.comp Primrec.id (Primrec.const 0))

def queryCode (δ : ℕ → ℕ) (hδ : Primrec δ) : OracleComputation.Code :=
  .comp .query (embed (ordinaryCode (leftInput δ)
    (Primrec.nat_iff.mp (left_input_primitive δ hδ))))

def appendPairCode : Nat.Partrec.Code :=
  ordinaryCode (fun z : ℕ => appendBit z.unpair.1 z.unpair.2)
    (Primrec.nat_iff.mp (appendBit_primitive.comp
      (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))

def stepCode (δ : ℕ → ℕ) (hδ : Primrec δ) : OracleComputation.Code :=
  .comp (embed appendPairCode) (.pair identityCode (queryCode δ hδ))

def wordsCode (δ : ℕ → ℕ) (hδ : Primrec δ) : OracleComputation.Code :=
  .comp (.prec .zero (.comp (stepCode δ hδ) (.comp .right .right)))
    (.pair .zero identityCode)

def pathCode (δ : ℕ → ℕ) (hδ : Primrec δ) : OracleComputation.Code :=
  .comp (queryCode δ hδ) (wordsCode δ hδ)

theorem selected_words_correct (T : Set ℕ) (hT : IsBinaryTree T)
    (hc : ComputablePred (fun u => u ∈ T)) (hi : ∀ n, HasLevel T n) (n : ℕ) :
    ValidCode (selectedWord (deadQuery T hc) n) ∧
      wordLength (selectedWord (deadQuery T hc) n) = n ∧
      Extendible T (selectedWord (deadQuery T hc) n) ∧
      Realizes (selectedWord (deadQuery T hc) n) (selectedPath (deadQuery T hc)) := by
  classical
  let δ := deadQuery T hc
  have hinv (k : ℕ) : ValidCode (selectedWord δ k) ∧
      wordLength (selectedWord δ k) = k ∧ Extendible T (selectedWord δ k) := by
    induction k with
    | zero =>
      refine ⟨by simp [selectedWord, ValidCode, BinaryWord],
        by simp [selectedWord, wordLength, FiniteSequenceCoding.length], ?_⟩
      intro m hm
      obtain ⟨v, hv, hl⟩ := hi m
      apply (empty_extension_spec T hT 0 m).mp hm
      refine ⟨v, hv, ?_, ?_⟩
      · simpa [wordLength, FiniteSequenceCoding.length] using hl
      · refine ⟨by simp [wordLength, FiniteSequenceCoding.length], ?_⟩
        intro q hq
        simp [wordLength, FiniteSequenceCoding.length] at hq
    | succ k ih =>
      refine ⟨append_valid _ _ ih.1, ?_, ?_⟩
      · change wordLength (appendBit (selectedWord δ k) _) = k + 1
        rw [(appendBit_spec _ _).1, ih.2.1]
      · change Extendible T (appendBit (selectedWord δ k)
          (indicator (fun e => e ∈ haltingDiagonal) (leftInput δ (selectedWord δ k))))
        by_cases hq : leftInput δ (selectedWord δ k) ∈ haltingDiagonal
        · simp only [indicator, hq, ↓reduceIte]
          rcases one_child_survives T hT _ ih.1 ih.2.2 with hleft | hright
          · obtain ⟨m, hm⟩ := (dead_query_correct T hc _
              (append_valid _ _ ih.1)).mp hq
            exact False.elim (hleft m hm)
          · exact hright
        · simp only [indicator, hq, ↓reduceIte]
          intro m hm
          exact hq ((dead_query_correct T hc _ (append_valid _ _ ih.1)).mpr ⟨m, hm⟩)
  have hp (k : ℕ) : Prefix (selectedWord δ k) (selectedWord δ (k + 1)) :=
    (appendBit_spec _ _).2.1
  have hg (k : ℕ) : k ≤ wordLength (selectedWord δ k) := (hinv k).2.1.ge
  have hsets : unionSet (selectedWord δ) = selectedPath δ := by
    ext q
    change wordBit (selectedWord δ (q + 1)) q = 1 ↔ selectedBit δ q = 1
    change wordBit (appendBit (selectedWord δ q) (selectedBit δ q)) q = 1 ↔ _
    have hl := (hinv q).2.1
    have he := (appendBit_spec (selectedWord δ q) (selectedBit δ q)).2.2
    rw [hl] at he
    rw [he]
    unfold selectedBit
    by_cases hq : leftInput δ (selectedWord δ q) ∈ haltingDiagonal <;>
      simp [indicator, hq]
  have hr := (coherent_union (selectedWord δ) hp hg).1 n
  rw [hsets] at hr
  exact ⟨(hinv n).1, (hinv n).2.1, (hinv n).2.2, hr⟩

theorem path_code_eval (δ : ℕ → ℕ) (hδ : Primrec δ) (n : ℕ) :
    eval haltingDiagonal (pathCode δ hδ) n = Part.some (selectedBit δ n) := by
  have hq (u : ℕ) : eval haltingDiagonal (queryCode δ hδ) u =
      Part.some (indicator (fun e => e ∈ haltingDiagonal) (leftInput δ u)) := by
    simp only [queryCode, eval, eval_embed, ordinaryCode_eval, Part.bind_some]
  have hs (u : ℕ) : eval haltingDiagonal (stepCode δ hδ) u =
      Part.some (appendBit u
        (indicator (fun e => e ∈ haltingDiagonal) (leftInput δ u))) := by
    have hp : eval haltingDiagonal (.pair identityCode (queryCode δ hδ)) u =
        Part.some (Nat.pair u
          (indicator (fun e => e ∈ haltingDiagonal) (leftInput δ u))) := by
      simp only [eval, identity_eval, hq, Part.bind_some, Part.map_some]
    change (eval haltingDiagonal (.pair identityCode (queryCode δ hδ)) u).bind
      (eval haltingDiagonal (embed appendPairCode)) = _
    rw [hp, Part.bind_some, eval_embed]
    simp only [appendPairCode, ordinaryCode_eval, Nat.unpair_pair]
  have hw (k : ℕ) : eval haltingDiagonal
      (.prec .zero (.comp (stepCode δ hδ) (.comp .right .right))) (Nat.pair 0 k) =
      Part.some (selectedWord δ k) := by
    induction k with
    | zero => simp [eval, selectedWord]
    | succ k ih =>
      rw [eval_prec_succ, ih, Part.bind_some]
      change (eval haltingDiagonal (.comp .right .right)
        (Nat.pair 0 (Nat.pair k (selectedWord δ k)))).bind
          (eval haltingDiagonal (stepCode δ hδ)) = _
      simp only [eval, Nat.unpair_pair, Part.bind_some]
      exact hs (selectedWord δ k)
  have hwords : eval haltingDiagonal (wordsCode δ hδ) n =
      Part.some (selectedWord δ n) := by
    have hp : eval haltingDiagonal (.pair .zero identityCode) n =
        Part.some (Nat.pair 0 n) := by simp [eval, identity_eval]
    change (eval haltingDiagonal (.pair .zero identityCode) n).bind
      (eval haltingDiagonal
        (.prec .zero (.comp (stepCode δ hδ) (.comp .right .right)))) = _
    rw [hp, Part.bind_some]
    exact hw n
  change (eval haltingDiagonal (wordsCode δ hδ) n).bind
    (eval haltingDiagonal (queryCode δ hδ)) = _
  rw [hwords, Part.bind_some]
  exact hq (selectedWord δ n)

theorem path_code_reduces (δ : ℕ → ℕ) (hδ : Primrec δ) :
    TuringDegrees.Reduces (pathCode δ hδ) (selectedPath δ) haltingDiagonal := by
  classical
  intro n
  rw [path_code_eval]
  congr 1
  unfold selectedPath selectedBit
  by_cases h : leftInput δ (selectedWord δ n) ∈ haltingDiagonal <;> simp [indicator, h]

theorem halting_oracle_path (T : Set ℕ) (hT : IsBinaryTree T)
    (hc : ComputablePred (fun u => u ∈ T)) (hi : ∀ n, HasLevel T n) :
    Path T (selectedPath (deadQuery T hc)) ∧
      TuringDegrees.Reduces
        (pathCode (deadQuery T hc) (dead_query_primitive T hc))
        (selectedPath (deadQuery T hc)) haltingDiagonal := by
  classical
  refine ⟨?_, path_code_reduces _ _⟩
  intro n
  have hs := selected_words_correct T hT hc hi n
  obtain ⟨v, hvT, _, hp⟩ : ∃ v ∈ T,
      wordLength v = wordLength (selectedWord (deadQuery T hc) n) + 0 ∧
        Prefix (selectedWord (deadQuery T hc) n) v := by
    simpa only [empty_extension_spec T hT, not_not] using hs.2.2.1 0
  have hm := hT.2 _ _ hs.1 hvT hp
  have he := realizes_code _ _ hs.1 hs.2.2.2
  rw [hs.2.1] at he
  simpa only [he] using hm

end
end Lemmatheca.ComputabilityTheory.ComputableTreesAndPaths
