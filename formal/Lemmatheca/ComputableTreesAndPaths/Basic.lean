import Lemmatheca.IncomparableTuringDegrees.Prefixes
import Mathlib.Order.KonigLemma

/-! Binary trees on the existing numerical list codes and paths as ones sets. -/
namespace Lemmatheca.ComputabilityTheory.ComputableTreesAndPaths

open IncomparableTuringDegrees PostsTheorem UniversalComputation

noncomputable section

def IsBinaryTree (T : Set ℕ) : Prop :=
  (∀ u ∈ T, ValidCode u) ∧
    ∀ u v, ValidCode u → v ∈ T → Prefix u v → u ∈ T

def HasLevel (T : Set ℕ) (n : ℕ) : Prop :=
  ∃ u ∈ T, wordLength u = n

def Path (T : Set ℕ) (X : Set ℕ) : Prop :=
  ∀ n, prefixCode X n ∈ T

def binaryLevel : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => (binaryLevel n).flatMap (fun u => [appendBit u 0, appendBit u 1])

def takeCode (n u : ℕ) : ℕ :=
  FiniteSequenceCoding.code ((FiniteSequenceCoding.decode u).take n)

theorem take_valid (n u : ℕ) (hu : ValidCode u) : ValidCode (takeCode n u) := by
  intro b hb
  simp only [takeCode, FiniteSequenceCoding.decode_code] at hb
  exact hu b (List.mem_of_mem_take hb)

theorem take_spec (n u : ℕ) (hu : ValidCode u) :
    wordLength (takeCode n u) = min n (wordLength u) ∧ Prefix (takeCode n u) u := by
  constructor
  · simp [takeCode, wordLength, FiniteSequenceCoding.length]
  · apply (prefix_native _ _).mpr
    rw [valid_code_interpretation _ (take_valid n u hu), valid_code_interpretation _ hu]
    simp only [takeCode, FiniteSequenceCoding.decode_code]
    exact List.take_prefix n _

theorem prefix_take (u v n : ℕ) (hv : ValidCode v) (hp : Prefix u v)
    (hn : wordLength u ≤ n) : Prefix u (takeCode n v) := by
  have hl : wordLength u ≤ wordLength (takeCode n v) := by
    rw [(take_spec n v hv).1]
    exact le_min hn hp.1
  refine ⟨hl, fun q hq => ?_⟩
  exact (hp.2 q hq).trans ((take_spec n v hv).2.2 q (lt_of_lt_of_le hq hl)).symm

theorem append_prefix (u v b : ℕ) (hp : Prefix u v) (hl : wordLength u < wordLength v)
    (hb : wordBit v (wordLength u) = b) (hbb : b = 0 ∨ b = 1) :
    Prefix (appendBit u b) v := by
  refine ⟨by rw [(appendBit_spec _ _).1]; omega, fun q hq => ?_⟩
  rw [(appendBit_spec _ _).1] at hq
  by_cases he : q = wordLength u
  · subst q
    rw [(appendBit_spec _ _).2.2, hb]
    rcases hbb with rfl | rfl <;> rfl
  · have hqu : q < wordLength u := by omega
    exact ((appendBit_spec _ _).2.1.2 q hqu).symm.trans (hp.2 q hqu)

theorem code_ext (u v : ℕ) (hu : ValidCode u) (hv : ValidCode v)
    (hlen : wordLength u = wordLength v)
    (hbits : ∀ q < wordLength u, wordBit u q = wordBit v q) : u = v := by
  have hp : Prefix u v := ⟨hlen.le, hbits⟩
  have he := List.IsPrefix.eq_of_length ((prefix_native _ _).mp hp)
    (by simpa only [(word_interpretation u 0).2.1, (word_interpretation v 0).2.1] using hlen)
  rw [valid_code_interpretation _ hu, valid_code_interpretation _ hv] at he
  simpa only [FiniteSequenceCoding.code_decode] using congrArg FiniteSequenceCoding.code he

theorem realizes_code (u : ℕ) (X : Set ℕ) (hu : ValidCode u)
    (hr : Realizes u X) : u = prefixCode X (wordLength u) := by
  have hs := prefixCode_spec X (wordLength u)
  apply code_ext u _ hu (prefix_code_valid _ _) hs.1.symm
  intro q hq
  exact (hr q hq).trans (hs.2 q hq).symm

theorem binary_level_spec (n u : ℕ) :
    u ∈ binaryLevel n ↔ ValidCode u ∧ wordLength u = n := by
  induction n generalizing u with
  | zero =>
    constructor
    · intro h
      have he : u = 0 := by simpa [binaryLevel] using h
      subst u
      simp [ValidCode, BinaryWord,
        wordLength, FiniteSequenceCoding.length]
    · rintro ⟨_, hl⟩
      have he : FiniteSequenceCoding.decode u = [] :=
        List.eq_nil_of_length_eq_zero hl
      have hz : u = 0 := by simpa [he] using (FiniteSequenceCoding.code_decode u).symm
      simp [binaryLevel, hz]
  | succ n ih =>
    constructor
    · intro h
      obtain ⟨v, hv, hu⟩ := List.mem_flatMap.mp h
      have hv' := ih v |>.mp hv
      have hc : u = appendBit v 0 ∨ u = appendBit v 1 := by simpa using hu
      rcases hc with rfl | rfl
      · exact ⟨append_valid _ _ hv'.1, by rw [(appendBit_spec _ _).1, hv'.2]⟩
      · exact ⟨append_valid _ _ hv'.1, by rw [(appendBit_spec _ _).1, hv'.2]⟩
    · rintro ⟨hu, hl⟩
      have hd : (FiniteSequenceCoding.decode u).length = n + 1 := hl
      have hdrop : ((FiniteSequenceCoding.decode u).drop n).length = 1 := by
        simp only [List.length_drop, hd]; omega
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hdrop
      let v := takeCode n u
      have hv : ValidCode v := take_valid _ _ hu
      have hvl : wordLength v = n := by
        rw [(take_spec _ _ hu).1, hl, min_eq_left (by omega)]
      have hbb : b = 0 ∨ b = 1 := hu b (by
        apply List.mem_of_mem_drop
        rw [hb]
        simp)
      have he : u = appendBit v b := by
        simp only [appendBit, FiniteSequenceCoding.append, FiniteSequenceCoding.decode_code]
        dsimp [v, takeCode]
        rw [FiniteSequenceCoding.decode_code]
        rcases hbb with rfl | rfl <;>
          simp only [Nat.zero_mod, show 1 % 2 = 1 by decide,
            ← hb, List.take_append_drop, FiniteSequenceCoding.code_decode]
      apply List.mem_flatMap.mpr
      refine ⟨v, (ih v).mpr ⟨hv, hvl⟩, ?_⟩
      rcases hbb with rfl | rfl <;> simp [he]

theorem binary_level_primitive : Primrec binaryLevel := by
  have h : Primrec (fun l : List ℕ =>
      l.flatMap (fun u => [appendBit u 0, appendBit u 1])) :=
    Primrec.list_flatMap Primrec.id
      ((Primrec.list_cons.comp (appendBit_primitive.comp Primrec.snd (Primrec.const 0))
        (Primrec.list_cons.comp (appendBit_primitive.comp Primrec.snd (Primrec.const 1))
          (Primrec.const []))).to₂)
  exact (Primrec.nat_rec₁ [0] (h.comp Primrec.snd).to₂).of_eq (fun n => by
    induction n <;> simp [binaryLevel, *])

theorem take_code_primitive : Primrec₂ takeCode := by
  exact (Primrec.encode.comp (Primrec.list_take.comp Primrec.fst
    ((Primrec.ofNat (List ℕ)).comp Primrec.snd))).to₂

theorem computable_list_map {α β : Type} [Primcodable α] [Primcodable β]
    (f : α → ℕ → β) (hf : Computable₂ f) :
    Computable₂ (fun a (l : List ℕ) => l.map (f a)) := by
  let build (z : α × List ℕ) : ℕ → List β :=
    Nat.rec [] (fun k old => old ++ [f z.1 (z.2[k]?.getD 0)])
  have hstep : Computable₂ (fun z : α × List ℕ => fun p : ℕ × List β =>
      p.2 ++ [f z.1 (z.2[p.1]?.getD 0)]) := by
    exact (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.fst)
        (Primrec.option_getD.to_comp.comp
          (Computable.list_getElem?.comp (Computable.snd.comp Computable.fst)
            (Computable.fst.comp Computable.snd)) (Computable.const 0)))).to₂
  have hc : Computable (fun z : α × List ℕ => build z z.2.length) :=
    Computable.nat_rec (Computable.list_length.comp Computable.snd)
      (Computable.const []) hstep
  apply hc.to₂.of_eq
  intro z
  change build z z.2.length = z.2.map (f z.1)
  have he (k : ℕ) : build z k =
      (List.range k).map (fun i => f z.1 (z.2[i]?.getD 0)) := by
    induction k with
    | zero => rfl
    | succ k ih => simp [build, List.range_succ, ih]
  rw [he]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.length_map, List.length_range] at hi
    simp [List.getElem?_eq_getElem hi]

theorem erase_dups_primitive : Primrec (List.eraseDups : List ℕ → List ℕ) := by
  have hm : PrimrecPred (fun p : List ℕ × ℕ => p.2 ∈ p.1) :=
    (Primrec.eq.exists_mem_list).of_eq (fun _ => by simp)
  have hs : Primrec (fun p : List ℕ × ℕ =>
      if p.2 ∈ p.1 then p.1 else p.2 :: p.1) :=
    Primrec.ite hm Primrec.fst (Primrec.list_cons.comp Primrec.snd Primrec.fst)
  have hf : Primrec (fun l : List ℕ =>
      (l.foldl (fun acc a => if a ∈ acc then acc else a :: acc) []).reverse) :=
    Primrec.list_reverse.comp
      (Primrec.list_foldl Primrec.id (Primrec.const []) (hs.comp Primrec.snd).to₂)
  have loop (l acc : List ℕ) : List.eraseDupsBy.loop (· == ·) l acc =
      (l.foldl (fun old a => if a ∈ old then old else a :: old) acc).reverse := by
    induction l generalizing acc with
    | nil => rfl
    | cons a l ih =>
      have hb : acc.any (fun b => a == b) = decide (a ∈ acc) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, beq_iff_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨b, hb, he⟩
          exact he.symm ▸ hb
        · intro ha
          exact ⟨a, ha, rfl⟩
      simp only [List.eraseDupsBy.loop, hb, List.foldl_cons]
      by_cases ha : a ∈ acc <;> simp [ha, ih]
  exact hf.of_eq (fun l => (loop l []).symm)

theorem erase_dups_nodup (l : List ℕ) : l.eraseDups.Nodup := by
  have loop (l acc : List ℕ) (hn : acc.Nodup) :
      (List.eraseDupsBy.loop (· == ·) l acc).Nodup := by
    induction l generalizing acc with
    | nil => simpa only [List.eraseDupsBy.loop, List.nodup_reverse] using hn
    | cons a l ih =>
      have hb : acc.any (fun b => a == b) = decide (a ∈ acc) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, beq_iff_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨b, hb, he⟩
          exact he.symm ▸ hb
        · intro ha
          exact ⟨a, ha, rfl⟩
      simp only [List.eraseDupsBy.loop, hb]
      by_cases ha : a ∈ acc
      · simpa only [ha, decide_true] using ih acc hn
      · simpa only [ha, decide_false] using
          ih (a :: acc) (List.nodup_cons.mpr ⟨ha, hn⟩)
  exact loop l [] (by simp)

theorem native_tree_correspondence (T : Set ℕ) :
    IsBinaryTree T ↔
      (∀ l : List ℕ, FiniteSequenceCoding.code l ∈ T → BinaryWord l) ∧
      (∀ l r : List ℕ, FiniteSequenceCoding.code r ∈ T →
        List.IsPrefix l r → FiniteSequenceCoding.code l ∈ T) := by
  constructor
  · rintro ⟨hv, hp⟩
    refine ⟨fun l hl => by simpa [ValidCode] using hv _ hl, ?_⟩
    intro l r hr hlr
    have hbr : BinaryWord r := by simpa [ValidCode] using hv _ hr
    have hbl : BinaryWord l := fun b hb => hbr b (hlr.subset hb)
    apply hp _ _ (by simpa [ValidCode] using hbl) hr
    apply (prefix_native _ _).mpr
    simpa only [binary_word_recovery l hbl, binary_word_recovery r hbr] using hlr
  · rintro ⟨hv, hp⟩
    refine ⟨fun u hu => by simpa [ValidCode] using hv _ (by simpa using hu), ?_⟩
    intro u v hu hvT huv
    have hv' : ValidCode v := by simpa [ValidCode] using hv _ (by simpa using hvT)
    have hn := (prefix_native _ _).mp huv
    rw [valid_code_interpretation _ hu, valid_code_interpretation _ hv'] at hn
    simpa only [FiniteSequenceCoding.code_decode] using hp _ _ (by simpa using hvT) hn

theorem all_levels_path (T : Set ℕ) (hT : IsBinaryTree T) :
    (∀ n, HasLevel T n) ↔ ∃ X, Path T X := by
  classical
  constructor
  · intro hi
    let A (n : ℕ) := {u : ℕ // u ∈ T ∧ wordLength u = n}
    have hfinite (n : ℕ) : {u : ℕ | u ∈ T ∧ wordLength u = n}.Finite := by
      apply (binaryLevel n).finite_toSet.subset
      intro u hu
      exact (binary_level_spec n u).mpr ⟨hT.1 u hu.1, hu.2⟩
    let : ∀ n, Fintype (A n) := fun n => (hfinite n).fintype
    let : ∀ n, Nonempty (A n) := fun n => by
      obtain ⟨u, hu, hl⟩ := hi n
      exact ⟨⟨u, hu, hl⟩⟩
    let π : {i j : ℕ} → i ≤ j → A j → A i := fun {i j} hij v =>
      ⟨takeCode i v.val,
        hT.2 _ _ (take_valid _ _ (hT.1 _ v.property.1)) v.property.1
          (take_spec _ _ (hT.1 _ v.property.1)).2,
        by rw [(take_spec _ _ (hT.1 _ v.property.1)).1,
          v.property.2, min_eq_left hij]⟩
    have hrefl : ∀ i (a : A i), π le_rfl a = a := by
      intro i a
      apply Subtype.ext
      change takeCode i a.val = a.val
      have ht : (FiniteSequenceCoding.decode a.val).take i =
          FiniteSequenceCoding.decode a.val :=
        List.take_of_length_le (show (FiniteSequenceCoding.decode a.val).length ≤ i
          from a.property.2.le)
      simp only [takeCode, ht, FiniteSequenceCoding.code_decode]
    have htrans : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
        π hij (π hjk a) = π (hij.trans hjk) a := by
      intro i j k hij hjk a
      apply Subtype.ext
      change takeCode i (takeCode j a.val) = takeCode i a.val
      simp [takeCode, List.take_take, min_eq_left hij]
    obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite π
      (fun {i} a => hrefl i a) (fun {i j k} hij hjk a => htrans i j k hij hjk a)
      (fun _ _ => Set.toFinite _)
    let u : ℕ → ℕ := fun n => (f n).val
    have hp (n : ℕ) : Prefix (u n) (u (n + 1)) := by
      have he : takeCode n (u (n + 1)) = u n :=
        congrArg Subtype.val (hf (Nat.le_succ n))
      rw [← he]
      exact (take_spec n _ (hT.1 _ (f (n + 1)).property.1)).2
    have hg (n : ℕ) : n ≤ wordLength (u n) := (f n).property.2.ge
    let X := unionSet u
    have hr := (coherent_union u hp hg).1
    refine ⟨X, fun n => ?_⟩
    have he := realizes_code (u n) X (hT.1 _ (f n).property.1) (hr n)
    rw [(f n).property.2] at he
    rw [← he]
    exact (f n).property.1
  · rintro ⟨X, hX⟩ n
    exact ⟨prefixCode X n, hX n, (prefixCode_spec X n).1⟩

end
end Lemmatheca.ComputabilityTheory.ComputableTreesAndPaths
