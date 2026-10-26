import Lemmatheca.OracleProgramNumberings.Bounded

/-! Finite primitive-recursive schemes with a formal query generator. -/
namespace Lemmatheca.ComputabilityTheory.OracleProgramNumberings

open OracleComputation
open PartialRecursiveFunctions (Args)


inductive UniformPrimitive : {n : ℕ} → ((ℕ → ℕ) → Args n → ℕ) → Prop
  | zero (n : ℕ) : UniformPrimitive (fun (_ : ℕ → ℕ) (_ : Args n) => 0)
  | succ : UniformPrimitive (fun _ (v : Args 1) => v.get 0 + 1)
  | proj {n : ℕ} (i : Fin n) : UniformPrimitive (fun _ (v : Args n) => v.get i)
  | query : UniformPrimitive (fun q (v : Args 1) => q (v.get 0))
  | comp {m n : ℕ} {h : (ℕ → ℕ) → Args m → ℕ}
      {g : Fin m → (ℕ → ℕ) → Args n → ℕ} :
      UniformPrimitive h → (∀ i, UniformPrimitive (g i)) →
      UniformPrimitive (fun q v => h q (List.Vector.ofFn (fun i => g i q v)))
  | prec {n : ℕ} {g : (ℕ → ℕ) → Args n → ℕ}
      {h : (ℕ → ℕ) → Args (n + 2) → ℕ} :
      UniformPrimitive g → UniformPrimitive h →
      UniformPrimitive (fun q => PrimitiveRecursion.lastRec (g q) (h q))

def SearchFree : Code → Prop
  | .zero | .succ | .left | .right | .query => True
  | .pair c d | .comp c d | .prec c d => SearchFree c ∧ SearchFree d
  | .find' _ => False

noncomputable def RelativePrimitive {n : ℕ} (A : Set ℕ) (f : Args n → ℕ) : Prop :=
  ∃ F : (ℕ → ℕ) → Args n → ℕ, UniformPrimitive F ∧
    F (UniversalComputation.indicator (fun x => x ∈ A)) = f

theorem uniform_ordinary_primitive {n : ℕ} (f : Args n → ℕ) (hf : Nat.Primrec' f) :
    UniformPrimitive (fun _ => f) := by
  exact PrimitiveRecursion.generated_by_lastRec
    (fun {m} g => UniformPrimitive (fun _ : ℕ → ℕ => g))
    (UniformPrimitive.zero 0) (by simpa only [List.Vector.get_zero, Nat.succ_eq_add_one] using UniformPrimitive.succ) (fun i => UniformPrimitive.proj i)
    (fun _ _ hh hg => UniformPrimitive.comp hh hg)
    (fun _ _ hg hh => UniformPrimitive.prec hg hh) hf


private theorem primitive_code {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ c : Code, SearchFree c ∧ ∀ (A : Set ℕ) x, eval A c x = Part.some (f x) := by
  induction hf with
  | zero => exact ⟨.zero, trivial, fun _ _ => rfl⟩
  | succ => exact ⟨.succ, trivial, fun _ _ => rfl⟩
  | left => exact ⟨.left, trivial, fun _ _ => rfl⟩
  | right => exact ⟨.right, trivial, fun _ _ => rfl⟩
  | pair hf hg ihf ihg =>
    obtain ⟨c, hcf, hc⟩ := ihf
    obtain ⟨d, hdf, hd⟩ := ihg
    exact ⟨.pair c d, ⟨hcf, hdf⟩, fun A x => by simp [eval, hc, hd]⟩
  | comp hf hg ihf ihg =>
    obtain ⟨c, hcf, hc⟩ := ihf
    obtain ⟨d, hdf, hd⟩ := ihg
    exact ⟨.comp c d, ⟨hcf, hdf⟩, fun A x => by simp [eval, hc, hd]⟩
  | @prec f g hf hg ihf ihg =>
    obtain ⟨c, hcf, hc⟩ := ihf
    obtain ⟨d, hdf, hd⟩ := ihg
    refine ⟨.prec c d, ⟨hcf, hdf⟩, ?_⟩
    intro A x
    obtain ⟨⟨a,n⟩, rfl⟩ := Nat.pairEquiv.surjective x
    simp only [Nat.pairEquiv_apply, Function.uncurry, Nat.unpaired, Nat.unpair_pair]
    change eval A (.prec c d) (Nat.pair a n) = Part.some (n.rec (f a) fun j v => g (Nat.pair a (Nat.pair j v)))
    induction n with
    | zero => rw [eval_prec_zero]; exact hc A a
    | succ n ih => simp only [eval_prec_succ, ih, Part.bind_some, hd]

private theorem primitive_code' {f : ℕ → ℕ} (hf : Primrec f) :
    ∃ c : Code, SearchFree c ∧ ∀ (A : Set ℕ) x, eval A c x = Part.some (f x) :=
  primitive_code (Primrec.nat_iff.mp hf)

private def tupleCode : {m : ℕ} → (Fin m → Code) → Code
  | 0, _ => .zero
  | m + 1, cs => .pair (cs 0) (tupleCode (fun i : Fin m => cs i.succ))

private theorem tupleCode_free {m : ℕ} (cs : Fin m → Code) (h : ∀ i, SearchFree (cs i)) :
    SearchFree (tupleCode cs) := by
  induction m with
  | zero => trivial
  | succ m ih => exact ⟨h 0, ih _ (fun i => h i.succ)⟩

private theorem tupleCode_total (A : Set ℕ) {m : ℕ} (cs : Fin m → Code)
    (values : Fin m → ℕ) (x : ℕ) (h : ∀ i, eval A (cs i) x = Part.some (values i)) :
    eval A (tupleCode cs) x = Part.some
      (MachinesAndComputationHistories.tuplePack (List.Vector.ofFn values)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [tupleCode, eval, h 0, Part.bind_some]
    rw [ih (fun i => cs i.succ) (fun i => values i.succ) (fun i => h i.succ), Part.map_some]
    rfl

private theorem primrec_initial (n : ℕ) : Primrec (@PrimitiveRecursion.initialPart n) :=
  Primrec.vector_ofFn fun i => Primrec.vector_get.comp Primrec.id (Primrec.const i.castSucc)

private theorem primrec_appendTwo (n : ℕ) :
    Primrec (fun p : Args n × ℕ × ℕ => p.1 ++ (List.Vector.cons p.2.1 (List.Vector.cons p.2.2 List.Vector.nil))) := by
  apply Primrec.vector_toList_iff.mp
  simpa only [List.Vector.toList_append, List.Vector.toList_cons, List.Vector.toList_nil] using
    Primrec.list_append.comp (Primrec.vector_toList.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])))

theorem uniform_primitive_program {n : ℕ} {F : (ℕ → ℕ) → Args n → ℕ}
    (hF : UniformPrimitive F) :
    ∃ c : Code, SearchFree c ∧ ∀ (A : Set ℕ) (v : Args n),
      eval A c (MachinesAndComputationHistories.tuplePack v) =
        Part.some (F (UniversalComputation.indicator (fun x => x ∈ A)) v) := by
  classical
  induction hF with
  | zero n => exact ⟨.zero, trivial, fun _ _ => rfl⟩
  | succ =>
    exact ⟨.comp .succ .left, ⟨trivial, trivial⟩,
      fun A v => by simp [eval, MachinesAndComputationHistories.tuplePack]⟩
  | proj i =>
    obtain ⟨c, hcf, hc⟩ := primitive_code' ((Primrec.vector_get.comp
      (MachinesAndComputationHistories.tuple_unpack_primrec _) (Primrec.const i)))
    exact ⟨c, hcf, fun A v => by simpa only [MachinesAndComputationHistories.tuple_unpack_pack] using hc A (MachinesAndComputationHistories.tuplePack v)⟩
  | query =>
    exact ⟨.comp .query .left, ⟨trivial, trivial⟩,
      fun A v => by simp [eval, MachinesAndComputationHistories.tuplePack]⟩
  | @comp m n h g hh hg ihh ihg =>
    obtain ⟨ch, hchf, hch⟩ := ihh
    choose cs hcsf hcs using ihg
    refine ⟨.comp ch (tupleCode cs), ⟨hchf, tupleCode_free cs hcsf⟩, ?_⟩
    intro A v
    change (eval A (tupleCode cs) (MachinesAndComputationHistories.tuplePack v)).bind (eval A ch) = _
    rw [tupleCode_total A cs _ _ (fun i => hcs i A v), Part.bind_some, hch]
  | @prec n g h hg hh ihg ihh =>
    obtain ⟨cg, hcgf, hcg⟩ := ihg
    obtain ⟨ch, hchf, hch⟩ := ihh
    let stepPack : ℕ → ℕ := fun z => MachinesAndComputationHistories.tuplePack
      ((MachinesAndComputationHistories.tupleUnpack n z.unpair.1) ++
        (List.Vector.cons z.unpair.2.unpair.1 (List.Vector.cons z.unpair.2.unpair.2 List.Vector.nil)))
    have hsp : Primrec stepPack :=
      (MachinesAndComputationHistories.tuple_pack_primrec (n + 2)).comp
        ((primrec_appendTwo n).comp
          (((MachinesAndComputationHistories.tuple_unpack_primrec n).comp (Primrec.fst.comp Primrec.unpair)).pair
            (((Primrec.fst.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair)).pair
              ((Primrec.snd.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair)))))
    obtain ⟨cs, hcsf, hcs⟩ := primitive_code' hsp
    let stepCode : Code := .comp ch cs
    have hstep (A : Set ℕ) (x : Args n) (j v : ℕ) : eval A stepCode
        (Nat.pair (MachinesAndComputationHistories.tuplePack x) (Nat.pair j v)) =
        Part.some (h (UniversalComputation.indicator (fun t => t ∈ A))
          (x ++ List.Vector.cons j (List.Vector.cons v List.Vector.nil))) := by
      simp [stepCode, eval, hcs, stepPack, MachinesAndComputationHistories.tuple_unpack_pack, hch]
    have hrec (A : Set ℕ) (x : Args n) (t : ℕ) : eval A (.prec cg stepCode)
        (Nat.pair (MachinesAndComputationHistories.tuplePack x) t) =
        Part.some (PrimitiveRecursion.recValue
          (g (UniversalComputation.indicator (fun r => r ∈ A)))
          (fun x j v => h (UniversalComputation.indicator (fun r => r ∈ A))
            (x ++ List.Vector.cons j (List.Vector.cons v List.Vector.nil))) x t) := by
      induction t with
      | zero =>
        rw [eval_prec_zero]
        exact hcg A x
      | succ t ih => simp only [eval_prec_succ, ih, Part.bind_some, hstep, PrimitiveRecursion.recValue]
    let move : ℕ → ℕ := fun z => Nat.pair
      (MachinesAndComputationHistories.tuplePack (PrimitiveRecursion.initialPart
        (MachinesAndComputationHistories.tupleUnpack (n + 1) z)))
      ((MachinesAndComputationHistories.tupleUnpack (n + 1) z).get (Fin.last n))
    have hm : Primrec move := Primrec₂.natPair.comp
      ((MachinesAndComputationHistories.tuple_pack_primrec n).comp
        ((primrec_initial n).comp (MachinesAndComputationHistories.tuple_unpack_primrec (n + 1))))
      (Primrec.vector_get.comp (MachinesAndComputationHistories.tuple_unpack_primrec (n + 1)) (Primrec.const (Fin.last n)))
    obtain ⟨cm, hcmf, hcm⟩ := primitive_code' hm
    refine ⟨.comp (.prec cg stepCode) cm, ⟨⟨hcgf, hchf, hcsf⟩, hcmf⟩, ?_⟩
    intro A v
    change (eval A cm (MachinesAndComputationHistories.tuplePack v)).bind (eval A (.prec cg stepCode)) = _
    rw [hcm, Part.bind_some]
    simpa only [move, MachinesAndComputationHistories.tuple_unpack_pack, PrimitiveRecursion.lastRec] using
      hrec A (PrimitiveRecursion.initialPart v) (v.get (Fin.last n))


theorem relative_primitive_program {n : ℕ} (A : Set ℕ) (f : Args n → ℕ)
    (hf : RelativePrimitive A f) :
    ∃ c : Code, ∀ v, eval A c (MachinesAndComputationHistories.tuplePack v) =
      Part.some (f v) := by
  obtain ⟨F, hF, he⟩ := hf
  obtain ⟨c, _, hc⟩ := uniform_primitive_program hF
  exact ⟨c, fun v => by simpa only [he] using hc A v⟩


def boundedFamily (q : ℕ → ℕ) (v : Args 3) : ℕ :=
  tableValue q (v.get 0) (v.get 1) (v.get 2)

private theorem UniformPrimitive.of_eq {n : ℕ}
    {F G : (ℕ → ℕ) → Args n → ℕ} (hF : UniformPrimitive F)
    (h : ∀ q v, F q v = G q v) : UniformPrimitive G :=
  (funext (fun q => funext (h q))) ▸ hF

private theorem get_primrec (n : ℕ) (i : Fin n) : Primrec (fun v : Args n => v.get i) :=
  Primrec.vector_get.comp Primrec.id (Primrec.const i)

private theorem uniform_precomp {m n : ℕ} {F : (ℕ → ℕ) → Args m → ℕ}
    (hF : UniformPrimitive F) (g : Fin m → Args n → ℕ) (hg : ∀ i, Primrec (g i)) :
    UniformPrimitive (fun q v => F q (List.Vector.ofFn (fun i => g i v))) :=
  UniformPrimitive.comp hF (fun i => uniform_ordinary_primitive (g i) (Nat.Primrec'.prim_iff.mpr (hg i)))

private theorem uniform_apply {m n : ℕ} (f : Args m → ℕ) (hf : Primrec f)
    (g : Fin m → (ℕ → ℕ) → Args n → ℕ) (hg : ∀ i, UniformPrimitive (g i)) :
    UniformPrimitive (fun q v => f (List.Vector.ofFn (fun i => g i q v))) :=
  UniformPrimitive.comp (uniform_ordinary_primitive f (Nat.Primrec'.prim_iff.mpr hf)) hg

private def tableEntryStep (old current k p x answer : ℕ) : ℕ :=
  if p = 0 then 1
  else if p = 1 then x + 2
  else if p = 2 then x.unpair.1 + 1
  else if p = 3 then x.unpair.2 + 1
  else if p = 4 then answer + 1
  else
    let n := p - 5
    let m := n / 4
    let a := m.unpair.1
    let b := m.unpair.2
    if n % 4 = 0 then
      let u := tableLookup current (k + 1) a x
      let w := tableLookup current (k + 1) b x
      if u = 0 ∨ w = 0 then 0 else Nat.pair (u - 1) (w - 1) + 1
    else if n % 4 = 1 then
      if x.unpair.2 = 0 then tableLookup current (k + 1) a x.unpair.1
      else
        let j := x.unpair.2 - 1
        let w := tableLookup old k p (Nat.pair x.unpair.1 j)
        if w = 0 then 0 else tableLookup current (k + 1) b
          (Nat.pair x.unpair.1 (Nat.pair j (w - 1)))
    else if n % 4 = 2 then
      let w := tableLookup current (k + 1) b x
      if w = 0 then 0 else tableLookup current (k + 1) a (w - 1)
    else
      let w := tableLookup current (k + 1) m x
      if w = 0 then 0 else if w = 1 then x.unpair.2 + 1
      else tableLookup old k p (Nat.pair x.unpair.1 (x.unpair.2 + 1))

private def tableEntrySkeleton (v : Args 6) : ℕ :=
  tableEntryStep (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4) (v.get 5)

private theorem get_primitive {n : ℕ} (i : Fin n) :
    Primrec (fun v : Args n => v.get i) :=
  Primrec.vector_get.comp Primrec.id (Primrec.const i)

private theorem lookup_primitive {α : Type*} [Primcodable α]
    {t k p x : α → ℕ} (ht : Primrec t) (hk : Primrec k) (hp : Primrec p) (hx : Primrec x) :
    Primrec (fun v => tableLookup (t v) (k v) (p v) (x v)) := by
  have h := Primrec.ite (Primrec.nat_lt.comp hx hk)
    (FiniteSequenceCoding.primrec_entry.comp (FiniteSequenceCoding.primrec_entry.comp ht hp) hx)
    (Primrec.const 0)
  exact h.of_eq fun _ => rfl

private theorem tableEntrySkeleton_primitive : Primrec tableEntrySkeleton := by
  have hOld := get_primitive (0 : Fin 6)
  have hCur := get_primitive (1 : Fin 6)
  have hK := get_primitive (2 : Fin 6)
  have hP := get_primitive (3 : Fin 6)
  have hX := get_primitive (4 : Fin 6)
  have hAns := get_primitive (5 : Fin 6)
  have z := Primrec.const (α := Args 6) 0
  have one := Primrec.const (α := Args 6) 1
  have two := Primrec.const (α := Args 6) 2
  have three := Primrec.const (α := Args 6) 3
  have four := Primrec.const (α := Args 6) 4
  have five := Primrec.const (α := Args 6) 5
  have hN := Primrec.nat_sub.comp hP five
  have hM := Primrec.nat_div.comp hN four
  have hA := Primrec.fst.comp (Primrec.unpair.comp hM)
  have hB := Primrec.snd.comp (Primrec.unpair.comp hM)
  have hL := Primrec.fst.comp (Primrec.unpair.comp hX)
  have hR := Primrec.snd.comp (Primrec.unpair.comp hX)
  have hK1 := Primrec.nat_add.comp hK one
  have hAX := lookup_primitive hCur hK1 hA hX
  have hBX := lookup_primitive hCur hK1 hB hX
  have hMX := lookup_primitive hCur hK1 hM hX
  have hPair := Primrec.ite
    (PrimrecPred.or (Primrec.eq.comp hAX z) (Primrec.eq.comp hBX z)) z
    (Primrec.nat_add.comp
      (Primrec₂.natPair.comp (Primrec.nat_sub.comp hAX one) (Primrec.nat_sub.comp hBX one)) one)
  have hPrev := lookup_primitive hOld hK hP
    (Primrec₂.natPair.comp hL (Primrec.nat_sub.comp hR one))
  have hRec := Primrec.ite (Primrec.eq.comp hR z)
    (lookup_primitive hCur hK1 hA hL)
    (Primrec.ite (Primrec.eq.comp hPrev z) z
      (lookup_primitive hCur hK1 hB
        (Primrec₂.natPair.comp hL
          (Primrec₂.natPair.comp (Primrec.nat_sub.comp hR one) (Primrec.nat_sub.comp hPrev one)))))
  have hComp := Primrec.ite (Primrec.eq.comp hBX z) z
    (lookup_primitive hCur hK1 hA (Primrec.nat_sub.comp hBX one))
  have hFind := Primrec.ite (Primrec.eq.comp hMX z) z
    (Primrec.ite (Primrec.eq.comp hMX one) (Primrec.nat_add.comp hR one)
      (lookup_primitive hOld hK hP (Primrec₂.natPair.comp hL (Primrec.nat_add.comp hR one))))
  have hTag := Primrec.nat_mod.comp hN four
  have hTail := Primrec.ite (Primrec.eq.comp hTag z) hPair
    (Primrec.ite (Primrec.eq.comp hTag one) hRec
      (Primrec.ite (Primrec.eq.comp hTag two) hComp hFind))
  have hTotal := Primrec.ite (Primrec.eq.comp hP z) one
    (Primrec.ite (Primrec.eq.comp hP one) (Primrec.nat_add.comp hX two)
      (Primrec.ite (Primrec.eq.comp hP two) (Primrec.nat_add.comp hL one)
        (Primrec.ite (Primrec.eq.comp hP three) (Primrec.nat_add.comp hR one)
          (Primrec.ite (Primrec.eq.comp hP four) (Primrec.nat_add.comp hAns one) hTail))))
  exact hTotal.of_eq fun _ => rfl

private theorem tableEntryStep_eq (q : ℕ → ℕ) (old current k p x : ℕ) :
    tableEntryStep old current k p x (q x) = tableEntry q old current k p x := by
  iterate 5 rcases p with _ | p; · simp [tableEntry, tableEntryStep]
  change tableEntryStep old current k (p + 5) x (q x) = _
  have h0 : p + 5 ≠ 0 := by omega
  have h1 : p + 5 ≠ 1 := by omega
  have h2 : p + 5 ≠ 2 := by omega
  have h3 : p + 5 ≠ 3 := by omega
  have h4 : p + 5 ≠ 4 := by omega
  simp only [tableEntryStep, h0, h1, h2, h3, h4, ↓reduceIte, Nat.add_sub_cancel_right]
  rw [tableEntry]
  have hm := Nat.mod_lt p (by decide : 0 < 4)
  interval_cases h : p % 4
  all_goals simp only [↓reduceIte, Nat.reduceEqDiff]
  cases hx : x.unpair.2 with
  | zero => simp
  | succ j => simp

private theorem tableEntry_uniform : UniformPrimitive (fun q (v : Args 5) =>
    tableEntry q (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4)) := by
  let parts : Fin 6 → (ℕ → ℕ) → Args 5 → ℕ :=
    Fin.cases (fun _ v => v.get 0) (Fin.cases (fun _ v => v.get 1)
      (Fin.cases (fun _ v => v.get 2) (Fin.cases (fun _ v => v.get 3)
        (Fin.cases (fun _ v => v.get 4) (fun _ q v => q (v.get 4))))))
  have hi : ∀ i, UniformPrimitive (parts i) := by
    intro i
    refine Fin.cases (.proj 0) (fun i => Fin.cases (.proj 1) (fun i =>
      Fin.cases (.proj 2) (fun i => Fin.cases (.proj 3) (fun i =>
        Fin.cases (.proj 4) (fun _ => ?_) i) i) i) i) i
    change UniformPrimitive (fun q (v : Args 5) => q (v.get 4))
    simpa only [List.Vector.get_ofFn] using
      (UniformPrimitive.comp UniformPrimitive.query (fun _ : Fin 1 => UniformPrimitive.proj (4 : Fin 5)))
  have h := UniformPrimitive.comp
    (uniform_ordinary_primitive tableEntrySkeleton
      (Nat.Primrec'.prim_iff.mpr tableEntrySkeleton_primitive)) hi
  convert h using 1
  funext q v
  change tableEntry q (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4) =
    tableEntryStep (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4) (q (v.get 4))
  exact (tableEntryStep_eq q _ _ _ _ _).symm

@[simp 1100] private theorem appended_get {n : ℕ} (v : Args n) (a b : ℕ) (i : Fin (n + 2)) :
    (v ++ List.Vector.cons a (List.Vector.cons b List.Vector.nil)).get i =
      if h : i.val < n then v.get ⟨i.val, h⟩ else if i.val = n then a else b := by
  rcases v with ⟨l, rfl⟩
  change (l ++ [a,b])[i.val]'_ = if h : i.val < l.length then l[i.val]'h else if i.val = l.length then a else b
  rw [List.getElem_append]
  by_cases hi : i.val < l.length
  · simp [hi]
  · by_cases he : i.val = l.length
    · simp [he]
    · have he' : i.val - l.length = 1 := by omega
      simp [hi,he,he']

private def rowStep (q : ℕ → ℕ) (v : Args 6) : ℕ :=
  FSC.append (v.get 5) (FSC.cons (tableEntry q (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4)) 0)

private theorem rowStep_uniform : UniformPrimitive rowStep := by
  have he : UniformPrimitive (fun q (v : Args 6) =>
      tableEntry q (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4)) := by
    exact (uniform_precomp tableEntry_uniform (fun i (v : Args 6) => v.get i.castSucc)
      (fun i => get_primrec _ _)).of_eq (fun _ _ => by simp)
  let inn : Fin 2 → (ℕ → ℕ) → Args 6 → ℕ := Fin.cases (fun _ v => v.get 5)
    (fun _ q v => tableEntry q (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4))
  have hp : Primrec (fun v : Args 2 => FSC.append (v.get 0) (FSC.cons (v.get 1) 0)) :=
    FiniteSequenceCoding.primrec_append.comp (get_primrec _ 0)
      (FiniteSequenceCoding.primrec_cons.comp (get_primrec _ 1) (Primrec.const 0))
  exact (uniform_apply _ hp inn (fun i => Fin.cases (UniformPrimitive.proj 5) (fun _ => he) i)).of_eq
    (fun _ _ => rfl)

private theorem row_uniform : UniformPrimitive (fun q (v : Args 5) =>
    buildRow q (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4)) := by
  have hrec (q : ℕ → ℕ) (v : Args 4) (t : ℕ) :
      PrimitiveRecursion.recValue (fun _ : Args 4 => 0)
        (fun v j u => rowStep q (v ++ List.Vector.cons j (List.Vector.cons u List.Vector.nil))) v t =
      buildRow q (v.get 0) (v.get 1) (v.get 2) (v.get 3) t := by
    induction t with
    | zero => rfl
    | succ t ih =>
      simpa [PrimitiveRecursion.recValue, buildRow, rowStep] using
        congrArg (fun u => rowStep q (v ++ List.Vector.cons t (List.Vector.cons u List.Vector.nil))) ih
  apply (UniformPrimitive.prec (UniformPrimitive.zero 4) rowStep_uniform).of_eq
  intro q v
  simpa [PrimitiveRecursion.lastRec, PrimitiveRecursion.initialPart] using hrec q (PrimitiveRecursion.initialPart v) (v.get 4)

private def rowsStep (q : ℕ → ℕ) (v : Args 4) : ℕ :=
  FSC.append (v.get 3) (FSC.cons (buildRow q (v.get 0) (v.get 3) (v.get 1) (v.get 2) (v.get 1 + 1)) 0)

private theorem rowsStep_uniform : UniformPrimitive rowsStep := by
  let coords : Fin 5 → Args 4 → ℕ := fun i v => match i.val with
    | 0 => v.get 0 | 1 => v.get 3 | 2 => v.get 1 | 3 => v.get 2 | _ => v.get 1 + 1
  have hp : ∀ i, Primrec (coords i) := by
    intro i
    fin_cases i
    · exact get_primrec _ 0
    · exact get_primrec _ 3
    · exact get_primrec _ 1
    · exact get_primrec _ 2
    · exact Primrec.succ.comp (get_primrec _ 1)
  have hr : UniformPrimitive (fun q (v : Args 4) =>
      buildRow q (v.get 0) (v.get 3) (v.get 1) (v.get 2) (v.get 1 + 1)) :=
    (uniform_precomp row_uniform coords hp).of_eq (fun _ _ => rfl)
  let inn : Fin 2 → (ℕ → ℕ) → Args 4 → ℕ := Fin.cases (fun _ v => v.get 3)
    (fun _ q v => buildRow q (v.get 0) (v.get 3) (v.get 1) (v.get 2) (v.get 1 + 1))
  have hp' : Primrec (fun v : Args 2 => FSC.append (v.get 0) (FSC.cons (v.get 1) 0)) :=
    FiniteSequenceCoding.primrec_append.comp (get_primrec _ 0)
      (FiniteSequenceCoding.primrec_cons.comp (get_primrec _ 1) (Primrec.const 0))
  exact (uniform_apply _ hp' inn (fun i => Fin.cases (UniformPrimitive.proj 3) (fun _ => hr) i)).of_eq
    (fun _ _ => rfl)

private theorem rows_uniform : UniformPrimitive (fun q (v : Args 3) =>
    buildRows q (v.get 0) (v.get 1) (v.get 2)) := by
  have hrec (q : ℕ → ℕ) (v : Args 2) (t : ℕ) :
      PrimitiveRecursion.recValue (fun _ : Args 2 => 0)
        (fun v j u => rowsStep q (v ++ List.Vector.cons j (List.Vector.cons u List.Vector.nil))) v t =
      buildRows q (v.get 0) (v.get 1) t := by
    induction t with
    | zero => rfl
    | succ t ih =>
      simpa [PrimitiveRecursion.recValue, buildRows, rowsStep] using
        congrArg (fun u => rowsStep q (v ++ List.Vector.cons t (List.Vector.cons u List.Vector.nil))) ih
  apply (UniformPrimitive.prec (UniformPrimitive.zero 2) rowsStep_uniform).of_eq
  intro q v
  simpa [PrimitiveRecursion.lastRec, PrimitiveRecursion.initialPart] using hrec q (PrimitiveRecursion.initialPart v) (v.get 2)

private theorem zeros_primrec : Primrec (fun v : Args 1 => FSC.code (List.replicate (v.get 0 + 1) 0)) := by
  have hp : Primrec (fun v : Args 1 => Nat.rec (motive := fun _ => ℕ) 0 (fun _ z => FSC.cons 0 z) (v.get 0 + 1)) :=
    Primrec.nat_rec' (Primrec.succ.comp (get_primrec _ 0)) (Primrec.const 0)
      (FiniteSequenceCoding.primrec_cons.comp (Primrec.const 0) (Primrec.snd.comp Primrec.snd)).to₂
  apply hp.of_eq
  intro v
  have he : ∀ t, Nat.rec (motive := fun _ => ℕ) 0 (fun _ z => FSC.cons 0 z) t = FSC.code (List.replicate t 0) := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => simpa only [List.replicate_succ, FiniteSequenceCoding.code_cons] using congrArg (FSC.cons 0) ih
  exact he (v.get 0 + 1)

private theorem finiteTable_uniform : UniformPrimitive (fun q (v : Args 2) =>
    finiteTable q (v.get 0) (v.get 1)) := by
  let coords : Fin 3 → Args 3 → ℕ := fun i v => match i.val with
    | 0 => v.get 2 | 1 => v.get 1 | _ => v.get 0 + 1
  have hp : ∀ i, Primrec (coords i) := by
    intro i
    fin_cases i
    · exact get_primrec _ 2
    · exact get_primrec _ 1
    · exact Primrec.succ.comp (get_primrec _ 0)
  have hs : UniformPrimitive (fun q (v : Args 3) => buildRows q (v.get 2) (v.get 1) (v.get 0 + 1)) :=
    (uniform_precomp rows_uniform coords hp).of_eq (fun _ _ => rfl)
  have hz := uniform_ordinary_primitive _ (Nat.Primrec'.prim_iff.mpr zeros_primrec)
  have hrec (q : ℕ → ℕ) (v : Args 1) (t : ℕ) :
      PrimitiveRecursion.recValue (fun v : Args 1 => FSC.code (List.replicate (v.get 0 + 1) 0))
        (fun v j u => buildRows q
          ((v ++ List.Vector.cons j (List.Vector.cons u List.Vector.nil)).get 2)
          ((v ++ List.Vector.cons j (List.Vector.cons u List.Vector.nil)).get 1)
          ((v ++ List.Vector.cons j (List.Vector.cons u List.Vector.nil)).get 0 + 1)) v t =
      finiteTable q (v.get 0) t := by
    induction t with
    | zero => rfl
    | succ t ih =>
      simpa [PrimitiveRecursion.recValue, finiteTable] using
        congrArg (fun u => buildRows q u t (v.get 0 + 1)) ih
  apply (UniformPrimitive.prec hz hs).of_eq
  intro q v
  simpa [PrimitiveRecursion.lastRec, PrimitiveRecursion.initialPart] using hrec q (PrimitiveRecursion.initialPart v) (v.get 1)

theorem boundedFamily_primitive : UniformPrimitive boundedFamily := by
  have htab : UniformPrimitive (fun q (v : Args 3) => finiteTable q (v.get 1) (v.get 0)) := by
    let coords : Fin 2 → Args 3 → ℕ := Fin.cases (fun v => v.get 1) (fun _ v => v.get 0)
    exact (uniform_precomp finiteTable_uniform coords (fun i =>
      Fin.cases (get_primrec _ 1) (fun _ => get_primrec _ 0) i)).of_eq (fun _ _ => rfl)
  have hlookup : Primrec (fun v : Args 4 => tableLookup (v.get 0) (v.get 1) (v.get 2) (v.get 3)) :=
    Primrec.ite (Primrec.nat_lt.comp (get_primrec _ 3) (get_primrec _ 1))
      (FiniteSequenceCoding.primrec_entry.comp
        (FiniteSequenceCoding.primrec_entry.comp (get_primrec _ 0) (get_primrec _ 2)) (get_primrec _ 3))
      (Primrec.const 0)
  let inn : Fin 4 → (ℕ → ℕ) → Args 3 → ℕ := Fin.cases
    (fun q v => finiteTable q (v.get 1) (v.get 0))
    (fun i _ v => v.get i)
  have hi : ∀ i, UniformPrimitive (inn i) := by
    intro i
    exact Fin.cases htab (fun i => UniformPrimitive.proj i) i
  exact (uniform_apply _ hlookup inn hi).of_eq (fun _ _ => rfl)


noncomputable def boundedScheme : Code :=
  Classical.choose (uniform_primitive_program boundedFamily_primitive)

def triplePacking : Code :=
  .pair .left (.pair (.comp .left .right) (.pair (.comp .right .right) .zero))

noncomputable def boundedCode : Code := .comp boundedScheme triplePacking

theorem boundedScheme_spec : SearchFree boundedScheme ∧
    ∀ (A : Set ℕ) (v : Args 3),
      eval A boundedScheme (MachinesAndComputationHistories.tuplePack v) =
        Part.some (boundedFamily (UniversalComputation.indicator (fun x => x ∈ A)) v) := by
  exact Classical.choose_spec (uniform_primitive_program boundedFamily_primitive)


theorem bounded_code_eval (A : Set ℕ) (k e x : ℕ) :
    eval A boundedCode (Nat.pair k (Nat.pair e x)) = Part.some (boundedValue A k e x) := by
  have hs := boundedScheme_spec.2 A
    (List.Vector.cons k (List.Vector.cons e (List.Vector.cons x List.Vector.nil)))
  change eval A boundedScheme (Nat.pair k (Nat.pair e (Nat.pair x 0))) =
    Part.some (tableValue (UniversalComputation.indicator (fun t => t ∈ A)) k e x) at hs
  rw [tableValue_correct] at hs
  simpa only [boundedCode, triplePacking, eval, Nat.unpair_pair, Part.bind_some, Part.map_some] using hs


theorem bounded_value_relative_primitive (A : Set ℕ) :
    RelativePrimitive A (fun v : Args 3 => boundedValue A (v.get 0) (v.get 1) (v.get 2)) := by
  refine ⟨boundedFamily, boundedFamily_primitive, ?_⟩
  funext v
  exact tableValue_correct A _ _ _


end Lemmatheca.ComputabilityTheory.OracleProgramNumberings
