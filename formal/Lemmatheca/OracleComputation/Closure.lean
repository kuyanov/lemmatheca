import Lemmatheca.OracleComputation.Traces
import Lemmatheca.MachinesAndComputationHistories.MachinesAndComputationHistories
import Mathlib.Computability.RecursiveIn

/-! Bridges to the library's relative unary class and the shared finite-arity calculus. -/
namespace Lemmatheca.ComputabilityTheory.OracleComputation

open PartialRecursiveFunctions UniversalComputation

set_option backward.isDefEq.respectTransparency false

def oracleFunctions (A : Set ℕ) : Set (ℕ → Part ℕ) :=
  {fun q => Part.some (indicator (fun n => n ∈ A) q)}

inductive RelativeRecursive (A : Set ℕ) : {n : ℕ} → PFunction n → Prop
  | zero (n : ℕ) : RelativeRecursive A (fun _ : Args n => Part.some 0)
  | succ : RelativeRecursive A (fun x : Args 1 => Part.some (x.get 0 + 1))
  | proj {n : ℕ} (i : Fin n) :
      RelativeRecursive A (fun x : Args n => Part.some (x.get i))
  | query : RelativeRecursive A
      (fun x : Args 1 => Part.some (indicator (fun n => n ∈ A) (x.get 0)))
  | comp {m n : ℕ} {h : PFunction m} {g : Fin m → PFunction n} :
      RelativeRecursive A h → (∀ i, RelativeRecursive A (g i)) →
      RelativeRecursive A (strictComp h g)
  | prec {k : ℕ} {g : PFunction k} {h : PFunction (k + 2)} :
      RelativeRecursive A g → RelativeRecursive A h → RelativeRecursive A (partialRec g h)
  | search {k : ℕ} {f : PFunction (k + 1)} :
      RelativeRecursive A f → RelativeRecursive A (minimize f)

private theorem ordinary_relative {n : ℕ} (A : Set ℕ) {f : PFunction n}
    (hf : PartialRecursiveFunctions.Recursive f) : RelativeRecursive A f := by
  induction hf with
  | zero n => exact .zero n
  | succ => exact .succ
  | proj i => exact .proj i
  | comp _ _ ihh ihg => exact .comp ihh ihg
  | prec _ _ ihg ihh => exact .prec ihg ihh
  | search _ ih => exact .search ih

private theorem computable_comp {A : Set ℕ} {f g : ℕ → Part ℕ}
    (hf : PartialComputable A f) (hg : PartialComputable A g) :
    PartialComputable A (fun x => (g x).bind f) := by
  obtain ⟨c, rfl⟩ := hf
  obtain ⟨d, rfl⟩ := hg
  exact ⟨.comp c d, rfl⟩

private theorem computable_pair {A : Set ℕ} {f g : ℕ → Part ℕ}
    (hf : PartialComputable A f) (hg : PartialComputable A g) :
    PartialComputable A (fun x => Nat.pair <$> f x <*> g x) := by
  obtain ⟨c, rfl⟩ := hf
  obtain ⟨d, rfl⟩ := hg
  exact ⟨.pair c d, by funext x; simp [eval, Seq.seq]⟩

private theorem computable_prec {A : Set ℕ} {f g : ℕ → Part ℕ}
    (hf : PartialComputable A f) (hg : PartialComputable A g) :
    PartialComputable A (fun p => p.unpair.2.rec (f p.unpair.1)
      fun j previous => previous.bind fun value => g (Nat.pair p.unpair.1 (Nat.pair j value))) := by
  obtain ⟨c, rfl⟩ := hf
  obtain ⟨d, rfl⟩ := hg
  exact ⟨.prec c d, rfl⟩

private theorem computable_find {A : Set ℕ} {f : ℕ → Part ℕ}
    (hf : PartialComputable A f) : PartialComputable A
      (fun a => Nat.rfind fun j => (f (Nat.pair a j)).map (fun value => decide (value = 0))) := by
  obtain ⟨c, rfl⟩ := hf
  obtain ⟨d, hd⟩ := ordinary_inclusion A Nat.Partrec.some
  refine ⟨.comp (.find' c) (.pair d .zero), ?_⟩
  funext x
  simp [eval, hd, Part.map_id']

private theorem library_to_code {A : Set ℕ} {f : ℕ → Part ℕ}
    (hf : Nat.RecursiveIn (oracleFunctions A) f) : PartialComputable A f := by
  induction hf with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | oracle g hg =>
    have he : g = fun q => Part.some (indicator (fun n => n ∈ A) q) := hg
    subst g
    exact ⟨.query, rfl⟩
  | pair _ _ ihf ihg => exact computable_pair ihf ihg
  | comp _ _ ihf ihg => exact computable_comp ihf ihg
  | prec _ _ ihf ihg => exact computable_prec ihf ihg
  | rfind _ ih => exact computable_find ih

private theorem code_to_library (A : Set ℕ) (c : Code) :
    Nat.RecursiveIn (oracleFunctions A) (eval A c) := by
  induction c with
  | zero => exact .zero
  | succ => exact .succ
  | left => exact .left
  | right => exact .right
  | query => exact .oracle _ (Set.mem_singleton _)
  | pair c d ihc ihd => simpa [eval, Seq.seq] using Nat.RecursiveIn.pair ihc ihd
  | comp c d ihc ihd => exact .comp ihc ihd
  | prec c d ihc ihd => exact .prec ihc ihd
  | find' c ih =>
    let shift : ℕ → ℕ := fun z => Nat.pair z.unpair.1.unpair.1 (z.unpair.2 + z.unpair.1.unpair.2)
    have hshift : Primrec shift :=
      Primrec₂.natPair.comp ((Primrec.fst.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair))
        (Primrec.nat_add.comp (Primrec.snd.comp Primrec.unpair)
          ((Primrec.snd.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair)))
    have htest := Nat.RecursiveIn.comp ih (Partrec.nat_iff.mp hshift.to_comp.partrec).recursiveIn
    have hs := Nat.RecursiveIn.rfind htest
    have hpair := Nat.RecursiveIn.pair Nat.Partrec.some.recursiveIn hs
    let addOffset : ℕ → ℕ := fun z => z.unpair.2 + z.unpair.1.unpair.2
    have hadd : Primrec addOffset := Primrec.nat_add.comp (Primrec.snd.comp Primrec.unpair)
      ((Primrec.snd.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair))
    apply (Nat.RecursiveIn.comp (Partrec.nat_iff.mp hadd.to_comp.partrec).recursiveIn hpair).of_eq
    intro x
    simp [eval, shift, addOffset, Seq.seq, Part.bind_eq_bind, Part.bind_map, Part.bind_some_eq_map]

theorem relative_library_iff (A : Set ℕ) (f : ℕ → Part ℕ) :
    PartialComputable A f ↔ Nat.RecursiveIn (oracleFunctions A) f := by
  constructor
  · rintro ⟨c, rfl⟩; exact code_to_library A c
  · exact library_to_code

private theorem primitive_code (A : Set ℕ) {f : ℕ → ℕ} (hf : Primrec f) :
    ∃ c : Code, ∀ x, eval A c x = Part.some (f x) := by
  obtain ⟨c, hc⟩ := ordinary_inclusion A (Partrec.nat_iff.mp hf.to_comp.partrec)
  exact ⟨c, fun x => congrFun hc x⟩

private def tupleCode : {m : ℕ} → (Fin m → Code) → Code
  | 0, _ => .zero
  | m + 1, cs => .pair (cs 0) (tupleCode (fun i : Fin m => cs i.succ))

private theorem tupleCode_spec (A : Set ℕ) {m : ℕ} (cs : Fin m → Code) (x y : ℕ) :
    y ∈ eval A (tupleCode cs) x ↔
      ∃ v : Args m, (∀ i, v.get i ∈ eval A (cs i) x) ∧ y = MachinesAndComputationHistories.tuplePack v := by
  induction m generalizing y with
  | zero => simp [tupleCode, eval, MachinesAndComputationHistories.tuplePack]
  | succ m ih =>
    rw [tupleCode, eval_pair]
    constructor
    · rintro ⟨u, w, hu, hw, rfl⟩
      obtain ⟨v, hv, rfl⟩ := (ih _ _).mp hw
      refine ⟨List.Vector.cons u v, ?_, rfl⟩
      intro i
      exact Fin.cases (by simpa using hu) (fun j => by simpa using hv j) i
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.head, MachinesAndComputationHistories.tuplePack v.tail,
        by simpa using hv 0, (ih _ _).mpr ⟨v.tail, ?_, rfl⟩, rfl⟩
      intro i
      simpa using hv i.succ

private theorem primrec_snoc (n : ℕ) : Primrec₂ (@snoc n) := by
  apply Primrec.vector_ofFn
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [snoc, List.Vector.get_ofFn, Fin.snoc_last] using (@Primrec.snd (Args n) ℕ _ _)
  · simpa only [snoc, List.Vector.get_ofFn, Fin.snoc_castSucc] using
      (Primrec.vector_get.comp Primrec.fst (Primrec.const j))

private theorem primrec_init (n : ℕ) : Primrec (@init n) :=
  Primrec.vector_ofFn fun i => Primrec.vector_get.comp Primrec.id (Primrec.const i.castSucc)

private theorem primrec_last (n : ℕ) : Primrec (@last n) :=
  Primrec.vector_get.comp Primrec.id (Primrec.const (Fin.last n))

private theorem relative_to_code {n : ℕ} {A : Set ℕ} {f : PFunction n}
    (hf : RelativeRecursive A f) :
    ∃ c : Code, ∀ v, eval A c (MachinesAndComputationHistories.tuplePack v) = f v := by
  classical
  induction hf with
  | zero n => exact ⟨.zero, fun _ => rfl⟩
  | succ =>
    obtain ⟨c, hc⟩ := MachinesAndComputationHistories.finite_arity_program_iff.mp
      PartialRecursiveFunctions.Recursive.succ
    exact ⟨embed c, fun v => (eval_embed A c _).trans (hc v)⟩
  | proj i =>
    obtain ⟨c, hc⟩ := MachinesAndComputationHistories.finite_arity_program_iff.mp
      (PartialRecursiveFunctions.Recursive.proj i)
    exact ⟨embed c, fun v => (eval_embed A c _).trans (hc v)⟩
  | query =>
    exact ⟨.comp .query .left, fun v => by simp [eval, MachinesAndComputationHistories.tuplePack]⟩
  | @comp m n h g hh hg ihh ihg =>
    obtain ⟨ch, hch⟩ := ihh
    choose cs hcs using ihg
    refine ⟨.comp ch (tupleCode cs), ?_⟩
    intro v
    apply Part.ext
    intro y
    rw [eval_comp, strictComp_spec]
    constructor
    · rintro ⟨z, hz, hy⟩
      obtain ⟨w, hw, rfl⟩ := (tupleCode_spec A cs _ z).mp hz
      rw [hch w] at hy
      exact ⟨w, fun i => by simpa only [hcs i v] using hw i, hy⟩
    · rintro ⟨w, hw, hy⟩
      refine ⟨MachinesAndComputationHistories.tuplePack w,
        (tupleCode_spec A cs _ _).mpr ⟨w, fun i => ?_, rfl⟩, ?_⟩
      · simpa only [hcs i v] using hw i
      · simpa only [hch w] using hy
  | @prec k g h hg hh ihg ihh =>
    obtain ⟨cg, hcg⟩ := ihg
    obtain ⟨ch, hch⟩ := ihh
    let stepPack : ℕ → ℕ := fun z => MachinesAndComputationHistories.tuplePack
      (snoc (snoc (MachinesAndComputationHistories.tupleUnpack k z.unpair.1)
        z.unpair.2.unpair.1) z.unpair.2.unpair.2)
    have hsp : Primrec stepPack :=
      (MachinesAndComputationHistories.tuple_pack_primrec (k + 2)).comp
        ((primrec_snoc (k + 1)).comp
          ((primrec_snoc k).comp
            ((MachinesAndComputationHistories.tuple_unpack_primrec k).comp (Primrec.fst.comp Primrec.unpair))
            ((Primrec.fst.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair)))
          ((Primrec.snd.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair)))
    obtain ⟨cs, hcs⟩ := primitive_code A hsp
    let stepCode : Code := .comp ch cs
    have hstep (x : Args k) (j v : ℕ) : eval A stepCode
        (Nat.pair (MachinesAndComputationHistories.tuplePack x) (Nat.pair j v)) =
        h (snoc (snoc x j) v) := by
      simp [stepCode, eval, hcs, stepPack, MachinesAndComputationHistories.tuple_unpack_pack, hch]
    have hrec (x : Args k) (t : ℕ) : eval A (.prec cg stepCode)
        (Nat.pair (MachinesAndComputationHistories.tuplePack x) t) = recValue g h x t := by
      induction t with
      | zero => simpa only [eval_prec_zero, recValue] using hcg x
      | succ t ih => simp only [eval_prec_succ, ih, recValue, hstep]
    let move : ℕ → ℕ := fun z => Nat.pair
      (MachinesAndComputationHistories.tuplePack (init (MachinesAndComputationHistories.tupleUnpack (k + 1) z)))
      (last (MachinesAndComputationHistories.tupleUnpack (k + 1) z))
    have hm : Primrec move := Primrec₂.natPair.comp
      ((MachinesAndComputationHistories.tuple_pack_primrec k).comp
        ((primrec_init k).comp (MachinesAndComputationHistories.tuple_unpack_primrec (k + 1))))
      ((primrec_last k).comp (MachinesAndComputationHistories.tuple_unpack_primrec (k + 1)))
    obtain ⟨cm, hcm⟩ := primitive_code A hm
    refine ⟨.comp (.prec cg stepCode) cm, ?_⟩
    intro v
    change (eval A cm (MachinesAndComputationHistories.tuplePack v)).bind
      (eval A (.prec cg stepCode)) = partialRec g h v
    rw [hcm, Part.bind_some]
    simpa only [move, MachinesAndComputationHistories.tuple_unpack_pack, partialRec] using
      hrec (init v) (last v)
  | @search k f hf ih =>
    obtain ⟨c, hc⟩ := ih
    let pack : ℕ → ℕ := fun z => MachinesAndComputationHistories.tuplePack
      (snoc (MachinesAndComputationHistories.tupleUnpack k z.unpair.1) z.unpair.2)
    have hp : Primrec pack := (MachinesAndComputationHistories.tuple_pack_primrec (k + 1)).comp
      ((primrec_snoc k).comp
        ((MachinesAndComputationHistories.tuple_unpack_primrec k).comp (Primrec.fst.comp Primrec.unpair))
        (Primrec.snd.comp Primrec.unpair))
    obtain ⟨cp, hcp⟩ := primitive_code A hp
    obtain ⟨d, hd⟩ := computable_find (A := A) (f := eval A (.comp c cp)) ⟨.comp c cp, rfl⟩
    refine ⟨d, fun v => ?_⟩
    simp only [hd]
    simp [eval, hcp, pack, MachinesAndComputationHistories.tuple_unpack_pack, hc, minimize]

variable {A : Set ℕ}
private theorem RelativeRecursive.of_eq {n : ℕ} {f g : PFunction n}
    (hf : RelativeRecursive A f) (h : ∀ v, f v = g v) : RelativeRecursive A g := (funext h) ▸ hf

private theorem bridge_precomp {m n : ℕ} {f : PartialRecursiveFunctions.PFunction m}
    (hf : RelativeRecursive A f)
    (g : Fin m → PartialRecursiveFunctions.Args n → ℕ)
    (hg : ∀ i, Primrec (g i)) :
    RelativeRecursive A (fun x => f (List.Vector.ofFn (fun i => g i x))) := by
  have hrec (i) := ordinary_relative A (PartialRecursiveFunctions.primitive_recursive_inclusion
    (Nat.Primrec'.prim_iff.mpr (hg i))).1
  apply RelativeRecursive.of_eq
    (RelativeRecursive.comp hf hrec)
  intro x
  apply Part.ext
  intro b
  simp only [PartialRecursiveFunctions.strictComp_spec, PartialRecursiveFunctions.lift,
    Part.mem_some_iff]
  constructor
  · rintro ⟨a, ha, hb⟩
    have he : a = List.Vector.ofFn (fun i => g i x) := by
      apply List.Vector.ext
      intro i
      simpa using ha i
    simpa only [he] using hb
  · intro hb
    exact ⟨List.Vector.ofFn (fun i => g i x), by simp, hb⟩

private theorem bridge_primitive {f : ℕ → ℕ} (hf : Primrec f) :
    RelativeRecursive A (fun v : PartialRecursiveFunctions.Args 1 =>
      Part.some (f (v.get 0))) := by
  exact ordinary_relative A (PartialRecursiveFunctions.primitive_recursive_inclusion
    (Nat.Primrec'.prim_iff.mpr
      (hf.comp (Primrec.vector_get.comp Primrec.id (Primrec.const 0))))).1

private theorem bridge_bind {n : ℕ} {f : ℕ → Part ℕ}
    {g : PartialRecursiveFunctions.PFunction n}
    (hf : RelativeRecursive A (fun v : PartialRecursiveFunctions.Args 1 => f (v.get 0)))
    (hg : RelativeRecursive A g) :
    RelativeRecursive A (fun v => (g v).bind f) := by
  apply (RelativeRecursive.comp hf (fun _ => hg)).of_eq
  intro v
  apply Part.ext
  intro b
  simp only [PartialRecursiveFunctions.strictComp_spec, Part.mem_bind_iff]
  constructor
  · rintro ⟨a, ha, hb⟩
    exact ⟨a.get 0, ha 0, hb⟩
  · rintro ⟨a, ha, hb⟩
    exact ⟨List.Vector.ofFn (fun _ => a), fun _ => by simpa using ha, by simpa using hb⟩

private theorem bridge_pair {n : ℕ} {f g : PartialRecursiveFunctions.PFunction n}
    (hf : RelativeRecursive A f) (hg : RelativeRecursive A g) :
    RelativeRecursive A (fun v => Nat.pair <$> f v <*> g v) := by
  let inn : Fin 2 → PartialRecursiveFunctions.PFunction n := Fin.cases f (fun _ => g)
  have hi : ∀ i, RelativeRecursive A (inn i) := by
    intro i
    exact Fin.cases hf (fun _ => hg) i
  have hp : RelativeRecursive A
      (PartialRecursiveFunctions.lift (fun v : PartialRecursiveFunctions.Args 2 =>
        Nat.pair (v.get 0) (v.get 1))) := by
    exact ordinary_relative A (PartialRecursiveFunctions.primitive_recursive_inclusion
      (Nat.Primrec'.prim_iff.mpr
        (Primrec₂.natPair.comp
          (Primrec.vector_get.comp Primrec.id (Primrec.const 0))
          (Primrec.vector_get.comp Primrec.id (Primrec.const 1))))).1
  apply (RelativeRecursive.comp hp hi).of_eq
  intro v
  apply Part.ext
  intro b
  simp only [PartialRecursiveFunctions.strictComp_spec, PartialRecursiveFunctions.lift,
    Part.mem_some_iff, Seq.seq, Part.map_eq_map, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨Nat.pair (a.get 0), ⟨a.get 0, ha 0, rfl⟩, a.get 1, ha 1, rfl⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, d, hd, rfl⟩
    refine ⟨List.Vector.ofFn (Fin.cases a (fun _ => d)), ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun _ => ?_) i
      · exact ha
      · simpa [inn] using hd
    · rfl

private theorem library_to_relative {f : ℕ → Part ℕ} (hf : Nat.RecursiveIn (oracleFunctions A) f) :
    RelativeRecursive A (fun v : PartialRecursiveFunctions.Args 1 => f (v.get 0)) := by
  induction hf with
  | zero => exact RelativeRecursive.zero 1
  | succ => exact RelativeRecursive.succ
  | left => exact bridge_primitive (Primrec.fst.comp Primrec.unpair)
  | right => exact bridge_primitive (Primrec.snd.comp Primrec.unpair)
  | oracle g hg =>
    have he : g = fun q => Part.some (indicator (fun n => n ∈ A) q) := by
      exact Set.mem_singleton_iff.mp hg
    subst g
    exact RelativeRecursive.query
  | pair hf hg ihf ihg => exact bridge_pair ihf ihg
  | comp hf hg ihf ihg => exact bridge_bind ihf ihg
  | @prec f g hf hg ihf ihg =>
    let step : PartialRecursiveFunctions.PFunction 3 := fun v =>
      g (Nat.pair (v.get 0) (Nat.pair (v.get 1) (v.get 2)))
    have hs : RelativeRecursive A step := by
      have hp : Primrec (fun v : PartialRecursiveFunctions.Args 3 =>
          Nat.pair (v.get 0) (Nat.pair (v.get 1) (v.get 2))) :=
        Primrec₂.natPair.comp (Primrec.vector_get.comp Primrec.id (Primrec.const 0))
          (Primrec₂.natPair.comp (Primrec.vector_get.comp Primrec.id (Primrec.const 1))
            (Primrec.vector_get.comp Primrec.id (Primrec.const 2)))
      exact (bridge_precomp ihg (fun _ v => Nat.pair (v.get 0)
        (Nat.pair (v.get 1) (v.get 2))) (fun _ => hp)).of_eq (fun _ => rfl)
    have hr := RelativeRecursive.prec ihf hs
    let coords : Fin 2 → PartialRecursiveFunctions.Args 1 → ℕ :=
      Fin.cases (fun v => (Nat.unpair (v.get 0)).1)
        (fun _ v => (Nat.unpair (v.get 0)).2)
    have hc : ∀ i, Primrec (coords i) := by
      intro i
      exact Fin.cases
        ((Primrec.fst.comp Primrec.unpair).comp
          (Primrec.vector_get.comp Primrec.id (Primrec.const 0)))
        (fun _ => (Primrec.snd.comp Primrec.unpair).comp
          (Primrec.vector_get.comp Primrec.id (Primrec.const 0))) i
    apply (bridge_precomp hr coords hc).of_eq
    intro v
    change PartialRecursiveFunctions.recValue (fun w => f (w.get 0)) step
      (List.Vector.ofFn (fun _ => (v.get 0).unpair.1)) (v.get 0).unpair.2 = _
    simp only
    generalize (v.get 0).unpair.2 = m
    induction m with
    | zero => rfl
    | succ m ih =>
      simpa [PartialRecursiveFunctions.recValue, step, PartialRecursiveFunctions.snoc, Fin.snoc]
        using congrArg (fun q : Part ℕ => q.bind
          (fun z => g (Nat.pair (v.get 0).unpair.1 (Nat.pair m z)))) ih
  | @rfind f hf ih =>
    have hs : RelativeRecursive A
        (fun v : PartialRecursiveFunctions.Args 2 => f (Nat.pair (v.get 0) (v.get 1))) := by
      exact (bridge_precomp ih (fun _ v => Nat.pair (v.get 0) (v.get 1))
        (fun _ => Primrec₂.natPair.comp
          (Primrec.vector_get.comp Primrec.id (Primrec.const 0))
          (Primrec.vector_get.comp Primrec.id (Primrec.const 1)))).of_eq (fun _ => rfl)
    exact (RelativeRecursive.search hs).of_eq (fun v => by
      simp [PartialRecursiveFunctions.minimize, PartialRecursiveFunctions.snoc, Fin.snoc])



theorem relative_finite_arity_iff {n : ℕ} (A : Set ℕ) (f : PFunction n) :
    RelativeRecursive A f ↔
      ∃ c : Code, ∀ v, eval A c (MachinesAndComputationHistories.tuplePack v) = f v := by
  constructor
  · exact relative_to_code
  · rintro ⟨c, hc⟩
    have hr := library_to_relative (code_to_library A c)
    apply (bridge_precomp hr (fun _ v => MachinesAndComputationHistories.tuplePack v)
      (fun _ => MachinesAndComputationHistories.tuple_pack_primrec n)).of_eq
    intro v
    simpa only [List.Vector.get_ofFn] using hc v

theorem ordinary_finite_arity_inclusion {n : ℕ} (A : Set ℕ) (f : PFunction n)
    (hf : PartialRecursiveFunctions.Recursive f) : RelativeRecursive A f := by
  exact ordinary_relative A hf

theorem relative_unary_iff (A : Set ℕ) (f : ℕ → Part ℕ) :
    RelativeRecursive A (fun v : Args 1 => f (v.get 0)) ↔ PartialComputable A f := by
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := relative_to_code hf
    obtain ⟨d, hd⟩ := ordinary_inclusion A Nat.Partrec.some
    refine ⟨.comp c (.pair d .zero), ?_⟩
    funext x
    have he := hc (List.Vector.ofFn (fun _ : Fin 1 => x))
    simpa [eval, hd, MachinesAndComputationHistories.tuplePack] using he
  · rintro ⟨c, rfl⟩
    exact library_to_relative (code_to_library A c)

end Lemmatheca.ComputabilityTheory.OracleComputation
