import Mathlib.Computability.PartrecCode
import Lemmatheca.MathematicalLogic.PartialRecursiveFunctions
import Lemmatheca.MathematicalLogic.FiniteSequenceCoding

/-! Deterministic arithmetic macro-step machines and their finite certificates.
The finite-arity `Recursive` predicate is the corpus definition; the bridge below
connects it to the encoded library basis rather than replacing that definition. -/
namespace Lemmatheca.MathematicalLogic.MachinesAndComputationHistories
open Part (pure_eq_some bind_eq_bind)

structure Machine where
  initial : ℕ → ℕ
  transition : ℕ → ℕ
  halt : ℕ → Bool
  output : ℕ → ℕ

def Primitive (M : Machine) : Prop :=
  Primrec M.initial ∧ Primrec M.transition ∧ Primrec M.halt ∧ Primrec M.output

def next (M : Machine) (c : ℕ) : ℕ := if M.halt c then c else M.transition c

def run (M : Machine) (x : ℕ) : ℕ → ℕ
  | 0 => M.initial x
  | t + 1 => next M (run M x t)

def compute (M : Machine) (x : ℕ) : Part ℕ :=
  (Nat.rfind (fun t => Part.some (M.halt (run M x t)))).map (fun t => M.output (run M x t))

def History (M : Machine) (x s : ℕ) : Prop :=
  0 < FiniteSequenceCoding.length s ∧ FiniteSequenceCoding.entry s 0 = M.initial x ∧
    M.halt (FiniteSequenceCoding.entry s (FiniteSequenceCoding.length s - 1)) = true ∧
      ∀ i < FiniteSequenceCoding.length s - 1,
        M.halt (FiniteSequenceCoding.entry s i) = false ∧ FiniteSequenceCoding.entry s (i + 1) = M.transition (FiniteSequenceCoding.entry s i)

instance (M : Machine) (x s : ℕ) : Decidable (History M x s) := by
  unfold History
  infer_instance

def Certificate (M : Machine) (x w : ℕ) : Prop :=
  History M x (Nat.unpair w).2 ∧ (Nat.unpair w).1 = M.output
    (FiniteSequenceCoding.entry (Nat.unpair w).2 (FiniteSequenceCoding.length (Nat.unpair w).2 - 1))

instance (M : Machine) (x w : ℕ) : Decidable (Certificate M x w) := by
  unfold Certificate
  infer_instance

def certificateTest (M : Machine) (x w : ℕ) : Bool := decide (Certificate M x w)
def firstCertificate (M : Machine) (x : ℕ) : Part ℕ :=
  Nat.rfind (fun w => Part.some (certificateTest M x w))
def extract (w : ℕ) : ℕ := (Nat.unpair w).1

private theorem primrec_snoc (n : ℕ) :
    Primrec₂ (@PartialRecursiveFunctions.snoc n) := by
  apply Primrec.vector_ofFn
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [PartialRecursiveFunctions.snoc, List.Vector.get_ofFn, Fin.snoc_last] using
      (@Primrec.snd (PartialRecursiveFunctions.Args n) ℕ _ _)
  · simpa only [PartialRecursiveFunctions.snoc, List.Vector.get_ofFn, Fin.snoc_castSucc] using
      (Primrec.vector_get.comp Primrec.fst (Primrec.const j))

private theorem primrec_init (n : ℕ) : Primrec (@PartialRecursiveFunctions.init n) :=
  Primrec.vector_ofFn fun i => Primrec.vector_get.comp Primrec.id (Primrec.const i.castSucc)

private theorem primrec_last (n : ℕ) : Primrec (@PartialRecursiveFunctions.last n) :=
  Primrec.vector_get.comp Primrec.id (Primrec.const (Fin.last n))

private theorem mem_mOfFn {n : ℕ} (p : Fin n → Part ℕ)
    (v : PartialRecursiveFunctions.Args n) :
    v ∈ List.Vector.mOfFn p ↔ ∀ i, v.get i ∈ p i := by
  induction n with
  | zero =>
    have hv : v = List.Vector.nil := Subsingleton.elim _ _
    simp [hv, List.Vector.mOfFn]
  | succ n ih =>
    simp only [List.Vector.mOfFn, pure_eq_some, bind_eq_bind, Part.mem_bind_iff,
      Part.mem_some_iff]
    constructor
    · rintro ⟨a, ha, w, hw, rfl⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ha
      · exact (ih _ w).mp hw j
    · intro h
      refine ⟨v.head, (by simpa using h 0), v.tail, (ih _ _).mpr (fun i => ?_), ?_⟩
      · simpa using h i.succ
      · exact (List.Vector.cons_head_tail v).symm

private theorem collect_partrec {α : Type*} [Primcodable α] {n : ℕ}
    (p : Fin n → α → Part ℕ) (hp : ∀ i, Partrec (p i)) :
    Partrec (fun x => PartialRecursiveFunctions.collect (fun i => p i x)) := by
  apply (Partrec.vector_mOfFn hp).of_eq
  intro x
  apply Part.ext
  intro v
  rw [mem_mOfFn, PartialRecursiveFunctions.collect_spec]

private theorem recursive_precomp {m n : ℕ} {f : PartialRecursiveFunctions.PFunction m}
    (hf : PartialRecursiveFunctions.Recursive f)
    (g : Fin m → PartialRecursiveFunctions.Args n → ℕ)
    (hg : ∀ i, Primrec (g i)) :
    PartialRecursiveFunctions.Recursive (fun x => f (List.Vector.ofFn (fun i => g i x))) := by
  have hrec (i) := (PartialRecursiveFunctions.primitive_recursive_inclusion
    (Nat.Primrec'.prim_iff.mpr (hg i))).1
  apply PartialRecursiveFunctions.Recursive.of_eq
    (PartialRecursiveFunctions.Recursive.comp hf hrec)
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

def tuplePack : {n : ℕ} → PartialRecursiveFunctions.Args n → ℕ
  | 0, _ => 0
  | _n + 1, v => Nat.pair v.head (tuplePack v.tail)

def tupleUnpack : (n : ℕ) → ℕ → PartialRecursiveFunctions.Args n
  | 0, _ => List.Vector.nil
  | n + 1, q => List.Vector.cons (Nat.unpair q).1 (tupleUnpack n (Nat.unpair q).2)

theorem tuple_pack_primrec (n : ℕ) : Primrec (@tuplePack n) := by
  induction n with
  | zero => exact Primrec.const 0
  | succ n ih => exact Primrec₂.natPair.comp Primrec.vector_head (ih.comp Primrec.vector_tail)

theorem tuple_unpack_primrec (n : ℕ) : Primrec (tupleUnpack n) := by
  induction n with
  | zero => exact Primrec.const List.Vector.nil
  | succ n ih =>
    exact Primrec.vector_cons.comp (Primrec.fst.comp Primrec.unpair)
      (ih.comp (Primrec.snd.comp Primrec.unpair))

theorem tuple_unpack_pack {n : ℕ} (v : PartialRecursiveFunctions.Args n) :
    tupleUnpack n (tuplePack v) = v := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [tuplePack, tupleUnpack, Nat.unpair_pair, ih, List.Vector.cons_head_tail]

/-- A genuine finite-arity representation bridge, including zero arguments. -/
theorem recursive_partrec {n : ℕ} {f : PartialRecursiveFunctions.PFunction n}
    (hf : PartialRecursiveFunctions.Recursive f) : Partrec f := by
  induction hf with
  | zero => exact (Computable.const 0).partrec
  | succ =>
    exact (Primrec.succ.comp (Primrec.vector_get.comp Primrec.id (Primrec.const 0))).to_comp.partrec
  | proj i => exact (Primrec.vector_get.comp Primrec.id (Primrec.const i)).to_comp.partrec
  | comp hh hg ihh ihg =>
    exact (collect_partrec _ ihg).bind (ihh.comp Computable.snd).to₂
  | @prec k g h hg hh ihg ihh =>
    have hstep : Partrec₂ (fun x : PartialRecursiveFunctions.Args (k + 1) =>
        fun p : ℕ × ℕ => h (PartialRecursiveFunctions.snoc
          (PartialRecursiveFunctions.snoc (PartialRecursiveFunctions.init x) p.1) p.2)) := by
      exact ihh.comp ((primrec_snoc (k + 1)).comp
        ((primrec_snoc k).comp ((primrec_init k).comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to_comp
    apply ((Partrec.nat_rec (primrec_last k).to_comp
      (ihg.comp (primrec_init k).to_comp) hstep)).of_eq
    intro v
    unfold PartialRecursiveFunctions.partialRec
    induction PartialRecursiveFunctions.last v with
    | zero => rfl
    | succ n ih => exact congrArg (fun p : Part ℕ => p.bind _) ih
  | @search k f hf ih =>
    apply Partrec.rfind
    exact (ih.comp (primrec_snoc k).to_comp).map
      ((Primrec.eq.comp Primrec.snd (Primrec.const 0)).decide.to_comp).to₂

private theorem unary_primitive {f : ℕ → ℕ} (hf : Primrec f) :
    PartialRecursiveFunctions.Recursive (fun v : PartialRecursiveFunctions.Args 1 =>
      Part.some (f (v.get 0))) := by
  exact (PartialRecursiveFunctions.primitive_recursive_inclusion
    (Nat.Primrec'.prim_iff.mpr
      (hf.comp (Primrec.vector_get.comp Primrec.id (Primrec.const 0))))).1

private theorem recursive_bind {n : ℕ} {f : ℕ → Part ℕ}
    {g : PartialRecursiveFunctions.PFunction n}
    (hf : PartialRecursiveFunctions.Recursive (fun v : PartialRecursiveFunctions.Args 1 => f (v.get 0)))
    (hg : PartialRecursiveFunctions.Recursive g) :
    PartialRecursiveFunctions.Recursive (fun v => (g v).bind f) := by
  apply (PartialRecursiveFunctions.Recursive.comp hf (fun _ => hg)).of_eq
  intro v
  apply Part.ext
  intro b
  simp only [PartialRecursiveFunctions.strictComp_spec, Part.mem_bind_iff]
  constructor
  · rintro ⟨a, ha, hb⟩
    exact ⟨a.get 0, ha 0, hb⟩
  · rintro ⟨a, ha, hb⟩
    exact ⟨List.Vector.ofFn (fun _ => a), fun _ => by simpa using ha, by simpa using hb⟩

private theorem recursive_pair {n : ℕ} {f g : PartialRecursiveFunctions.PFunction n}
    (hf : PartialRecursiveFunctions.Recursive f) (hg : PartialRecursiveFunctions.Recursive g) :
    PartialRecursiveFunctions.Recursive (fun v => Nat.pair <$> f v <*> g v) := by
  let inn : Fin 2 → PartialRecursiveFunctions.PFunction n := Fin.cases f (fun _ => g)
  have hi : ∀ i, PartialRecursiveFunctions.Recursive (inn i) := by
    intro i
    exact Fin.cases hf (fun _ => hg) i
  have hp : PartialRecursiveFunctions.Recursive
      (PartialRecursiveFunctions.lift (fun v : PartialRecursiveFunctions.Args 2 =>
        Nat.pair (v.get 0) (v.get 1))) := by
    exact (PartialRecursiveFunctions.primitive_recursive_inclusion
      (Nat.Primrec'.prim_iff.mpr
        (Primrec₂.natPair.comp
          (Primrec.vector_get.comp Primrec.id (Primrec.const 0))
          (Primrec.vector_get.comp Primrec.id (Primrec.const 1))))).1
  apply (PartialRecursiveFunctions.Recursive.comp hp hi).of_eq
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

theorem nat_partrec_recursive {f : ℕ → Part ℕ} (hf : Nat.Partrec f) :
    PartialRecursiveFunctions.Recursive (fun v : PartialRecursiveFunctions.Args 1 => f (v.get 0)) := by
  induction hf with
  | zero => exact PartialRecursiveFunctions.Recursive.zero 1
  | succ => exact PartialRecursiveFunctions.Recursive.succ
  | left => exact unary_primitive (Primrec.fst.comp Primrec.unpair)
  | right => exact unary_primitive (Primrec.snd.comp Primrec.unpair)
  | pair hf hg ihf ihg => exact recursive_pair ihf ihg
  | comp hf hg ihf ihg => exact recursive_bind ihf ihg
  | @prec f g hf hg ihf ihg =>
    let step : PartialRecursiveFunctions.PFunction 3 := fun v =>
      g (Nat.pair (v.get 0) (Nat.pair (v.get 1) (v.get 2)))
    have hs : PartialRecursiveFunctions.Recursive step := by
      have hp : Primrec (fun v : PartialRecursiveFunctions.Args 3 =>
          Nat.pair (v.get 0) (Nat.pair (v.get 1) (v.get 2))) :=
        Primrec₂.natPair.comp (Primrec.vector_get.comp Primrec.id (Primrec.const 0))
          (Primrec₂.natPair.comp (Primrec.vector_get.comp Primrec.id (Primrec.const 1))
            (Primrec.vector_get.comp Primrec.id (Primrec.const 2)))
      exact (recursive_precomp ihg (fun _ v => Nat.pair (v.get 0)
        (Nat.pair (v.get 1) (v.get 2))) (fun _ => hp)).of_eq (fun _ => rfl)
    have hr := PartialRecursiveFunctions.Recursive.prec ihf hs
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
    apply (recursive_precomp hr coords hc).of_eq
    intro v
    change PartialRecursiveFunctions.recValue (fun w => f (w.get 0)) step
      (List.Vector.ofFn (fun _ => (v.get 0).unpair.1)) (v.get 0).unpair.2 = _
    simp only [Nat.unpaired]
    generalize (v.get 0).unpair.2 = m
    induction m with
    | zero => rfl
    | succ m ih =>
      simpa [PartialRecursiveFunctions.recValue, step, PartialRecursiveFunctions.snoc, Fin.snoc]
        using congrArg (fun q : Part ℕ => q.bind
          (fun z => g (Nat.pair (v.get 0).unpair.1 (Nat.pair m z)))) ih
  | @rfind f hf ih =>
    have hs : PartialRecursiveFunctions.Recursive
        (fun v : PartialRecursiveFunctions.Args 2 => f (Nat.pair (v.get 0) (v.get 1))) := by
      exact (recursive_precomp ih (fun _ v => Nat.pair (v.get 0) (v.get 1))
        (fun _ => Primrec₂.natPair.comp
          (Primrec.vector_get.comp Primrec.id (Primrec.const 0))
          (Primrec.vector_get.comp Primrec.id (Primrec.const 1)))).of_eq (fun _ => rfl)
    exact (PartialRecursiveFunctions.Recursive.search hs).of_eq (fun v => by
      simp [PartialRecursiveFunctions.minimize, PartialRecursiveFunctions.snoc, Fin.snoc])

theorem recursive_iff_partrec {n : ℕ} {f : PartialRecursiveFunctions.PFunction n} :
    PartialRecursiveFunctions.Recursive f ↔ Partrec f := by
  constructor
  · exact recursive_partrec
  · intro hf
    have hr := nat_partrec_recursive hf
    apply (recursive_precomp hr (fun _ v => Encodable.encode v)
      (fun _ => Primrec.encode)).of_eq
    intro v
    simp only [List.Vector.get_ofFn, Encodable.encodek, Part.coe_some, Part.bind_some]
    change Part.map id (f v) = f v
    exact Part.map_id' (fun x => rfl) (f v)

theorem unary_recursive_iff {f : ℕ → Part ℕ} :
    PartialRecursiveFunctions.Recursive (fun v : PartialRecursiveFunctions.Args 1 => f (v.get 0)) ↔ Nat.Partrec f := by
  constructor
  · intro hf
    have hc : Computable (fun x : ℕ => List.Vector.ofFn (fun _ : Fin 1 => x)) :=
      (Primrec.vector_ofFn (fun _ => Primrec.id)).to_comp
    exact Partrec.nat_iff.mp ((recursive_partrec hf).comp hc)
  · exact nat_partrec_recursive

theorem paired_program_iff {f : ℕ → Part ℕ} :
    PartialRecursiveFunctions.Recursive (fun v : PartialRecursiveFunctions.Args 1 => f (v.get 0)) ↔
      ∃ c : Nat.Partrec.Code, Nat.Partrec.Code.eval c = f := by
  exact unary_recursive_iff.trans Nat.Partrec.Code.exists_code

theorem finite_arity_program_iff {n : ℕ} {f : PartialRecursiveFunctions.PFunction n} :
    PartialRecursiveFunctions.Recursive f ↔
      ∃ c : Nat.Partrec.Code, ∀ v, Nat.Partrec.Code.eval c (tuplePack v) = f v := by
  constructor
  · intro hf
    have hp := (recursive_partrec hf).comp (tuple_unpack_primrec n).to_comp
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hp)
    refine ⟨c, fun v => ?_⟩
    simp only [hc, tuple_unpack_pack]
  · rintro ⟨c, hc⟩
    have hp : Nat.Partrec (Nat.Partrec.Code.eval c) :=
      Nat.Partrec.Code.exists_code.mpr ⟨c, rfl⟩
    exact recursive_iff_partrec.mpr
      (((Partrec.nat_iff.mpr hp).comp (tuple_pack_primrec n).to_comp).of_eq hc)

theorem next_primrec (M : Machine) (hM : Primitive M) : Primrec (next M) := by
  exact (Primrec.cond hM.2.2.1 Primrec.id hM.2.1).of_eq fun c => by
    cases h : M.halt c <;> simp [next, h]

theorem run_primrec (M : Machine) (hM : Primitive M) : Primrec₂ (run M) := by
  exact (Primrec.nat_rec hM.1 ((next_primrec M hM).comp (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun x n => by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg (next M) ih

theorem run_zero (M : Machine) (x : ℕ) : run M x 0 = M.initial x := by
  rfl

theorem run_succ (M : Machine) (x t : ℕ) :
    run M x (t + 1) = if M.halt (run M x t) then run M x t else M.transition (run M x t) := by
  rfl

theorem run_absorbing (M : Machine) (x t j : ℕ) (h : M.halt (run M x t) = true) :
    run M x (t + j) = run M x t := by
  induction j with
  | zero => simp
  | succ j ih => simp [run, next, ih, h]

theorem compute_output (M : Machine) (x y : ℕ) :
    y ∈ compute M x ↔ ∃ t, M.halt (run M x t) = true ∧ M.output (run M x t) = y := by
  simp only [compute, Part.mem_map_iff]
  constructor
  · rintro ⟨t, ht, ho⟩
    exact ⟨t, by
      have hh : true = M.halt (run M x t) := by
        simpa only [Part.mem_some_iff] using Nat.rfind_spec ht
      exact hh.symm, ho⟩
  · rintro ⟨t, ht, ho⟩
    have hd : (Nat.rfind (fun n => Part.some (M.halt (run M x n)))).Dom := by
      exact Nat.rfind_dom.mpr ⟨t, by simpa using ht.symm, fun _ => trivial⟩
    obtain ⟨n, hn⟩ := Part.dom_iff_mem.mp hd
    have hhn : M.halt (run M x n) = true := by
      have hh : true = M.halt (run M x n) := by
        simpa only [Part.mem_some_iff] using Nat.rfind_spec hn
      exact hh.symm
    have he : run M x n = run M x t := by
      rcases le_total n t with hnt | htn
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnt
        exact (run_absorbing M x n j hhn).symm
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le htn
        exact run_absorbing M x t j ht
    exact ⟨n, hn, by simpa only [he] using ho⟩

theorem history_primrec (M : Machine) (hM : Primitive M) : PrimrecRel (History M) := by
  have hl : Primrec (fun p : ℕ × ℕ => FiniteSequenceCoding.length p.2) :=
    FiniteSequenceCoding.primrec_length.comp Primrec.snd
  have hb : Primrec (fun p : ℕ × ℕ => FiniteSequenceCoding.length p.2 - 1) :=
    Primrec.nat_sub.comp hl (Primrec.const 1)
  have he : Primrec (fun p : ℕ × ℕ => FiniteSequenceCoding.entry p.2 0) :=
    FiniteSequenceCoding.primrec_entry.comp Primrec.snd (Primrec.const 0)
  have heLast : Primrec (fun p : ℕ × ℕ =>
      FiniteSequenceCoding.entry p.2 (FiniteSequenceCoding.length p.2 - 1)) :=
    FiniteSequenceCoding.primrec_entry.comp Primrec.snd hb
  have hi : PrimrecRel (fun i (p : ℕ × ℕ) =>
      M.halt (FiniteSequenceCoding.entry p.2 i) = false ∧
        FiniteSequenceCoding.entry p.2 (i + 1) = M.transition (FiniteSequenceCoding.entry p.2 i)) := by
    have hentry : Primrec (fun q : ℕ × (ℕ × ℕ) => FiniteSequenceCoding.entry q.2.2 q.1) :=
      FiniteSequenceCoding.primrec_entry.comp (Primrec.snd.comp Primrec.snd) Primrec.fst
    have hnext : Primrec (fun q : ℕ × (ℕ × ℕ) => FiniteSequenceCoding.entry q.2.2 (q.1 + 1)) :=
      FiniteSequenceCoding.primrec_entry.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.succ.comp Primrec.fst)
    exact (Primrec.eq.comp (hM.2.2.1.comp hentry) (Primrec.const false)).and
      (Primrec.eq.comp hnext (hM.2.1.comp hentry))
  have hAll : PrimrecPred (fun p : ℕ × ℕ =>
      ∀ i < FiniteSequenceCoding.length p.2 - 1,
        M.halt (FiniteSequenceCoding.entry p.2 i) = false ∧
          FiniteSequenceCoding.entry p.2 (i + 1) = M.transition (FiniteSequenceCoding.entry p.2 i)) :=
    ((PrimrecRel.forall_mem_list hi).comp (Primrec.list_range.comp hb) Primrec.id).of_eq
      (fun p => by simp)
  exact (Primrec.nat_lt.comp (Primrec.const 0) hl).and
    ((Primrec.eq.comp he (hM.1.comp Primrec.fst)).and
      ((Primrec.eq.comp (hM.2.2.1.comp heLast) (Primrec.const true)).and
        hAll))

theorem certificate_primrec (M : Machine) (hM : Primitive M) : PrimrecRel (Certificate M) := by
  have hs : Primrec (fun p : ℕ × ℕ => (Nat.unpair p.2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hy : Primrec (fun p : ℕ × ℕ => (Nat.unpair p.2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hb : Primrec (fun p : ℕ × ℕ => FiniteSequenceCoding.length (Nat.unpair p.2).2 - 1) :=
    Primrec.nat_sub.comp (FiniteSequenceCoding.primrec_length.comp hs) (Primrec.const 1)
  exact ((history_primrec M hM).comp Primrec.fst hs).and
    (Primrec.eq.comp hy (hM.2.2.2.comp (FiniteSequenceCoding.primrec_entry.comp hs hb)))

theorem history_run (M : Machine) (x s i : ℕ) (hs : History M x s) (hi : i < FiniteSequenceCoding.length s) :
    FiniteSequenceCoding.entry s i = run M x i := by
  induction i with
  | zero => exact hs.2.1
  | succ i ih =>
    have hii : i < FiniteSequenceCoding.length s := by omega
    have hstep := hs.2.2.2 i (by omega)
    rw [run, next, ← ih hii, hstep.1]
    exact hstep.2

private theorem first_halt_history (M : Machine) (x t : ℕ)
    (ht : M.halt (run M x t) = true)
    (hmin : ∀ i < t, M.halt (run M x i) = false) :
    History M x (FiniteSequenceCoding.code ((List.range (t + 1)).map (run M x))) := by
  let s := FiniteSequenceCoding.code ((List.range (t + 1)).map (run M x))
  have hl : FiniteSequenceCoding.length s = t + 1 := by
    simp [s, FiniteSequenceCoding.length]
  have he (i : ℕ) (hi : i ≤ t) : FiniteSequenceCoding.entry s i = run M x i := by
    simp [s, FiniteSequenceCoding.entry_code,
      show i < t + 1 by omega]
  change History M x s
  refine ⟨by omega, ?_, ?_, ?_⟩
  · rw [he 0 (by omega)]
    rfl
  · simpa only [hl, Nat.add_sub_cancel, he t (by omega)] using ht
  · intro i hi
    have hit : i < t := by omega
    rw [he i (by omega), he (i + 1) (by omega)]
    refine ⟨hmin i hit, ?_⟩
    simp only [run, next, hmin i hit, Bool.false_eq_true, ↓reduceIte]

theorem history_exists (M : Machine) (x : ℕ) :
    (compute M x).Dom ↔ ∃ s, History M x s := by
  constructor
  · intro hd
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨t, ht, _⟩ := (compute_output M x y).mp hy
    have hex : ∃ t, M.halt (run M x t) = true := ⟨t, ht⟩
    refine ⟨_, first_halt_history M x (Nat.find hex) (Nat.find_spec hex) ?_⟩
    intro i hi
    exact Bool.eq_false_iff.mpr (Nat.find_min hex hi)
  · rintro ⟨s, hs⟩
    have he := history_run M x s (FiniteSequenceCoding.length s - 1) hs (by have hpos := hs.1; omega)
    have hy : M.output (run M x (FiniteSequenceCoding.length s - 1)) ∈ compute M x :=
      (compute_output M x _).mpr ⟨FiniteSequenceCoding.length s - 1, by simpa only [← he] using hs.2.2.1, rfl⟩
    exact hy.1

theorem certificate_output (M : Machine) (x y : ℕ) :
    y ∈ compute M x ↔ ∃ w, Certificate M x w ∧ extract w = y := by
  constructor
  · intro hy
    obtain ⟨s, hs⟩ := (history_exists M x).mp hy.1
    have he := history_run M x s (FiniteSequenceCoding.length s - 1) hs (by have hpos := hs.1; omega)
    have hout : M.output (FiniteSequenceCoding.entry s (FiniteSequenceCoding.length s - 1)) ∈
        compute M x := (compute_output M x _).mpr ⟨FiniteSequenceCoding.length s - 1, by simpa only [← he] using hs.2.2.1,
          by rw [he]⟩
    refine ⟨Nat.pair y s, ?_, by simp [extract]⟩
    change History M x (Nat.unpair (Nat.pair y s)).2 ∧ _
    simp only [Nat.unpair_pair]
    exact ⟨hs, (Part.mem_unique hout hy).symm⟩
  · rintro ⟨w, hw, he⟩
    have hs := hw.1
    have hr := history_run M x (Nat.unpair w).2
      (FiniteSequenceCoding.length (Nat.unpair w).2 - 1) hs (by have hpos := hs.1; omega)
    apply (compute_output M x y).mpr
    refine ⟨FiniteSequenceCoding.length (Nat.unpair w).2 - 1, by simpa only [← hr] using hs.2.2.1, ?_⟩
    rw [← hr, ← hw.2]
    exact he

theorem compute_search (M : Machine) (x : ℕ) :
    compute M x = (firstCertificate M x).map extract := by
  apply Part.ext
  intro y
  simp only [Part.mem_map_iff]
  constructor
  · intro hy
    obtain ⟨w, hw, _⟩ := (certificate_output M x y).mp hy
    have hd : (firstCertificate M x).Dom := by
      apply Nat.rfind_dom.mpr
      exact ⟨w, by simpa only [Part.mem_some_iff, certificateTest] using (decide_eq_true hw).symm,
        fun _ => trivial⟩
    obtain ⟨u, hu⟩ := Part.dom_iff_mem.mp hd
    have huc : Certificate M x u := by
      have h : true = certificateTest M x u := by
        simpa only [Part.mem_some_iff] using Nat.rfind_spec hu
      exact of_decide_eq_true h.symm
    have hout : extract u ∈ compute M x := (certificate_output M x _).mpr ⟨u, huc, rfl⟩
    exact ⟨u, hu, Part.mem_unique hout hy⟩
  · rintro ⟨w, hw, he⟩
    have hcert : Certificate M x w := by
      have h : true = certificateTest M x w := by
        simpa only [Part.mem_some_iff] using Nat.rfind_spec hw
      exact of_decide_eq_true h.symm
    exact (certificate_output M x y).mpr ⟨w, hcert, he⟩

theorem compute_partrec (M : Machine) (hM : Primitive M) : Nat.Partrec (compute M) := by
  have hr : Primrec₂ (run M) := run_primrec M hM
  have hhalt : Partrec₂ (fun x t => Part.some (M.halt (run M x t))) :=
    (hM.2.2.1.comp hr).to_comp.partrec.to₂
  have hout : Computable₂ (fun x t => M.output (run M x t)) :=
    (hM.2.2.2.comp hr).to_comp.to₂
  exact Partrec.nat_iff.mp ((Partrec.rfind hhalt).map hout)

theorem compute_recursive (M : Machine) (hM : Primitive M) :
    PartialRecursiveFunctions.Recursive (fun v : PartialRecursiveFunctions.Args 1 => compute M (v.get 0)) := by
  exact unary_recursive_iff.mpr (compute_partrec M hM)

def bounded (c : Nat.Partrec.Code) (k x : ℕ) : Option ℕ := Nat.Partrec.Code.evaln k c x

def boundedNumber (c : Nat.Partrec.Code) (k x : ℕ) : ℕ :=
  match bounded c k x with
  | none => 0
  | some y => y + 1

theorem bounded_primrec (c : Nat.Partrec.Code) : Primrec₂ (bounded c) := by
  exact Nat.Partrec.Code.primrec_evaln.comp
    ((Primrec.fst.pair (Primrec.const c)).pair Primrec.snd)

theorem bounded_number_primrec (c : Nat.Partrec.Code) : Primrec₂ (boundedNumber c) := by
  exact (Primrec.encode.comp (bounded_primrec c)).of_eq fun p => by
    cases h : bounded c p.1 p.2 <;> simp [boundedNumber, h]

theorem bounded_number_some (c : Nat.Partrec.Code) (k x y : ℕ) :
    boundedNumber c k x = y + 1 ↔ bounded c k x = some y := by
  unfold boundedNumber
  cases bounded c k x <;> simp

def evaluationMachine (c : Nat.Partrec.Code) : Machine where
  initial x := Nat.pair x (Nat.pair 0 0)
  transition q :=
    let x := (Nat.unpair q).1
    let k := (Nat.unpair (Nat.unpair q).2).1
    Nat.pair x (Nat.pair (k + 1) (boundedNumber c (k + 1) x))
  halt q := decide (0 < (Nat.unpair (Nat.unpair q).2).2)
  output q := (Nat.unpair (Nat.unpair q).2).2 - 1

theorem evaluationMachine_primitive (c : Nat.Partrec.Code) : Primitive (evaluationMachine c) := by
  have hx : Primrec (fun q : ℕ => (Nat.unpair q).1) := Primrec.fst.comp Primrec.unpair
  have ht : Primrec (fun q : ℕ => (Nat.unpair q).2) := Primrec.snd.comp Primrec.unpair
  have hk : Primrec (fun q : ℕ => (Nat.unpair (Nat.unpair q).2).1) := hx.comp ht
  have hb : Primrec (fun q : ℕ => (Nat.unpair (Nat.unpair q).2).2) := ht.comp ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Primrec₂.natPair.comp Primrec.id
      (Primrec₂.natPair.comp (Primrec.const 0) (Primrec.const 0))
  · exact Primrec₂.natPair.comp hx
      (Primrec₂.natPair.comp (Primrec.succ.comp hk)
        ((bounded_number_primrec c).comp (Primrec.succ.comp hk) hx))
  · exact (Primrec.nat_lt.comp (Primrec.const 0) hb).decide
  · exact Primrec.nat_sub.comp hb (Primrec.const 1)

private def evaluationState (c : Nat.Partrec.Code) (x k : ℕ) : ℕ :=
  Nat.pair x (Nat.pair k (boundedNumber c k x))

private theorem evaluation_run_state (c : Nat.Partrec.Code) (x t : ℕ) :
    ∃ k, run (evaluationMachine c) x t = evaluationState c x k := by
  induction t with
  | zero => exact ⟨0, by simp [run, evaluationState, evaluationMachine, boundedNumber, bounded, Nat.Partrec.Code.evaln]⟩
  | succ t ih =>
    obtain ⟨k, hk⟩ := ih
    rw [run, next, hk]
    cases hh : (evaluationMachine c).halt (evaluationState c x k) with
    | false => exact ⟨k + 1, by simp [evaluationState, evaluationMachine]⟩
    | true => exact ⟨k, by simp⟩

theorem evaluationMachine_compute (c : Nat.Partrec.Code) :
    compute (evaluationMachine c) = Nat.Partrec.Code.eval c := by
  funext x
  apply Part.ext
  intro y
  have hs (z : ℕ) (hz : z ∈ compute (evaluationMachine c) x) : z ∈ Nat.Partrec.Code.eval c x := by
    obtain ⟨t, ht, ho⟩ := (compute_output (evaluationMachine c) x z).mp hz
    obtain ⟨k, hk⟩ := evaluation_run_state c x t
    rw [hk] at ht ho
    have hb : 0 < boundedNumber c k x := by
      simpa only [evaluationMachine, evaluationState, Nat.unpair_pair, decide_eq_true_eq] using ht
    cases he : bounded c k x with
    | none => simp only [boundedNumber, he, Nat.lt_irrefl] at hb
    | some a =>
      have ha : a = z := by
        simpa only [evaluationMachine, evaluationState, Nat.unpair_pair,
          boundedNumber, he, Nat.add_sub_cancel] using ho
      exact ha ▸ Nat.Partrec.Code.evaln_sound he
  constructor
  · exact hs y
  · intro hy
    have hd : (compute (evaluationMachine c) x).Dom := by
      by_contra hn
      have hnever (t : ℕ) : (evaluationMachine c).halt (run (evaluationMachine c) x t) = false := by
        apply Bool.eq_false_iff.mpr
        intro hh
        exact hn ((compute_output (evaluationMachine c) x _).mpr ⟨t, hh, rfl⟩).1
      have hrun (t : ℕ) : run (evaluationMachine c) x t = evaluationState c x t := by
        induction t with
        | zero => simp [run, evaluationState, evaluationMachine, boundedNumber, bounded, Nat.Partrec.Code.evaln]
        | succ t ih =>
          rw [run, next, hnever t]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [ih]
          simp only [evaluationState, evaluationMachine, Nat.unpair_pair]
      obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hy
      have hk' : Nat.Partrec.Code.evaln k c x = some y := hk
      have hfalse := hnever k
      rw [hrun k] at hfalse
      simp only [evaluationMachine, evaluationState, Nat.unpair_pair,
        boundedNumber, bounded, hk', Nat.zero_lt_succ, decide_true, Bool.true_eq_false] at hfalse
    obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp hd
    exact (Part.mem_unique (hs z hz) hy) ▸ hz

def MachineComputable (f : ℕ → Part ℕ) : Prop :=
  ∃ M : Machine, Primitive M ∧ compute M = f

theorem machine_equivalence (f : ℕ → Part ℕ) :
    MachineComputable f ↔ PartialRecursiveFunctions.Recursive (fun v : PartialRecursiveFunctions.Args 1 => f (v.get 0)) := by
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact compute_recursive M hM
  · intro hf
    obtain ⟨c, rfl⟩ := paired_program_iff.mp hf
    exact ⟨evaluationMachine c, evaluationMachine_primitive c, evaluationMachine_compute c⟩

/-- Finite tuples, including the empty tuple, are packed before machine input. -/
theorem finite_arity_machine_iff {n : ℕ} {f : PartialRecursiveFunctions.PFunction n} :
    PartialRecursiveFunctions.Recursive f ↔
      ∃ M : Machine, Primitive M ∧ ∀ v, compute M (tuplePack v) = f v := by
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := finite_arity_program_iff.mp hf
    exact ⟨evaluationMachine c, evaluationMachine_primitive c,
      fun v => (congrFun (evaluationMachine_compute c) (tuplePack v)).trans (hc v)⟩
  · rintro ⟨M, hM, hf⟩
    apply recursive_iff_partrec.mpr
    exact (((Partrec.nat_iff.mpr (compute_partrec M hM)).comp
      (tuple_pack_primrec n).to_comp).of_eq hf)

def searchTest (T : ℕ → ℕ → Bool) (x : ℕ) : Part ℕ :=
  Nat.rfind (fun w => Part.some (T x w))

theorem normal_form (f : ℕ → Part ℕ)
    (hf : PartialRecursiveFunctions.Recursive (fun v : PartialRecursiveFunctions.Args 1 => f (v.get 0))) :
    ∃ T : ℕ → ℕ → Bool, Primrec₂ T ∧
      (∀ x y, y ∈ f x ↔ ∃ w, T x w = true ∧ extract w = y) ∧
      (∀ x, f x = (searchTest T x).map extract) ∧
      (∀ x u v, T x u = true → T x v = true → extract u = extract v) := by
  obtain ⟨M, hM, hMf⟩ := (machine_equivalence f).mpr hf
  refine ⟨certificateTest M, (certificate_primrec M hM).decide, ?_, ?_, ?_⟩
  · intro x y
    rw [← hMf]
    simpa only [certificateTest, decide_eq_true_eq] using certificate_output M x y
  · intro x
    rw [← hMf]
    exact compute_search M x
  · intro x u v hu hv
    have hcu : Certificate M x u := by simpa only [certificateTest, decide_eq_true_eq] using hu
    have hcv : Certificate M x v := by simpa only [certificateTest, decide_eq_true_eq] using hv
    exact Part.mem_unique ((certificate_output M x _).mpr ⟨u, hcu, rfl⟩)
      ((certificate_output M x _).mpr ⟨v, hcv, rfl⟩)

theorem normal_form_converse (T : ℕ → ℕ → Bool) (hT : Primrec₂ T) :
    PartialRecursiveFunctions.Recursive (fun v : PartialRecursiveFunctions.Args 1 => (searchTest T (v.get 0)).map extract) := by
  apply (unary_recursive_iff (f := fun x => (searchTest T x).map extract)).mpr
  have hs : Partrec (searchTest T) := Partrec.rfind hT.to_comp.partrec.to₂
  have hu : Primrec extract := Primrec.fst.comp Primrec.unpair
  exact Partrec.nat_iff.mp (hs.map (hu.comp Primrec.snd).to_comp.to₂)

theorem no_fixed_allowance (k : ℕ) :
    bounded .zero k k = none ∧ Nat.Partrec.Code.eval .zero k = Part.some 0 := by
  refine ⟨?_, rfl⟩
  cases h : bounded .zero k k with
  | none => rfl
  | some y => exact (Nat.lt_irrefl k (Nat.Partrec.Code.evaln_bound h)).elim

end Lemmatheca.MathematicalLogic.MachinesAndComputationHistories
