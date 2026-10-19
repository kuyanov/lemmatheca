import Lemmatheca.MathematicalLogic.ArithmeticRepresentabilityRecursion
import Lemmatheca.MathematicalLogic.MachinesAndComputationHistories

/-! Total computable functions are strongly numeralwise represented in the
shared Robinson theory. The finite-arity conclusion uses the corpus's specified
tuple packing, and the normal-form argument searches a total primitive-recursive
test, without asserting totality of arbitrary partial-recursive subprograms. -/
namespace Lemmatheca.MathematicalLogic.ArithmeticRepresentability
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories
noncomputable section

def Representable {n : ℕ} (f : (Fin n → ℕ) → ℕ) : Prop :=
  ∃ φ : language.Formula (Fin n ⊕ Unit), StronglyRepresents f φ

private theorem vector_ofFn_snoc {n : ℕ} (x : Fin n → ℕ) (a : ℕ) :
    List.Vector.ofFn (Fin.snoc x a) =
      List.Vector.ofFn x ++ a ::ᵥ List.Vector.nil := by
  apply List.Vector.toList_injective
  simp only [List.Vector.toList_ofFn, List.Vector.toList_append,
    List.Vector.toList_cons, List.Vector.toList_nil]
  rw [List.ofFn_succ']
  simp

private theorem primitiveRec_lastRec {n : ℕ}
    (f : PrimitiveRecursion.Args n → ℕ) (g : PrimitiveRecursion.Args (n + 2) → ℕ)
    (x : Fin n → ℕ) (k : ℕ) :
    primitiveRec (fun v => f (List.Vector.ofFn v)) (fun v => g (List.Vector.ofFn v)) x k =
      PrimitiveRecursion.recValue f (fun v i u => g (v ++ i ::ᵥ u ::ᵥ List.Vector.nil))
        (List.Vector.ofFn x) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [primitiveRec, PrimitiveRecursion.recValue, ih, vector_ofFn_snoc]
    congr 1
    apply List.Vector.toList_injective
    simp

theorem primitive_recursive_representable {n : ℕ}
    (f : PrimitiveRecursion.Args n → ℕ) (hf : Nat.Primrec' f) :
    Representable (fun x => f (List.Vector.ofFn x)) := by
  refine PrimitiveRecursion.generated_by_lastRec
    (C := fun {m} g => Representable (fun x : Fin m → ℕ => g (List.Vector.ofFn x)))
    ?_ ?_ ?_ ?_ ?_ hf
  · refine ⟨termGraph zeroTerm, ?_⟩
    convert term_stronglyRepresents (n := 0) zeroTerm using 1
    funext x
    rfl
  · refine ⟨termGraph (succTerm (.var 0)), ?_⟩
    convert term_stronglyRepresents (succTerm (.var (0 : Fin 1))) using 1
    funext x
    dsimp only
    rw [List.Vector.head_ofFn]
    rfl
  · intro m i
    refine ⟨termGraph (.var i), ?_⟩
    simpa only [Term.realize_var, List.Vector.get_ofFn] using
      (term_stronglyRepresents (.var i))
  · intro m k f g hf hg
    obtain ⟨φ, hφ⟩ := hf
    choose ψ hψ using hg
    exact ⟨compositionGraph φ ψ,
      composition_stronglyRepresents (fun x => f (List.Vector.ofFn x))
        (fun i x => g i (List.Vector.ofFn x)) φ ψ hφ hψ⟩
  · intro m f g hf hg
    obtain ⟨φ, hφ⟩ := hf
    obtain ⟨ψ, hψ⟩ := hg
    have hcodes : ∀ k (a : Fin k → ℕ), ∃ c d,
        ∀ i, (fun v : Fin 3 → ℕ => beta (v 0) (v 1) (v 2)) ![c, d, i.val] = a i := by
      intro k a
      obtain ⟨c, d, _, hcd⟩ := beta_codes_finite_tuple k a
      exact ⟨c, d, by simpa using hcd⟩
    refine ⟨recursionGraph betaGraph φ ψ, ?_⟩
    have hr := represents_primitiveRec (fun v => beta (v 0) (v 1) (v 2)) betaGraph
      beta_stronglyRepresents hcodes (fun x => f (List.Vector.ofFn x))
      (fun x => g (List.Vector.ofFn x)) φ ψ hφ hψ
    convert hr using 1
    funext x
    simp only [primitiveRecFunction, PrimitiveRecursion.lastRec,
      PrimitiveRecursion.initialPart, List.Vector.get_ofFn, primitiveRec_lastRec]

theorem unary_computable_representable (f : ℕ → ℕ) (hf : Computable f) :
    Representable (fun x : Fin 1 → ℕ => f (x 0)) := by
  obtain ⟨T, hT, hspec, _, _⟩ := MachinesAndComputationHistories.normal_form
    (fun x => Part.some (f x))
    (MachinesAndComputationHistories.unary_recursive_iff.mpr (Partrec.nat_iff.mp hf.partrec))
  let test (v : Fin 2 → ℕ) : ℕ := cond (T (v 0) (v 1)) 0 1
  have htest : Primrec (fun v : PrimitiveRecursion.Args 2 => test v.get) := by
    exact Primrec.cond
      (hT.comp (Primrec.vector_get.comp Primrec.id (Primrec.const 0))
        (Primrec.vector_get.comp Primrec.id (Primrec.const 1)))
      (Primrec.const 0) (Primrec.const 1)
  have hreptest : Representable test := by
    have hget (x : Fin 2 → ℕ) : (List.Vector.ofFn x).get = x := by
      funext i
      exact List.Vector.get_ofFn x i
    simpa only [hget] using
      primitive_recursive_representable _ (Nat.Primrec'.prim_iff.mpr htest)
  obtain ⟨φ, hφ⟩ := hreptest
  have htestzero (x : Fin 1 → ℕ) (w : ℕ) :
      test (Fin.snoc x w) = 0 ↔ T (x 0) w = true := by
    dsimp only [test]
    simp only [show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl,
      Fin.snoc_castSucc, show (1 : Fin 2) = Fin.last 1 from rfl, Fin.snoc_last]
    cases T (x 0) w <;> decide
  have hdom (x : Fin 1 → ℕ) : ∃ w, test (Fin.snoc x w) = 0 := by
    obtain ⟨w, hw, _⟩ := (hspec (x 0) (f (x 0))).mp (Part.mem_some_iff.mpr rfl)
    exact ⟨w, (htestzero x w).mpr hw⟩
  have hsearch := regularSearch_stronglyRepresents test hdom φ hφ
  have hextract : Primrec MachinesAndComputationHistories.extract :=
    Primrec.fst.comp Primrec.unpair
  obtain ⟨ψ, hψ⟩ := primitive_recursive_representable
    (fun v : PrimitiveRecursion.Args 1 => MachinesAndComputationHistories.extract v.head)
    (Nat.Primrec'.prim_iff₁.mpr hextract)
  refine ⟨compositionGraph ψ (fun _ : Fin 1 => graphSearch φ), ?_⟩
  have hr := composition_stronglyRepresents
    (fun x : Fin 1 → ℕ => MachinesAndComputationHistories.extract (x 0))
    (fun _ : Fin 1 => regularSearch test hdom) ψ (fun _ => graphSearch φ)
    (by simpa only [List.Vector.head_ofFn] using hψ) (fun _ => hsearch)
  convert hr using 1
  funext x
  have ht : T (x 0) (regularSearch test hdom x) = true :=
    (htestzero x _).mp (Nat.find_spec (hdom x))
  exact (Part.mem_some_iff.mp
    ((hspec (x 0) (MachinesAndComputationHistories.extract (regularSearch test hdom x))).mpr
      ⟨regularSearch test hdom x, ht, rfl⟩)).symm

theorem computable_representable {n : ℕ} (f : (Fin n → ℕ) → ℕ)
    (hf : Computable (fun x : List.Vector ℕ n => f x.get)) : Representable f := by
  let g (q : ℕ) : ℕ := f ((MachinesAndComputationHistories.tupleUnpack n q).get)
  have hg : Computable g :=
    hf.comp (MachinesAndComputationHistories.tuple_unpack_primrec n).to_comp
  obtain ⟨φ, hφ⟩ := unary_computable_representable g hg
  obtain ⟨ψ, hψ⟩ := primitive_recursive_representable
    (@MachinesAndComputationHistories.tuplePack n)
    (Nat.Primrec'.prim_iff.mpr (MachinesAndComputationHistories.tuple_pack_primrec n))
  refine ⟨compositionGraph φ (fun _ : Fin 1 => ψ), ?_⟩
  have hr := composition_stronglyRepresents (fun x : Fin 1 → ℕ => g (x 0))
    (fun _ : Fin 1 => fun x : Fin n → ℕ =>
      MachinesAndComputationHistories.tuplePack (List.Vector.ofFn x))
    φ (fun _ => ψ) hφ (fun _ => hψ)
  convert hr using 1
  funext x
  simp only [g, MachinesAndComputationHistories.tuple_unpack_pack]
  congr 1
  funext i
  exact (List.Vector.get_ofFn x i).symm

end
end Lemmatheca.MathematicalLogic.ArithmeticRepresentability
