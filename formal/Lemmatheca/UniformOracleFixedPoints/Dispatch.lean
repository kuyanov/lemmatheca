import Lemmatheca.UniformOracleFixedPoints.Compiler

/-! A common dispatcher from a supplied ordinary program for a computable transformer. -/
namespace Lemmatheca.ComputabilityTheory.UniformOracleFixedPoints

open OracleComputation OracleProgramNumberings

def dispatchInput (F : ℕ → ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.pair (F w.unpair.1 w.unpair.2.unpair.1) w.unpair.2.unpair.2

def IsDispatchCode (F : ℕ → ℕ → ℕ) (c : Nat.Partrec.Code) : Prop :=
  ∀ w, Nat.Partrec.Code.eval c w = Part.some (dispatchInput F w)

theorem dispatch_input_computable {F : ℕ → ℕ → ℕ} (hF : Computable₂ F) :
    Computable (dispatchInput F) := by
  have hn : Computable (fun w : ℕ => w.unpair.1) := Computable.fst.comp Computable.unpair
  have ha : Computable (fun w : ℕ => w.unpair.2.unpair.1) :=
    Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))
  have hx : Computable (fun w : ℕ => w.unpair.2.unpair.2) :=
    Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))
  exact Primrec₂.natPair.to_comp.comp (hF.comp hn ha) hx

theorem dispatch_code_exists {F : ℕ → ℕ → ℕ} (hF : Computable₂ F) :
    ∃ c : Nat.Partrec.Code, IsDispatchCode F c := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (dispatch_input_computable hF).partrec)
  exact ⟨c, fun w => congrFun hc w⟩

noncomputable def dispatchIndex (c : Nat.Partrec.Code) : ℕ :=
  encodeCode (.comp universalCode (embed c))

theorem supplied_dispatcher_eval {F : ℕ → ℕ → ℕ} (c : Nat.Partrec.Code)
    (hc : IsDispatchCode F c) (A : Set ℕ) (n a x : ℕ) :
    phi A (dispatchIndex c) (Nat.pair n (Nat.pair a x)) =
      phi A (F n a) x := by
  change (eval A (decodeCode (dispatchIndex c)) (Nat.pair n (Nat.pair a x))) = _
  rw [dispatchIndex, decode_encode]
  change (eval A (embed c) (Nat.pair n (Nat.pair a x))).bind
    (eval A universalCode) = _
  rw [eval_embed, hc]
  simp only [dispatchInput, Nat.unpair_pair, Part.bind_some]
  exact universal_code_eval A (F n a) x

theorem specified_uniform_selector {F : ℕ → ℕ → ℕ} (c : Nat.Partrec.Code)
    (hc : IsDispatchCode F c) :
    Primrec (compiler (dispatchIndex c)) ∧
      IsAllOracleSelector F (compiler (dispatchIndex c)) := by
  have hh : Primrec (compiler (dispatchIndex c)) :=
    compiler_primitive.comp (Primrec.const _) Primrec.id
  refine ⟨hh, hh.to_comp, ?_⟩
  intro A a x
  exact (compiler_eval A (dispatchIndex c) a x).trans
    (supplied_dispatcher_eval c hc A (compiler (dispatchIndex c) a) a x)

theorem parameterized_recursion {F : ℕ → ℕ → ℕ} (hF : Computable₂ F) :
    ∃ h : ℕ → ℕ, Primrec h ∧ ∀ A : Set ℕ, ∀ a x,
      phi A (h a) x = phi A (F (h a) a) x := by
  obtain ⟨c, hc⟩ := dispatch_code_exists hF
  obtain ⟨hh, _, hs⟩ := specified_uniform_selector c hc
  exact ⟨compiler (dispatchIndex c), hh, hs⟩

theorem recursion {f : ℕ → ℕ} (hf : Computable f) :
    ∃ e : ℕ, ∀ A : Set ℕ, ∀ x, phi A e x = phi A (f e) x := by
  have hF : Computable₂ (fun n (_a : ℕ) => f n) := hf.comp Computable.fst
  obtain ⟨h, _, hs⟩ := parameterized_recursion hF
  exact ⟨h 0, fun A x => hs A 0 x⟩

end Lemmatheca.ComputabilityTheory.UniformOracleFixedPoints
