import Lemmatheca.ExactPairsAndFailureOfMeets.Checker

/-! One fixed oracle checker and the actual protected-prefix least-search decoder. -/
namespace Lemmatheca.ComputabilityTheory.ExactPairs
open OracleComputation OracleProgramNumberings UniversalComputation IncomparableTuringDegrees
open PartialRecursiveFunctions (Args)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
local instance exactPairsSearchDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable

/-- Numerical total-query functions are tested only at positions in protected columns. -/
def SearchTest (q : ℕ → ℕ) (s e u x w : ℕ) : Prop :=
  Prefix u w ∧ 0 < certificateValue w e x ∧
    ∀ j < wordLength w, wordLength u ≤ j → j.unpair.1 < s → wordBit w j = q j

def checkFamily (q : ℕ → ℕ) (v : Args 5) : ℕ :=
  if SearchTest q (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4) then 0 else 1

theorem check_family_primitive : UniformPrimitive checkFamily := by
  convert checkFamily_primitive_helper using 1
  funext q v
  simp only [checkFamily, SearchTest]
  split <;> rfl

/-- Chosen once, before the oracle and all five numerical parameters vary. -/
def checkKernel : Code := Classical.choose (uniform_primitive_program check_family_primitive)

/-- Input (x,w) is repacked as the tuple (s,e,u,x,w). -/
def checkCode (s e u : ℕ) : Code :=
  .comp checkKernel (.pair (constantCode s) (.pair (constantCode e) (.pair (constantCode u)
    (.pair .left (.pair .right .zero)))))

def outputValue (z : ℕ) : ℕ :=
  certificateValue z.unpair.2.unpair.2 z.unpair.1 z.unpair.2.unpair.1 - 1

theorem output_value_primitive : Nat.Primrec outputValue := by
  have hr := Primrec.snd.comp Primrec.unpair
  have hv := IncomparableTuringDegrees.certificate_primitive.comp
    (((Primrec.snd.comp (Primrec.unpair.comp hr)).pair
      (Primrec.fst.comp Primrec.unpair)).pair
      (Primrec.fst.comp (Primrec.unpair.comp hr)))
  exact Primrec.nat_iff.mp (Primrec.nat_sub.comp hv (Primrec.const 1))

def outputKernel : Code := embed (ordinaryCode outputValue output_value_primitive)

/-- Native find' searches w from zero, retaining x for the certificate decoder. -/
def searchCode (s e u : ℕ) : Code :=
  .comp outputKernel (.pair (constantCode e)
    (.pair identityCode (.comp (.find' (checkCode s e u)) (.pair identityCode .zero))))

def SearchCandidate (Q : Set ℕ) (s e u x w : ℕ) : Prop :=
  SearchTest (indicator (fun j => j ∈ Q)) s e u x w

def searchPartial (Q : Set ℕ) (s e u x : ℕ) : Part ℕ :=
  (Nat.rfind (fun w => Part.some (decide (SearchCandidate Q s e u x w)))).map
    (fun w => certificateValue w e x - 1)

theorem check_code_eval (Q : Set ℕ) (s e u x w : ℕ) :
    eval Q (checkCode s e u) (Nat.pair x w) =
      Part.some (if SearchCandidate Q s e u x w then 0 else 1) := by
  have hk := (Classical.choose_spec (uniform_primitive_program check_family_primitive)).2
    Q (List.Vector.ofFn (![s,e,u,x,w] : Fin 5 → ℕ))
  have hp : eval Q (.pair (constantCode s) (.pair (constantCode e) (.pair (constantCode u)
      (.pair .left (.pair .right .zero))))) (Nat.pair x w) =
      Part.some (Nat.pair s (Nat.pair e (Nat.pair u (Nat.pair x (Nat.pair w 0))))) := by
    simp [eval, constant_eval, Nat.unpair_pair]
  change (eval Q _ _).bind (eval Q checkKernel) = _
  rw [hp, Part.bind_some]
  simpa [MachinesAndComputationHistories.tuplePack, checkKernel, checkFamily,
    SearchCandidate] using hk

theorem search_index_primitive :
    Primrec (fun z : ℕ × ℕ × ℕ => encodeCode (searchCode z.1 z.2.1 z.2.2)) := by
  have hc : Primrec (fun z : ℕ × ℕ × ℕ => encodeCode (checkCode z.1 z.2.1 z.2.2)) :=
    compIndex_primitive.comp (Primrec.const (encodeCode checkKernel))
      (pairIndex_primitive.comp (constantIndex_primitive.comp Primrec.fst)
        (pairIndex_primitive.comp (constantIndex_primitive.comp (Primrec.fst.comp Primrec.snd))
          (pairIndex_primitive.comp (constantIndex_primitive.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.const (encodeCode (.pair .left (.pair .right .zero)))))))
  exact compIndex_primitive.comp (Primrec.const (encodeCode outputKernel))
    (pairIndex_primitive.comp (constantIndex_primitive.comp (Primrec.fst.comp Primrec.snd))
      (pairIndex_primitive.comp (Primrec.const (encodeCode identityCode))
        (compIndex_primitive.comp (findIndex_primitive.comp hc)
          (Primrec.const (encodeCode (.pair identityCode .zero))))))

theorem search_code_eval (Q : Set ℕ) (s e u x : ℕ) :
    eval Q (searchCode s e u) x = searchPartial Q s e u x := by
  have hs : eval Q (.find' (checkCode s e u)) (Nat.pair x 0) =
      Nat.rfind (fun w => Part.some (decide (SearchCandidate Q s e u x w))) := by
    rw [eval]
    simp only [Nat.unpair_pair, Nat.add_zero, check_code_eval, Part.map_some]
    change (Nat.rfind (fun w => Part.some
      (decide ((if SearchCandidate Q s e u x w then 0 else 1) = 0)))).map (fun w => w) = _
    rw [Part.map_id' (fun _ => rfl)]
    congr 1
    funext w
    by_cases h : SearchCandidate Q s e u x w <;> simp [h]
  have hp : eval Q (.pair (constantCode e)
      (.pair identityCode (.comp (.find' (checkCode s e u)) (.pair identityCode .zero)))) x =
      (eval Q (.find' (checkCode s e u)) (Nat.pair x 0)).map
        (fun w => Nat.pair e (Nat.pair x w)) := by
    simp only [eval, constant_eval, identity_eval, Part.bind_some, Part.map_some,
      Part.map_map]
    rfl
  change (eval Q _ x).bind (eval Q outputKernel) = _
  rw [hp, hs, Part.bind_map]
  simp only [outputKernel, eval_embed, ordinaryCode_eval, outputValue, Nat.unpair_pair, searchPartial,
    Part.bind_some_eq_map]

theorem search_result_certificate (Q : Set ℕ) (s e u x y : ℕ)
    (hy : y ∈ searchPartial Q s e u x) :
    ∃ w, SearchCandidate Q s e u x w ∧ certificateValue w e x = y + 1 ∧
      ∀ z < w, ¬ SearchCandidate Q s e u x z := by
  obtain ⟨w, hw, heq⟩ := (Part.mem_map_iff _).mp hy
  have hg : SearchCandidate Q s e u x w := by simpa using Nat.rfind_spec hw
  refine ⟨w, hg, ?_, ?_⟩
  · have := hg.2.1
    omega
  · intro z hz
    simpa using Nat.rfind_min hw hz

theorem protected_search_test (A : ℕ → Set ℕ) (s e u x w : ℕ) :
    SearchCandidate (boundedJoin A s) s e u x w ↔
      ProtectedExtension A s u w ∧ 0 < certificateValue w e x := by
  constructor
  · rintro ⟨hp, hv, hh⟩
    refine ⟨⟨hp, fun j hju hjw hjs => ?_⟩, hv⟩
    simpa only [bounded_join_indicator, ite_eq_left hjs] using hh j hjw hju hjs
  · rintro ⟨⟨hp, hh⟩, hv⟩
    refine ⟨hp, hv, fun j hjw hju hjs => ?_⟩
    simpa only [bounded_join_indicator, ite_eq_left hjs] using hh j hju hjw hjs

/-- The same supplied e,f and fixed decoder compute every common total g. -/
theorem no_disagreement_search (A : ℕ → Set ℕ) (s e f u v : ℕ)
    (X Y : Set ℕ) (g : ℕ → ℕ) (hn : ¬ HasDisagreement A s e f u v)
    (hX : ProtectedCompletion A s u X) (hY : ProtectedCompletion A s v Y)
    (he : ∀ x, phi X e x = Part.some (g x)) (hf : ∀ x, phi Y f x = Part.some (g x)) :
    ∀ x, eval (boundedJoin A s) (searchCode s e u) x = Part.some (g x) := by
  intro x
  obtain ⟨w, hw, hwX, hc⟩ := prefix_adequacy X u e x (g x) hX.1
    (by rw [he]; exact Part.mem_some _)
  have hex : ∃ z, SearchCandidate (boundedJoin A s) s e u x z :=
    ⟨w, (protected_search_test A s e u x w).mpr
      ⟨protected_prefix A s u w X hX hw hwX, by rw [hc]; omega⟩⟩
  let z := Nat.find hex
  have hz : SearchCandidate (boundedJoin A s) s e u x z := Nat.find_spec hex
  have hmin : ∀ k < z, ¬ SearchCandidate (boundedJoin A s) s e u x k :=
    fun k hk => Nat.find_min hex hk
  have hr : z ∈ Nat.rfind (fun w => Part.some
      (decide (SearchCandidate (boundedJoin A s) s e u x w))) := by
    exact Nat.mem_rfind.mpr ⟨by simpa using hz, fun {k} hk => by simpa using hmin k hk⟩
  obtain ⟨hzp, hzv⟩ := (protected_search_test A s e u x z).mp hz
  let y := certificateValue z e x - 1
  have hy : certificateValue z e x = y + 1 := by dsimp [y]; omega
  obtain ⟨b, hb, hbY, hbval⟩ := prefix_adequacy Y v f x (g x) hY.1
    (by rw [hf]; exact Part.mem_some _)
  have heq : y = g x := by
    by_contra hne
    apply hn
    refine ⟨Nat.pair x (Nat.pair z b), ?_⟩
    simp only [DisagreementCandidate, Nat.unpair_pair]
    exact ⟨hzp, protected_prefix A s v b Y hY hb hbY, hzv,
      by rw [hbval]; omega, by omega⟩
  rw [search_code_eval]
  apply Part.eq_some_iff.mpr
  change g x ∈ (Nat.rfind _).map _
  rw [← heq]
  exact Part.mem_map _ hr

theorem no_disagreement_relative (A : ℕ → Set ℕ) (s e f u v : ℕ)
    (X Y : Set ℕ) (g : ℕ → ℕ) (hn : ¬ HasDisagreement A s e f u v)
    (hX : ProtectedCompletion A s u X) (hY : ProtectedCompletion A s v Y)
    (he : ∀ x, phi X e x = Part.some (g x)) (hf : ∀ x, phi Y f x = Part.some (g x)) :
    PartialComputable (boundedJoin A s) (fun x => Part.some (g x)) ∧
      PartialComputable (finiteJoin A s) (fun x => Part.some (g x)) := by
  have hcode := no_disagreement_search A s e f u v X Y g hn hX hY he hf
  have hp : PartialComputable (boundedJoin A s) (fun x => Part.some (g x)) :=
    ⟨searchCode s e u, funext hcode⟩
  obtain ⟨c, hc⟩ := (finite_join_presentations A s).1
  refine ⟨hp, subst c (searchCode s e u), ?_⟩
  funext x
  rw [subst_eval (boundedJoin A s) (finiteJoin A s) c hc]
  exact hcode x
end
end Lemmatheca.ComputabilityTheory.ExactPairs
