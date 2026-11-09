import Lemmatheca.EffectivelyClosedClassesAndDnc.ClosedClasses
import Lemmatheca.ComputableTreesAndPaths.Separator

/-! Total diagonal avoidance, its finite prohibitions, and the exact separator convention. -/
namespace Lemmatheca.ComputabilityTheory.EffectivelyClosedClassesAndDnc

open ComputableTreesAndPaths IncomparableTuringDegrees PostsTheorem
open UniversalComputation EffectiveEnumerations ComputableSeparation

noncomputable section

def DNC (f : ℕ → ℕ) : Prop := ∀ e y, y ∈ phi e e → f e ≠ y

def binaryDNCClass : Set (Set ℕ) := {X | DNC (indicator (fun e => e ∈ X))}

theorem dnc_not_computable (f : ℕ → ℕ) (hf : DNC f) : ¬ Computable f := by
  intro hc
  obtain ⟨j, hj⟩ := phi_complete (Partrec.nat_iff.mp hc.partrec)
  exact hf j (f j) (by rw [hj]; exact Part.mem_some_iff.mpr rfl) rfl

theorem binary_dnc_not_computable (X : Set ℕ) (hX : X ∈ binaryDNCClass) :
    ¬ ComputablePred (fun e => e ∈ X) := by
  intro hc
  obtain ⟨f, hf, he⟩ := (decidable_iff_characteristic (fun e => e ∈ X)).mp hc
  exact dnc_not_computable _ hX (hf.of_eq he)

def diagonalForbidden : Set ℕ :=
  {u | ValidCode u ∧ ∃ e < wordLength u, wordBit u e ∈ phi e e}

def diagonalCheck (u c : ℕ) : Bool := by
  classical
  exact decide (ValidCode u ∧ c.unpair.1 < wordLength u ∧
    boundedValue c.unpair.2 c.unpair.1 c.unpair.1 = wordBit u c.unpair.1 + 1)

def diagonalSearch (u : ℕ) : Part ℕ :=
  (Nat.rfind fun c => Part.some (diagonalCheck u c)).map (fun _ => 0)

theorem diagonal_check_primitive :
    Primrec (fun p : ℕ × ℕ => diagonalCheck p.1 p.2) := by
  classical
  have he : Primrec (fun p : ℕ × ℕ => p.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hk : Primrec (fun p : ℕ × ℕ => p.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hb : Primrec (fun p : ℕ × ℕ =>
      boundedValue p.2.unpair.2 p.2.unpair.1 p.2.unpair.1) :=
    boundedValue_primitive.comp ((hk.pair he).pair he)
  have hp : PrimrecPred (fun p : ℕ × ℕ =>
      ValidCode p.1 ∧ p.2.unpair.1 < wordLength p.1 ∧
      boundedValue p.2.unpair.2 p.2.unpair.1 p.2.unpair.1 = wordBit p.1 p.2.unpair.1 + 1) :=
    (valid_code_primitive.comp Primrec.fst).and
      ((Primrec.nat_lt.comp he (FiniteSequenceCoding.primrec_length.comp Primrec.fst)).and
        (Primrec.eq.comp hb (Primrec.succ.comp (beta_primitive.comp Primrec.fst he))))
  exact hp.decide

theorem diagonal_search_recursive : Nat.Partrec diagonalSearch := by
  have hc : Computable₂ diagonalCheck := diagonal_check_primitive.to_comp
  exact Partrec.nat_iff.mp ((Partrec.rfind hc.partrec₂).map (Computable.const 0).to₂)

theorem diagonal_search_domain (u : ℕ) :
    (diagonalSearch u).Dom ↔ u ∈ diagonalForbidden := by
  classical
  simp only [diagonalSearch, Part.map_Dom]
  constructor
  · intro hd
    obtain ⟨c, hc, _⟩ := Nat.rfind_dom.mp hd
    have h : ValidCode u ∧ c.unpair.1 < wordLength u ∧
        boundedValue c.unpair.2 c.unpair.1 c.unpair.1 = wordBit u c.unpair.1 + 1 := by
      have hcheck : diagonalCheck u c = true := (Part.mem_some_iff.mp hc).symm
      simpa only [diagonalCheck, decide_eq_true_eq] using hcheck
    exact ⟨h.1, c.unpair.1, h.2.1, (phi_output _ _ _).mpr ⟨c.unpair.2, h.2.2⟩⟩
  · rintro ⟨hu, e, he, hy⟩
    obtain ⟨k, hk⟩ := (phi_output _ _ _).mp hy
    apply Nat.rfind_dom.mpr
    exact ⟨Nat.pair e k, by simp [diagonalCheck, hu, he, hk], fun _ => trivial⟩

def diagonalRecognizerCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp diagonal_search_recursive)

def diagonalRecognizerIndex : ℕ := Encodable.encode diagonalRecognizerCode

theorem diagonal_recognizer_eval (u : ℕ) :
    phi diagonalRecognizerIndex u = diagonalSearch u := by
  have he := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp diagonal_search_recursive)) u
  simpa only [phi, diagonalRecognizerIndex, diagonalRecognizerCode,
    Denumerable.ofNat_encode] using he

theorem diagonal_recognizer_domain : indexSet diagonalRecognizerIndex = diagonalForbidden := by
  ext u
  change (phi diagonalRecognizerIndex u).Dom ↔ _
  rw [diagonal_recognizer_eval, diagonal_search_domain]

theorem diagonal_forbidden_family : ForbiddenFamily diagonalForbidden := by
  exact ⟨fun _ h => h.1,
    (Partrec.nat_iff.mpr diagonal_search_recursive).dom_re.of_eq diagonal_search_domain⟩

theorem binary_dnc_closed :
    avoidance diagonalForbidden = binaryDNCClass ∧ EffectivelyClosed binaryDNCClass := by
  have he : avoidance diagonalForbidden = binaryDNCClass := by
    ext X
    constructor
    · intro hX e y hy heq
      apply hX (e + 1)
      refine ⟨prefix_code_valid X (e + 1), e, ?_, ?_⟩
      · rw [show wordLength (prefixCode X (e + 1)) = e + 1 from
          (prefixCode_spec X (e + 1)).1]
        omega
      · have hb : wordBit (prefixCode X (e + 1)) e =
            indicator (fun q => q ∈ X) e := (prefixCode_spec X (e + 1)).2 e (by omega)
        rw [hb, heq]
        exact hy
    · intro hX n hn
      obtain ⟨_, e, he, hy⟩ := hn
      have hen : e < n := by simpa only [(prefixCode_spec X n).1] using he
      exact hX e (wordBit (prefixCode X n) e) hy ((prefixCode_spec X n).2 e hen).symm
  exact ⟨he, diagonalForbidden, diagonal_forbidden_family, he⟩

theorem dnc_iff_separator (X : Set ℕ) :
    X ∈ binaryDNCClass ↔ Separator (diagonalOutput 0) (diagonalOutput 1) X := by
  classical
  constructor
  · intro hX
    constructor
    · intro e he
      by_contra hn
      have h := hX e 0 he
      simp [indicator, hn] at h
    · apply Set.disjoint_left.mpr
      intro e hx he
      have h := hX e 1 he
      simp [indicator, hx] at h
  · intro hs e y hy he
    by_cases hx : e ∈ X
    · have hey : y = 1 := by simpa [indicator, hx] using he.symm
      rw [hey] at hy
      exact Set.disjoint_left.mp hs.2 hx hy
    · have hey : y = 0 := by simpa [indicator, hx] using he.symm
      rw [hey] at hy
      exact hx (hs.1 hy)

theorem dnc_separator_tree : binaryDNCClass = {X | Path kleeneTree X} := by
  ext X
  rw [dnc_iff_separator]
  change Separator (diagonalOutput 0) (diagonalOutput 1) X ↔
    Path (separatorTree diagonalAIndex diagonalBIndex) X
  rw [paths_are_separators, diagonal_indices.1, diagonal_indices.2]

theorem nonbinary_diagonal_unconstrained (e y b : ℕ) (hy : 2 ≤ y)
    (hb : b = 0 ∨ b = 1) :
    b ≠ y ∧ (y ∈ phi e e → e ∉ diagonalOutput 0 ∧ e ∉ diagonalOutput 1) := by
  refine ⟨by omega, ?_⟩
  intro hout
  constructor
  · intro h0
    have he := Part.mem_unique hout h0
    omega
  · intro h1
    have he := Part.mem_unique hout h1
    omega

end
end Lemmatheca.ComputabilityTheory.EffectivelyClosedClassesAndDnc
