import Lemmatheca.SetTheory.Clubs

namespace Lemmatheca.Entry.ClubsAndStationarySets

open Set Order Cardinal Ordinal Lemmatheca.SetTheory.Clubs

theorem parity_clubs :
    IsClub {n : ℕ | n % 2 = 0} ∧ IsClub {n : ℕ | n % 2 = 1} ∧
    ({n : ℕ | n % 2 = 0} ∩ {n : ℕ | n % 2 = 1}) = ∅ ∧
    (∀ C : Set ℕ, IsOrdinalClosed C) ∧
    ¬ IsClub (diagonalIntersection (fun n : ℕ =>
      if n = 0 then {m | m % 2 = 0} else if n = 1 then {m | m % 2 = 1} else Set.univ)) ∧
    diagonalIntersection (fun n : ℕ =>
      if n = 0 then {m | m % 2 = 0} else if n = 1 then {m | m % 2 = 1} else Set.univ) ⊆ {0, 1} := by
  have hclosed (C : Set ℕ) : IsOrdinalClosed C := by
    intro δ hδ
    exact False.elim (not_isSuccLimit_of_isSuccArchimedean hδ)
  have he : IsClub {n : ℕ | n % 2 = 0} := by
    apply (club_iff _).mpr
    refine ⟨hclosed _, fun n => ⟨2 * (n + 1), ?_, ?_⟩⟩
    · simp
    · omega
  have ho : IsClub {n : ℕ | n % 2 = 1} := by
    apply (club_iff _).mpr
    refine ⟨hclosed _, fun n => ⟨2 * (n + 1) + 1, ?_, ?_⟩⟩
    · simp
    · omega
  have hsub : diagonalIntersection (fun n : ℕ =>
      if n = 0 then {m | m % 2 = 0} else if n = 1 then {m | m % 2 = 1} else Set.univ) ⊆ {0, 1} := by
    intro n hn
    by_cases h : n ≤ 1
    · simp only [mem_insert_iff, mem_singleton_iff]
      omega
    · have hn0 : n % 2 = 0 := by simpa using hn 0 (by omega)
      have hn1 : n % 2 = 1 := by simpa using hn 1 (by omega)
      omega
  refine ⟨he, ho, ?_, hclosed, ?_, hsub⟩
  · ext n
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    omega
  · intro h
    obtain ⟨n, hn, hn2⟩ := h.isCofinal 2
    have := hsub hn
    simp only [mem_insert_iff, mem_singleton_iff] at this
    omega

theorem clubFilter_member_not_closed :
    ∃ A : Set (Carrier (ℵ_ 1)),
      A = {a : Carrier (ℵ_ 1) | (a : Ordinal) < Ordinal.omega0 ∨ Ordinal.omega0 < (a : Ordinal)} ∧
      A ∈ clubFilter (Carrier (ℵ_ 1)) ∧ ¬ IsOrdinalClosed A := by
  classical
  have : Fact (ℵ_ 1).IsRegular := ⟨isRegular_aleph_one⟩
  have hω : omega0 < (ℵ_ 1).ord := by
    simpa only [ord_aleph] using omega0_lt_omega_one
  let δ : Carrier (ℵ_ 1) := ToType.mk ⟨omega0, hω⟩
  have hδ : (δ : Ordinal) = omega0 := by
    change ((ToType.mk.symm (ToType.mk ⟨omega0, hω⟩) : Iio (ℵ_ 1).ord) : Ordinal) = _
    simp
  have hlt (a b : Carrier (ℵ_ 1)) : a < b ↔ (a : Ordinal) < (b : Ordinal) := by
    exact ToType.mk.symm.lt_iff_lt.symm
  have hbetween (β : Carrier (ℵ_ 1)) (hβ : β < δ) :
      ∃ γ : Carrier (ℵ_ 1), β < γ ∧ γ < δ := by
    have hβω : (β : Ordinal) < omega0 := by simpa only [hδ] using (hlt β δ).mp hβ
    obtain ⟨c, hβc, hcω⟩ := isSuccLimit_omega0.lt_iff_nonempty_Ioo.mp hβω
    let γ : Carrier (ℵ_ 1) := ToType.mk ⟨c, hcω.trans hω⟩
    have hγ : (γ : Ordinal) = c := by
      change ((ToType.mk.symm (ToType.mk ⟨c, hcω.trans hω⟩) : Iio (ℵ_ 1).ord) : Ordinal) = _
      simp
    exact ⟨γ, (hlt β γ).mpr (hγ ▸ hβc), (hlt γ δ).mpr (by rw [hγ, hδ]; exact hcω)⟩
  have hδlim : IsSuccLimit δ := by
    constructor
    · let z : Carrier (ℵ_ 1) := ToType.mk ⟨0, omega0_pos.trans hω⟩
      have hz : (z : Ordinal) = 0 := by
        change ((ToType.mk.symm (ToType.mk ⟨0, omega0_pos.trans hω⟩) : Iio (ℵ_ 1).ord) : Ordinal) = _
        simp
      exact ((hlt z δ).mpr (by rw [hz, hδ]; exact omega0_pos)).not_isMin
    · intro β hβ
      obtain ⟨γ, hβγ, hγδ⟩ := hbetween β hβ.lt
      exact hβ.2 hβγ hγδ
  let A : Set (Carrier (ℵ_ 1)) := {a | (a : Ordinal) < omega0 ∨ omega0 < (a : Ordinal)}
  have hcof : ℵ₀ < cof (Carrier (ℵ_ 1)) := by
    simpa only [Carrier, cof_toType, isRegular_aleph_one.cof_ord] using aleph0_lt_aleph_one
  refine ⟨A, rfl, (mem_clubFilter hcof A).mpr ⟨Ioi δ, tail_club δ, ?_⟩, ?_⟩
  · intro a ha
    exact Or.inr (by simpa only [hδ] using (hlt δ a).mp ha)
  · intro hA
    have hmem := hA δ hδlim (fun β hβ => by
      obtain ⟨γ, hβγ, hγδ⟩ := hbetween β hβ
      refine ⟨γ, Or.inl ?_, hβγ, hγδ⟩
      simpa only [hδ] using (hlt γ δ).mp hγδ)
    change (δ : Ordinal) < omega0 ∨ omega0 < (δ : Ordinal) at hmem
    simp only [hδ, lt_self_iff_false, or_self] at hmem

end Lemmatheca.Entry.ClubsAndStationarySets
