import Lemmatheca.InaccessibleCardinals.WellOrders

namespace Lemmatheca.Entry.InaccessibleCardinals
universe u

theorem first_uncountable_not_strong_limit :
    ¬Cardinal.IsStrongLimit (Cardinal.aleph (1 : Ordinal.{u}))  := by
  intro h
  have hh := h.isSuccLimit
  rw [← Cardinal.succ_aleph0] at hh
  exact Order.not_isSuccLimit_succ _ hh

end Lemmatheca.Entry.InaccessibleCardinals
