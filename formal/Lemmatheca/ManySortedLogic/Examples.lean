import Lemmatheca.ManySortedLogic.ManySortedLogic

namespace Lemmatheca.Entry.ManySortedLogic

theorem bad_existential_guard :
    (∃ x : Bool, x = false → False) ∧ ¬(∃ x : Bool, x = false ∧ False) := by
  exact ⟨⟨true,by decide⟩,by simp⟩

end Lemmatheca.Entry.ManySortedLogic
