import Lemmatheca.Combinatorics.Additive.Sumsets
import Lemmatheca.Combinatorics.Additive.FiniteSumsets

/-!
These checks fail the build if the reported axiom dependencies change. They are
checks for the example theorems, not the planned full dependency auditor.
-/

/-- info: 'Lemmatheca.translate_mem_sumset' does not depend on any axioms -/
#guard_msgs in
#print axioms Lemmatheca.translate_mem_sumset

/-- info: 'Lemmatheca.translate_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lemmatheca.translate_injective

/-- info: 'Lemmatheca.example_sumset' does not depend on any axioms -/
#guard_msgs in
#print axioms Lemmatheca.example_sumset

/-- info: 'Lemmatheca.sumset_card_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lemmatheca.sumset_card_lower_bound

/-- info: 'Lemmatheca.triple_sumset_card_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lemmatheca.triple_sumset_card_lower_bound

/-- info: 'Lemmatheca.finite_sumset_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lemmatheca.finite_sumset_nonempty

/-- info: 'Lemmatheca.sumset_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lemmatheca.sumset_zero

/-- info: 'Lemmatheca.triple_sumset_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lemmatheca.triple_sumset_nonempty

/-- info: 'Lemmatheca.sumset_empty_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lemmatheca.sumset_empty_counterexample

/-- info: 'Lemmatheca.triple_sumset_no_strict_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lemmatheca.triple_sumset_no_strict_growth
