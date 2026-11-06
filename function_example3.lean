import natural_numbers
import functions
import plus_comm
import succ_inj

private def g : ℕ → ℕ 
| a => 1 + a

example : injective g := by
  sorry
