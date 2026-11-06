import natural_numbers
import functions
import plus_comm
import succ_inj


private def f : ℕ × ℕ → ℕ 
| ⟨ a, b ⟩ => a + b


example : surjective f := by
  sorry
