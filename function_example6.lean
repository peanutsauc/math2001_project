import natural_numbers
import functions
import plus_comm
import zero_not_succ
import lt_succ
import zero_le
import le_lt_is_lt


private theorem plus_one_gt_zero ( n : ℕ ) 
: n + 1 > 0 := by
  sorry



def f ( n : ℕ ) : ℕ_pos := ⟨ n+1, plus_one_gt_zero n ⟩


private theorem f_surj : surjective f := by
  sorry



def g ( x : ℕ_pos ) : ℕ := by
  have ⟨ a, ha ⟩ := x  /- this is how you break a subtype
                          into the underlying element of the
                          ambient set and the proof that it
                          lies in the subset -/
  exact a

-- Here is a shorter way of defining the same g
-- def g ( x : ℕ_pos ) : ℕ := x.val


def h ( x : ℕ ) : ℕ := 1 + x

private theorem h_eq_gf : h = g ∘ f := by
  sorry

private theorem g_inj : injective g := by
  sorry


private example : ∃ (V:Type) ( p : ℕ → V ) ( i : V → ℕ ), 
i ∘ p = h ∧ surjective p ∧ injective i := by
  sorry



  



  

