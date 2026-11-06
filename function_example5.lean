import natural_numbers 
import functions
import succ_inj
import times_comm
import times_one
import plus_zero
import plus_comm
import zero_not_succ
import division_algorithm
import one_times

def Evens := { x : ℕ // x % 2 = 0 }
def Odds := { x : ℕ // x % 2 = 1 }

def f ( x : ℕ ) : ℕ := 2 * x

private theorem double_has_remainder_0_by_2 ( n : ℕ ) 
: ( n * 2 ) % 2 = 0 := by
  sorry

private theorem remainder_0_by_2_then_2_divides ( n : ℕ )
: n % 2 = 0 → ∃ (m:ℕ), n = m*2 := by
  sorry

def g ( n : ℕ ) : Evens := sorry

example : surjective g := by
  sorry

def i ( y : Evens ) : ℕ := y.val

example : ¬ surjective i := by
  sorry

private theorem f_eq_ig : f = i ∘ g := by
  sorry

private theorem not_2_divides_1 ( z : ℕ )
: 2*z ≠ 1 := by
  sorry

open Classical
example : ¬ surjective f := by
  sorry
