import natural_numbers
import functions
import plus_comm
import zero_not_succ
import lt_succ
import zero_le
import le_lt_is_lt

def ℕ_pos := { n : ℕ // n > 0 }

private theorem plus_one_gt_zero ( n : ℕ ) 
: n + 1 > 0 := by
  sorry

def f ( n : ℕ ) : ℕ_pos := sorry

private theorem f_surj : surjective f := by
  sorry

def I := { n : ℕ // 1 ≤ n ∧ n ≤ 10 }
def J := { n : ℕ // 2 ≤ n ∧ n ≤ 20 }

private theorem from_I_plus_from_I_in_J ( a b : I )
: 2 ≤ a.val + b.val ∧ a.val + b.val ≤ 20 := by
  sorry

def p ( a : I × I ) : J := sorry 

def g ( x : ℕ_pos ) : ℕ := x.val

def h ( x : ℕ ) : ℕ := 1 + x

private theorem h_eq_gf : h = g ∘ f := by
  sorry

private theorem g_inj : injective g := by
  sorry

private example : ∃ (V:Type) ( p : ℕ → V ) ( i : V → ℕ ), 
i ∘ p = h ∧ surjective p ∧ injective i := by
  sorry
