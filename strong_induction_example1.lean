import natural_numbers
import strong_induction
import times_left_distrib
import lt_succ

private def f : ℕ → ℕ
| 0 => 0
| ℕ.succ n => 2 * ( f n ) + 1


example ( n : ℕ ) : f n + 1 = 2^n := by
  induction n using strong_induction
  case ih n ih=>
  cases n
  case zero =>
    decide
  case succ n =>
    unfold power
    have a : f n + 1 = 2^n := by
      have b := ih n
      apply b
      exact lt_succ n
    rewrite [← a]
    rewrite [times_left_distrib]
    rewrite [f]
    rewrite [show 2*1=2 by decide]
    rewrite [← plus_assoc]
    rewrite [show 1+1=2 by decide]
    rfl

example ( n : ℕ ) : f n + 1 = 2^n := by
  sorry
