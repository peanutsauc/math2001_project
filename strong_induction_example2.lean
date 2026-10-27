import natural_numbers
import strong_induction
import fibonacci
import remainders_by_3
import odd_iff_not_even
import even_plus_odd_is_odd
import odd_plus_odd_is_even
import odd_plus_even_is_odd
import lt_succ
import lt_is_le


local notation "F" => Fibonacci

private theorem trichotomy ( n : ℕ )
: ( n = 0 ) ∨ ( n = 1 ) ∨ ( ∃ (m:ℕ), n = m.succ.succ )
:= by
  sorry



example ( n : ℕ )
: ( n % 3 ) = 0 ↔ ( F n % 2 ) = 0
:= by
  induction n using strong_induction
  case ih n ih =>
  rcases trichotomy n with h|h|h
    --n=0
    rewrite [h]
    decide
