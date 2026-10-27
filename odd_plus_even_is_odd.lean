import odd_plus_is_opposite_parity
import even_plus_odd_is_odd
import plus_comm

theorem odd_plus_even_is_odd (m n : ℕ)
: is_odd m ∧ is_even n → is_odd (m + n)
:= by
  intro omen
  have hom := omen.left
  have hen := omen.right
  have hmn := odd_plus_is_opposite_parity m n
  have hmnns := hmn hom
  change remainder (m + n) 2 = remainder n.succ 2 at hmnns
  sorry
