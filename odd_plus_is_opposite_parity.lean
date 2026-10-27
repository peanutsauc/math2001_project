import parity
import plus_zero
import plus_succ

theorem odd_remainder_one (m : ℕ)
  : is_odd m → m % 2 = 1 := by
  sorry

theorem odd_plus_is_opposite_parity (m n : ℕ)
  : is_odd m → (m + n) % 2 = n.succ % 2 := by
  intro hm
  induction n with
  | zero =>
      rw [plus_zero m]
      change m % 2 = 1
      exact odd_remainder_one m hm

  | succ n ih =>
      rw [plus_succ]
      change
        (if ((m + n) % 2).succ = 2 then 0
         else ((m + n) % 2).succ) =
        (if (n.succ % 2).succ = 2 then 0
         else (n.succ % 2).succ)
      rw [ih]
