import odd_plus_is_opposite_parity
import even_plus_odd_is_odd
import plus_comm

theorem remainder_one_is_odd (n : ℕ)
  : n % 2 = 1 → is_odd n := by
  sorry

theorem remainder_zero_is_even (n : ℕ)
  : n % 2 = 0 → is_even n := by
  sorry

theorem remainder_zero_or_one (n : ℕ)
  : n % 2 = 0 ∨ n % 2 = 1 := by
  induction n with
  | zero =>
      apply Or.inl
      rfl
  | succ n ih =>
      cases ih with
      | inl hz =>
          apply Or.inr
          change
            (if (n % 2).succ = 2 then 0
             else (n % 2).succ) = 1
          rw [hz]
          rfl
      | inr ho =>
          apply Or.inl
          change
            (if (n % 2).succ = 2 then 0
             else (n % 2).succ) = 0
          rw [ho]
          rfl

theorem even_succ_remainder_one (n : ℕ)
  : is_even n → n.succ % 2 = 1 := by
  intro hn
  have hc := remainder_zero_or_one n
  cases hc with
  | inl hz =>
      change
        (if (n % 2).succ = 2 then 0
         else (n % 2).succ) = 1
      rw [hz]
      rfl
  | inr ho =>
      have hodd := remainder_one_is_odd n ho
      exact False.elim (hodd hn)

theorem odd_plus_even_is_odd (m n : ℕ)
: is_odd m ∧ is_even n → is_odd (m + n)
:= by
  intro omen
  have hm := omen.left
  have hn := omen.right
  have hopop := odd_plus_is_opposite_parity m n
  have hmn := hopop hm
  have hs := even_succ_remainder_one n hn
  have hsum : (m + n) % 2 = 1 := by
    rw [hmn]
    exact hs
  exact remainder_one_is_odd (m + n) hsum
