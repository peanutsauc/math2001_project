import natural_numbers
import le_trans
import le_refl
import le_zero_is_eq_zero
import le_is_lt_or_eq
import lt_succ_is_le
import lt_le_is_lt

theorem strong_induction { P : (n:ℕ) → Prop } ( ih : ∀ (n:ℕ), ( ∀ (m:ℕ), (m<n) → P m ) → P n )
: ∀ (n:ℕ), P n := by
  have h : ∀ n : ℕ, ∀ m : ℕ, m ≤ n → P m := by
    intro n
    induction n with
    | zero =>
        intro m hm
        have heq := le_zero_is_eq_zero hm
        subst m
        apply ih 0
        intro k hk
        have hk0 : k ≤ 0 := hk.left
        have hkeq := le_zero_is_eq_zero hk0
        exact False.elim (hk.right hkeq)

    | succ n ind =>
        intro m hm
        have hc := le_is_lt_or_eq hm
        cases hc with
        | inl hlt =>
            exact ind m (lt_succ_is_le hlt)
        | inr heq =>
            subst m
            apply ih n.succ
            intro k hk
            exact ind k (lt_succ_is_le hk)

  intro n
  exact h n n (le_refl n)
