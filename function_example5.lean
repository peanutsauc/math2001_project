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
import parity
import even_plus_even_is_even
import zero_plus

def Evens := { x : ℕ // x % 2 = 0 }
def Odds := { x : ℕ // x % 2 = 1 }

def f ( x : ℕ ) : ℕ := 2 * x


private theorem double_has_remainder_0_by_2 ( n : ℕ )
: ( n * 2 ) % 2 = 0 := by
  induction n
  case zero =>
    unfold times
    unfold remainder
    rfl
  case succ n ih =>
    unfold times
    change is_even (n*2) at ih
    have h1: is_even 2 := by rfl
    have h2 := even_plus_even_is_even 2 (n*2)
    have h3 := h2 (And.intro h1 ih)
    exact h3


private theorem remainder_0_by_2_then_2_divides ( n : ℕ )
: n % 2 = 0 → ∃ (m:ℕ), n = m*2 := by
  intro even_n
  have h1 := division_algorithm 2 n
  rw [even_n] at h1
  cases h1 with
  | intro q h =>
    rw [plus_comm] at h
    change n = q * 2 at h
    apply Exists.intro q
    exact h




-- this function should be the same as f, but with codomain Evens instead of ℕ
def g ( n : ℕ ) : Evens := ⟨ n*2, double_has_remainder_0_by_2 n ⟩

example : surjective g := by
  unfold surjective
  intro x
  cases x with
  | mk nx px =>
    have h1 := (remainder_0_by_2_then_2_divides nx) px
    cases h1 with
    | intro m pm =>
      apply Exists.intro m
      apply Subtype.ext
      change m*2 = nx
      exact pm.symm



/- this should be the function that takes an even number to the underlying
natural number; it justs forgets the proof that the number was even -/
def i ( y : Evens ) : ℕ := y.val


example : ¬ surjective i := by
  intro surji
  unfold surjective at surji
  have h1 := surji 1
  cases h1 with
  | intro even1 i1_is_1 =>
    change even1.val=1 at i1_is_1
    cases even1 with
    | mk ℕ_1 h2 =>
      change ℕ_1=1 at i1_is_1
      rw [i1_is_1] at h2
      contradiction

private theorem f_eq_ig : f = i ∘ g := by
  funext x
  unfold compose
  change f x = i (⟨ x*2, double_has_remainder_0_by_2 x ⟩)
  change 2 * x = x * 2
  exact times_comm 2 x



private theorem not_2_divides_1 ( z : ℕ )
: 2*z ≠ 1 := by
  rw [times_comm 2 z]
  intro eq
  have h := double_has_remainder_0_by_2 z
  have odd1 : 1 % 2 = 1 := by rfl
  have eq2 : (z * 2) % 2 = 1 % 2 := congrArg (fun x => x % 2) eq
  rw [h] at eq2
  rw [odd1] at eq2
  contradiction


example : ¬ surjective f := by
  intro surjf
  unfold surjective at surjf
  have h1 := surjf 1
  change ∃ y, 2*y = 1 at h1
  cases h1 with
  | intro y h2 =>
    have h3 := not_2_divides_1 y
    contradiction
