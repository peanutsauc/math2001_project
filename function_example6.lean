import natural_numbers
import functions
import plus_comm
import zero_not_succ
import lt_succ
import zero_le
import le_lt_is_lt

private theorem succ_is_plus_one ( n : ℕ )
: n.succ = n + 1 := by
  have h1 : n + 1 = (n + 0).succ := plus_succ n 0
  have h2 : n + 0 = n := plus_zero n
  rewrite [h2] at h1
  exact h1.symm


private theorem plus_one_gt_zero ( n : ℕ )
: n + 1 > 0 := by
  have h1 := zero_le n
  have h2 := lt_succ n
  have h3 := succ_is_plus_one n
  rw [h3] at h2
  have h4 := le_lt_is_lt h1 h2
  exact h4


def f ( n : ℕ ) : ℕ_pos :=
  ⟨n + 1, plus_one_gt_zero n⟩


private theorem f_surj : surjective f := by
  unfold surjective
  intro sn
  cases sn with
  | mk sn hn =>
    cases sn with
    | zero =>
      unfold lt at hn
      have h2 := hn.right
      contradiction
    | succ n =>
      apply Exists.intro n
      apply Subtype.ext
      change n + 1 = n.succ
      exact (succ_is_plus_one n).symm


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
  funext n
  unfold compose
  change 1 + n = n + 1
  exact plus_comm 1 n


private theorem g_inj : injective g := by
  unfold injective
  intro a b hgab
  apply Subtype.ext
  change a.val = b.val at hgab
  exact hgab


private example : ∃ (V:Type) ( p : ℕ → V ) ( i : V → ℕ ),
i ∘ p = h ∧ surjective p ∧ injective i := by
  apply Exists.intro ℕ_pos
  apply Exists.intro f
  apply Exists.intro g
  have h1 := And.intro f_surj g_inj
  have h2 := And.intro h_eq_gf.symm h1
  exact h2
