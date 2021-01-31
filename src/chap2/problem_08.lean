variables (n : ℕ)

def even : Prop := n % 2 = 0
def odd : Prop := n % 2 = 1

def mod2Decidable : n % 2 = 0 ∨ n % 2 = 1 := nat.mod_two_eq_zero_or_one n

theorem evenIffNotOdd : even n ↔ ¬odd n := by {
  delta even odd,
  split,
  { intros h1 hEqOne,
    have h2 : n % 2 ≠ 0, by { rw hEqOne, exact nat.one_ne_zero },
    exact absurd h1 h2
  },
  intro hNotOdd,
  cases (mod2Decidable n) with h0 h1,
  { exact h0 },
  exact (false.elim $ absurd h1 hNotOdd)
}
