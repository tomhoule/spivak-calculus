def completeInductionByInduction (P : ℕ → Prop) :
  P 0 →
  (∀ (k : nat), (∀ i, i ≤ k → P i) → P (k+1)) →
  (∀ (n : ℕ), P n)
:= by {
    intros pZero pLe n,
    have h₁ : ∀ x, x ≤ n → P x := by {
      induction n with n ih,
      { intros x H, rw nat.eq_zero_of_le_zero H, exact pZero },
      intros x xLe,
      cases (lt_or_eq_of_le xLe),
      { have : x ≤ n := nat.le_of_lt_succ h,
        exact ih x this
      },
      rw h, exact pLe n ih
    },
    cases n,
    { exact pZero },
    refine pLe n _,
    intros i iLe,
    have : i ≤ n.succ := nat.le_succ_of_le iLe,
    exact h₁ i this
}
