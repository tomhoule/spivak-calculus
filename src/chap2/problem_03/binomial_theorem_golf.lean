import algebra.big_operators.basic
import data.nat.choose.basic
import tactic.zify

open_locale big_operators
open finset (range)
open nat (choose)

variables ( a b : ℕ )

private def f : ℕ → ℕ → ℕ := λ n j, choose n j * a^(n-j) * b^j

private lemma fZero : ∀ (n : ℕ), f a b n 0 = a^n := λ n, by {
  unfold f,
  rw [nat.choose_zero_right, one_mul, pow_zero, mul_one, nat.sub_zero]
}

private lemma fNsucc : ∀ n j, n > j → f a b (n+1) (j+1) = b * f a b n j + a * f a b n (j+1) := by {
  intros _ _ nGtJ,
  unfold f,
  rw [nat.choose_succ_succ, mul_assoc, right_distrib, <-mul_assoc, <-mul_assoc],
  rw [nat.succ_sub_succ n j, pow_succ, <-mul_assoc _ b _, mul_comm _ b, mul_assoc, add_right_inj],
  conv_rhs { rw [<-mul_assoc a _ _, <-mul_assoc a _ _, mul_comm a, mul_assoc _ a _, <-pow_succ a] },
  have : (n - (j+1)) + 1 = n - j, by { rw [nat.sub_succ], apply nat.succ_pred_eq_of_pos, exact nat.sub_pos_of_lt nGtJ },
  rw this
}

private lemma fNsucc' : ∀ n j, j ∈ range n → f a b (n+1) (j+1) = b * f a b n j + a * f a b n (j+1) := by
{ intros _ _ h, exact fNsucc a b n j (finset.mem_range.mp h) }


private lemma fSelf : ∀ (n : ℕ), f a b n n = b^n := λ n, by {
  unfold f,
  rw [nat.choose_self, one_mul, nat.sub_self, pow_zero, one_mul]
}

private lemma fSumMul : ∀ (n x : ℕ), x * ∑ j in range (n+1), f a b n j = ∑ j in range (n+1), x * (f a b n j) := by {
  intros,
  apply (symm $ finset.sum_hom _ (λ x', x * x'))
}

private theorem binomial_theorem_impl : ∀ (n : ℕ), (a + b)^n = ∑ j in range (n+1), f a b n j
| 0 := rfl
| (n+1) := by {
  let ih := binomial_theorem_impl n,
  rw [pow_succ, ih, right_distrib],
  conv_rhs { rw [finset.sum_range_succ', fZero], congr, rw [finset.sum_range_succ, finset.sum_congr (show range n = range n, from rfl) (fNsucc' a b n), add_comm] },
  rw [finset.sum_add_distrib, add_comm (a * _) (b * _), fSumMul a b _ b],

  conv_lhs { congr, rw [finset.sum_range_succ, add_comm] },

  simp only [add_assoc, add_right_inj],

  rw [fSumMul a b n a, finset.sum_range_succ', add_comm],

  simp only [add_assoc, add_right_inj, fSelf, fZero, pow_succ],
  ac_refl
}

theorem binomial_theorem : ∀ (n : ℕ), (a + b)^n = ∑ j in range (n+1), choose n j * a^(n-j) * b^j := by
{ intros, let out := binomial_theorem_impl a b n, unfold f at out, exact out }
