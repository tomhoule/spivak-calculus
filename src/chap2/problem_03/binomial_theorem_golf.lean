import algebra.big_operators.basic
import data.nat.choose.basic
import data.polynomial.default
import data.polynomial.monomial

open_locale big_operators
open finset (range)
open nat (choose)
open polynomial (C X)

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

def choose_polynomial (n : ℕ) : polynomial ℕ := {
  to_fun := n.choose,
  support := range (n+1),
  mem_support_to_fun := by {
    intro k, rw [finset.mem_range], split,
    { intro hKLtNSucc, exact (ne_of_gt $ nat.choose_pos (nat.lt_succ_iff.mp hKLtNSucc)) },
    intro hPos, by_contradiction, rw [<-not_le, not_not] at h,
    refine absurd _ hPos,
    exact nat.choose_eq_zero_of_lt (nat.succ_le_iff.mp h)
  }
}

lemma choose_polynomial.zero_eq_one : choose_polynomial 0 = 1 := by {
  ext1,
  unfold choose_polynomial, simp,
  rcases (em $ n = 0) with nZero | nPos,
  { rw nZero, simp },
  obtain ⟨_, h⟩ := nat.exists_eq_succ_of_ne_zero nPos,
  simp only [h, nat.choose_zero_succ],
  have : polynomial.coeff 1 n = 0 := by { rw [<-polynomial.C_1, polynomial.coeff_C], simp only [nPos, if_false]},
  rw [<-h, this]
}

lemma choose_polynomial.coeff_eq (n : ℕ) : (choose_polynomial n).coeff = choose n := by { refl }

--| Binomial theorem special case for 1+x
theorem binomial_theorem' : ∀ (n : ℕ), (1+polynomial.X)^n = choose_polynomial n
| 0 := by { rw pow_zero, rw choose_polynomial.zero_eq_one }
| (n+1) := by {
  let ih := binomial_theorem' n,
  rw [pow_succ, ih, right_distrib, one_mul],
  rw [polynomial.as_sum_support_C_mul_X_pow (choose_polynomial (n+1))],
  rw [polynomial.as_sum_support_C_mul_X_pow (choose_polynomial (n))],
  unfold choose_polynomial, simp only,
  conv_rhs { rw [finset.sum_range_succ'], congr, congr, skip, funext, simp, rw [nat.choose_succ_succ], simp, rw add_mul },
  simp only [mul_one, nat.choose_zero_right, polynomial.coeff_mk, pow_zero],
  conv_rhs { rw [finset.sum_add_distrib, finset.sum_range_succ] },
  conv_lhs { congr, skip, rw [finset.mul_sum, finset.sum_range_succ], congr, skip, congr, skip, funext, rw [mul_comm, mul_assoc, <-pow_succ'] },
  conv_lhs { rw [nat.choose_self, <-add_assoc, add_comm (∑ _ in _, _), mul_comm X, mul_assoc _ (X^_) X, <-pow_succ', polynomial.C_1, one_mul],  },
  rw [finset.sum_range_succ', finset.sum_range_succ],
  simp only [nat.choose_self, mul_one, nat.choose_zero_right, nat.cast_zero, zero_mul, nat.choose_succ_self, zero_add, nat.cast_one,
  ring_hom.eq_nat_cast, pow_zero],
  ring
}
