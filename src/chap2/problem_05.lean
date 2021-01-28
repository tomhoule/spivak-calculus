import algebra.big_operators.basic
import data.rat.basic
import tactic.linarith

open_locale big_operators
open finset (range)

namespace problem5

theorem a (r : ℚ) (rNotOne : r ≠ 1) : ∀ n, (∑ i in range (n+1), r^i) = (1 - r^(n+1)) / (1 - r)
| 0 := by {
  have : (1 - r) ≠ 0, by { intro h, have : r = 1, by linarith only [h], exact absurd this rNotOne },
  norm_num [this],
}
| (n+1) := by {
  let ih := a n,
  have denomNotZero : (1 - r) ≠ 0, by { intro h, have : r = 1, by linarith only [h], exact absurd this rNotOne },

  rw [finset.sum_range_succ, ih],
  conv_lhs { congr, rw <-(mul_div_cancel_left (r^(n+1)) denomNotZero) },
  conv_lhs {
    rw [div_add_div_same, sub_mul, one_mul],
  },
  norm_num,
  rw <-pow_succ,
}

def S (r : ℚ) (n : ℕ) : ℚ := ∑ i in range (n+1), r^i

lemma SMulR (r : ℚ) (n : ℕ) : S r n * r = ∑ i in range (n+1), r^(i+1) := by {
  unfold S,
  rw [mul_comm, <-finset.sum_hom (range (n+1)) (has_mul.mul r)],
  conv_lhs { congr, skip, funext, rw <-pow_succ },
}

lemma SMulRSubOne (r : ℚ) (n : ℕ) : S r n * (1-r) = (1 - r^(n+1)) := by {
  rw [mul_sub, mul_one],
  rw SMulR r n, unfold S,
  rw <-finset.sum_sub_distrib,
  rw finset.sum_range_sub',
  rw pow_zero
}

theorem b (r : ℚ) (rNotOne : r ≠ 1) (n : ℕ) : S r n = (1 - r^(n+1)) / (1 - r) := by {
  rw <-SMulRSubOne r n,
  have denomNotZero : (1 - r) ≠ 0, by { intro h, have : r = 1, by linarith only [h], exact absurd this rNotOne },
  norm_num [denomNotZero]
}

end problem5
