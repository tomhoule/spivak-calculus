import algebra.big_operators.basic
import data.rat.basic
import tactic.linarith
import ring_theory.power_series
import chap2.problem_03.binomial_theorem_golf

open_locale big_operators
open finset (range)

namespace problem06Prelude

variables (n: ℕ) (k : ℚ)

lemma sumPow1Aux1 : (k + 1)^2 - k^2 = 2*k + 1 := by linarith

lemma sumPow1Aux2 : ∀ n, (∑ i in range (n+1), (((i:ℚ)+1)^2 - i^2)) = (n+1)^2
| 0 := rfl
| (n+1) := by {
  let ih := sumPow1Aux2 n,
  rw [finset.sum_range_succ, ih],
  norm_num
}

lemma sumPow1Aux3 : (∑ i in range (n+1), (((i:ℚ)+1)^2 - i^2)) = ∑ i in range (n+1), (2*i + 1) := finset.sum_congr rfl (λ x _, sumPow1Aux1 x)

lemma sumPow1 : ∑ i in range (n+1), (↑i:ℚ) = ((n+1)^2 - (n+1))/2 := by {
  let h := sumPow1Aux3 n,
  rw [finset.sum_add_distrib, <-finset.mul_sum] at h,
  rw [sumPow1Aux2 n, <-sub_eq_iff_eq_add] at h,
  simp only [mul_one, finset.sum_const, nsmul_eq_mul, finset.card_range] at h,
  rw [mul_comm (2:rat), <-div_eq_iff (show (2:rat) ≠ 0, by norm_num)] at h,
  exact h.symm
}

lemma sumSquaresAux1 : (k + 1)^3 - k^3 = 3*k^2 + 3*k + 1 := by linarith

lemma sumSquaresAux2 : ∀ n, (∑ i in range (n+1), (((i:rat)+1)^3 - i^3)) = (n+1)^3
| 0 := rfl
| (n+1) := by {
  let ih := sumSquaresAux2 n,
  rw [finset.sum_range_succ, ih],
  norm_num
}

lemma sumSquaresAux3 : (∑ i in range (n+1), (((i:ℚ)+1)^3 - i^3)) = ∑ i in range (n+1), (3*i^2 + 3*i + 1) := finset.sum_congr rfl (λ x _, sumSquaresAux1 x)

example (a b c : ℚ) : a + b = c ↔ a = c - b := eq_sub_iff_add_eq.symm
example (a b c : ℚ) (h : a ≠ 0) : (a * b) / a = b := mul_div_cancel_left b h

lemma threeNonZero : (3:rat) ≠ 0 := by norm_num

lemma sumSquares : ∑ i in range (n+1), (i:rat)^2 = ((1 / 3 * ↑n + 1 / 2) * ↑n + 1 / 6) * ↑n := by {
  let h := (eq.symm $ sumSquaresAux3 n),
  rw [finset.sum_add_distrib, finset.sum_add_distrib, <-finset.mul_sum, <-finset.mul_sum] at h,
  rw [sumSquaresAux2 n, sumPow1] at h,
  simp only [mul_one, finset.sum_const, nsmul_eq_mul, finset.card_range, nat.cast_add, nat.cast_one] at h,
  replace h := (symm $ eq_sub_iff_add_eq.mpr $ eq_sub_iff_add_eq.mpr h),
  rw [mul_comm (3:rat) (∑ _ in _, _), <-div_eq_iff threeNonZero] at h,
  replace h := h.symm,
  simp [sub_div, mul_div_cancel_left _ threeNonZero] at h,
  ring at h,
  exact h
}

end problem06Prelude

namespace problem6part1

variables (n: ℕ) (k : ℚ)

lemma sumCubesAux1 : (k + 1)^4 - k^4 = (k+1)^3 + 3*k^3 + 3*k^2 + k := by linarith

end problem6part1
