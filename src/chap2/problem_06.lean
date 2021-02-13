import algebra.big_operators.basic
import data.rat.basic
import tactic.linarith
import ring_theory.power_series.basic
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

theorem sumSquares : ∑ i in range (n+1), (i:rat)^2 = 1/3 * n^3 + 1/2 * n^2 + 1/6 * n := by {
  let h := (eq.symm $ sumSquaresAux3 n),
  rw [finset.sum_add_distrib, finset.sum_add_distrib, <-finset.mul_sum, <-finset.mul_sum] at h,
  rw [sumSquaresAux2 n, sumPow1] at h,
  simp only [mul_one, finset.sum_const, nsmul_eq_mul, finset.card_range, nat.cast_add, nat.cast_one] at h,
  replace h := (symm $ eq_sub_iff_add_eq.mpr $ eq_sub_iff_add_eq.mpr h),
  rw [mul_comm (3:rat) (∑ _ in _, _), <-div_eq_iff threeNonZero] at h,
  replace h := h.symm,
  simp only [sub_div, mul_div_cancel_left _ threeNonZero] at h,
  linarith [h],
}

end problem06Prelude

namespace problem6part1

open problem06Prelude

variables (n: ℕ) (k : ℚ)

lemma sumCubesAux1 : (k + 1)^4 - k^4 = 4*k^3 + 6*k^2 + 4*k + 1 := by linarith

lemma sumCubesAux2 : ∀ n, (∑ i in range (n+1), (((i:rat)+1)^4 - i^4)) = (n+1)^4
| 0 := rfl
| (n+1) := by { rw [finset.sum_range_succ, sumCubesAux2 n], norm_num }

lemma sumCubesAux3 : (∑ i in range (n+1), (((i:rat)+1)^4 - i^4)) = ∑ k in range (n+1), (4*k^3 + 6*k^2 + 4*k + 1) := finset.sum_congr rfl (λ x _, sumCubesAux1 x)

theorem sumCubes : (∑ i in range (n+1), (i:rat)^3) = 1/4*n^4 + 1/2*n^3 + 1/4 * n^2 := by {
  let h := (eq.symm $ sumCubesAux3 n),

  -- Isolate i^3
  simp only [finset.sum_add_distrib, <-eq_sub_iff_add_eq] at h,
  rw [<-finset.mul_sum, mul_comm (4:rat), (eq_div_iff_mul_eq (show (4:rat) ≠ 0, by norm_num)).symm] at h,
  rw h,
  clear h, -- too much noise

  simp only [sumCubesAux2],
  rw [finset.sum_const, finset.card_range, nsmul_eq_mul, mul_one, <-finset.mul_sum, <-finset.mul_sum],
  rw [sumSquares, sumPow1],
  push_cast, ring
}

end problem6part1

namespace problem6part2

open problem06Prelude
open problem6part1

variables (n: ℕ) (k : ℚ)

lemma sumPow4Aux1 : (k + 1)^5 - k^5 = 5*k^4 + 10*k^3 + 10*k^2 + 5*k + 1 := by linarith

lemma sumPow4Aux2 : ∀ n, (∑ i in range (n+1), (((i:rat)+1)^5 - i^5)) = (n+1)^5
| 0 := rfl
| (n+1) := by { rw [finset.sum_range_succ, sumPow4Aux2 n], norm_num }

lemma sumPow4Aux3 : (∑ i in range (n+1), (((i:rat)+1)^5 - i^5)) = ∑ k in range (n+1), (5*k^4 + 10*k^3 + 10*k^2 + 5*k + 1) := finset.sum_congr rfl (λ x _, sumPow4Aux1 x)

theorem sumPow4 : (∑ i in range (n+1), (i:rat)^4) = 1/5 * n^5 + 1/2 * n^4 + 1/3 * n^3 - 1/30 * n := by {
  let h := (eq.symm $ sumPow4Aux3 n),
  simp only [finset.sum_add_distrib, <-eq_sub_iff_add_eq] at h,
  rw [<-finset.mul_sum, mul_comm (5:rat), (eq_div_iff_mul_eq (show (5:rat) ≠ 0, by norm_num)).symm] at h,

  rw h, clear h,

  rw [finset.sum_const, nsmul_eq_mul, finset.card_range, mul_one],

  rw sumPow4Aux2,

  simp only [<-finset.mul_sum, sumCubes, sumSquares, sumPow1],
  push_cast, ring
}

end problem6part2

namespace problem6part3

variables (n: ℕ) (k : ℚ)

def f : ℕ → ℚ := λ n, ite (n=0) (-(n+1)⁻¹) (((n:rat) * (n+1))⁻¹)

lemma fZero : f 0 = -1 := by { unfold f, simp only [if_true, nat.cast_zero, eq_self_iff_true, inv_one, zero_add]}

lemma sumAux1 : ∀ (n:nat), (n:rat)⁻¹ - (n+1)⁻¹ = f n
| 0 := rfl
| (n+1) := by {
  unfold f,
  have h1 : (n:rat) + 1 > 0 := nat.cast_add_one_pos n,
  have h2 : (n:rat) + 1 + 1 > 0 := by { norm_cast, exact (n + 1).succ_pos },
  push_cast,
  rw [inv_sub_inv (ne_of_gt h1) (ne_of_gt h2)],
  norm_num,
  exact one_div ((↑n + 1) * (↑n + 1 + 1))
}

lemma sumAux2 : ∀ n, (∑ i in range (n+1), ((i:rat)⁻¹ - (i+1)⁻¹)) = -(n+1)⁻¹
| 0 := rfl
| (n+1) := by {
  let ih := sumAux2 n,
  rw [finset.sum_range_succ, ih],
  push_cast, ring
}

lemma sumAux3 : ∑ i in range (n+1), ((i:rat)⁻¹ - (i+1)⁻¹) = ∑ i in range (n+1), f i := by {
  refine finset.sum_congr rfl _,
  intros,
  induction x with x xSucc,
  { simp only [fZero, zero_sub, nat.cast_zero, inv_zero, inv_one, zero_add] },
  have : x.succ ≠ 0 := nat.succ_ne_zero x,
  simp only [this, nat.cast_succ, if_false],
  exact sumAux1 (x+1)
}

theorem sum (h : n ≠ 0) : (∑ i in range (n+1), f i) = -(n+1)⁻¹ :=
by rw [<-sumAux3 n, sumAux2 n]

end problem6part3

namespace problem6part4

variables { k : ℚ } { n : ℕ }

def f : ℕ → ℚ := λ n, ite (n=0) (-1) ((2*n+1)/(n^2*(n+1)^2))

lemma sumPreAux (h : n ≠ 0) : ((n:rat)^2)⁻¹ - ((n+1)^2)⁻¹ = f n := by {
  unfold f,
  have : (n:rat) ≠ 0 := nat.cast_ne_zero.mpr h,
  have h1 : (n:rat)^2 ≠ 0 := pow_ne_zero 2 this,
  have : (n:rat) + 1 ≠ 0 := nat.cast_add_one_ne_zero n,
  have : ((n:rat) + 1)^2 ≠ 0 := pow_ne_zero 2 this,
  rw [inv_sub_inv h1 this],
  simp [h],
  conv_lhs { congr, rw [sq_sub_sq], norm_num, ring },
}

lemma sumAux2 : ∀ (n:ℕ), ∑ i in range (n+1), (((i:rat)^2)⁻¹ - ((i+1)^2)⁻¹) = -((n+1)^2)⁻¹
| 0 := rfl
| (n+1) := by {
  let ih := sumAux2 n,
  rw [finset.sum_range_succ, ih],
  push_cast, ring
}

lemma sumAux3 : ∑ i in range (n+1), (((i:rat)^2)⁻¹ - ((i+1)^2)⁻¹) = ∑ i in range (n+1), f i := by {
  refine finset.sum_congr rfl _,
  intros i H, clear H,
  induction i with i iSucc,
  { unfold f, norm_num },
  have : i.succ ≠ 0 := nat.succ_ne_zero i,
  rw [sumPreAux this],
}

theorem sum : ∑ i in range (n+1), f i = -((n+1)^2)⁻¹ :=
by { rw [<-sumAux3, sumAux2 n] }

end problem6part4
