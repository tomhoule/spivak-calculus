import data.nat.basic
import tactic.linarith
import data.real.sqrt

namespace chap2problem16

open real (sqrt)

example (a b : ℝ) : abs a < b → a^2 < b^2 := sqr_lt_sqr
example (a b : ℝ) (h1 : 0 < a) (h2 : 0 < b) : a < b → b⁻¹ < a⁻¹ := λ h3, (inv_lt_inv h2 h1).mpr h3
example (a b c : ℝ) : a + b < c → a < c - b := lt_sub_iff_add_lt.mpr
example (a b c : ℝ) (h : 0 < c) : a < b → a * c < b * c := (mul_lt_mul_right h).mpr
example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := add_pow_two a b
example (a b c : ℝ) : a/b * c = (a*c) / b := div_mul_eq_mul_div c a b
example (a b c : ℝ) (h1 : 0 < a) (h2 : 0 < b) (h3 : 0 < c) : a * c < b * c → a < b := (mul_lt_mul_right h3).mp

theorem a (m n : ℕ) (nPos : 0 < n) (hSq : (m:ℝ)^2 / n^2 < 2) : ((m:ℝ)+2*n)^2 / (m+n)^2 > 2 := by {
  have nSqPosReal : 0 < (n:real)^2 := by exact_mod_cast (pow_pos nPos 2),
  replace hSq : m^2 < 2*n^2 := by {
    rw [<-mul_lt_mul_right nSqPosReal, div_mul_cancel (_^2) (ne_of_gt nSqPosReal)] at hSq,
    exact_mod_cast hSq
  },
  rcases m,
  { norm_cast, norm_num, rw [mul_pow, pow_two, mul_div_assoc, div_self (ne_of_gt nSqPosReal)], norm_cast, linarith },
  have denomPos : (((m.succ):real) + n) > 0 := by exact_mod_cast add_pos (nat.succ_pos m) nPos,
  have denomSqPos : (((m.succ):real) + n)^2 > 0 := pow_pos denomPos 2,

  -- Simplify by multiplying both sides by the denominator.
  rw [gt_iff_lt, <-mul_lt_mul_right denomSqPos, div_mul_cancel ((_+_)^2) (ne_of_gt denomSqPos)],
  norm_cast,
  linarith [hSq]
}

theorem aMoreover (m n : ℕ) (mPos : 0 < m) (nPos : 0 < n) (hSq : (m:ℝ)^2 / n^2 < 2) : (((m:ℝ)+2*n)^2) / (m+n)^2 - 2 < 2 - (m^2/n^2) := by {
  have mPosReal : 0 < (m:ℝ) := nat.cast_pos.mpr mPos,
  have nPosReal : 0 < (n:ℝ) := nat.cast_pos.mpr nPos,
  have nSqPosReal : 0 < (n:real)^2 := by exact_mod_cast (pow_pos nPos 2),
  have denomPos : (((m):real) + n) > 0 := by exact_mod_cast add_pos mPos nPos,
  have denomSqPos : (((m):real) + n)^2 > 0 := pow_pos denomPos 2,
  replace hSq : (m:ℝ)^2 < 2*n^2 := by {
    rw [<-mul_lt_mul_right nSqPosReal, div_mul_cancel (_^2) (ne_of_gt nSqPosReal)] at hSq,
    exact hSq,
  },

  rw [div_sub' _ (2:real) _ (ne_of_gt denomSqPos)],
  rw [sub_div' _ (2:real) _ (ne_of_gt nSqPosReal)],
  rw [<-mul_lt_mul_right nSqPosReal, div_mul_cancel (_-_) (ne_of_gt nSqPosReal)],
  rw div_mul_eq_mul_div,
  rw [<-mul_lt_mul_right denomSqPos, div_mul_cancel _ (ne_of_gt denomSqPos)],
  push_cast,
  simp only [mul_sub, sub_mul, mul_add, add_mul],
  ring,
  rw add_lt_add_iff_right,
  simp only [pow_succ, neg_mul_eq_neg_mul, pow_zero, mul_one, <-mul_assoc],
  rw [mul_lt_mul_right (mPosReal), <-add_lt_add_iff_right ((n:real) * n * m)],
  norm_num,
  ring,
  simp only [neg_mul_eq_neg_mul, sub_mul, mul_sub, add_mul, mul_add],

  have : -(m:real) * ↑m * ↑m - 2 * ↑n * ↑m * ↑m = -m^2 * (m + 2*n) := by linarith,
  rw this,
  rw [<-add_lt_add_iff_left ((m:real)^2 * (m + 2*n)), add_assoc],
  norm_num,

  have : (2:real) * ↑n ^ 2 * ↑m + 4 * ↑n ^ 3 = 2*n^2 * (m + 2*n) := by linarith,
  rw this,

  have : 0 < (m:real) + 2*n, by linarith [mPosReal, nPosReal],
  rw mul_lt_mul_right this,

  exact hSq
}

theorem b (m n : ℕ) (nPos : 0 < n) (mPos : 0 < m) (hSq : (m:ℝ)^2 / n^2 > 2) : ((m:ℝ)+2*n)^2 / (m+n)^2 < 2 := by {
  rw gt_iff_lt at hSq,
  have nSqPosReal : 0 < (n:real)^2 := by exact_mod_cast (pow_pos nPos 2),
  replace hSq : 2 * n^2 < m^2 := by {
    rw [<-mul_lt_mul_right nSqPosReal, div_mul_cancel (_^2) (ne_of_gt nSqPosReal)] at hSq,
    exact_mod_cast hSq
  },
  have denomPos : ((m:real) + n) > 0 := by exact_mod_cast add_pos mPos nPos,
  have denomSqPos : ((m:real) + n)^2 > 0 := pow_pos denomPos 2,
  rw [<-mul_lt_mul_right denomSqPos, div_mul_cancel ((_+_)^2) (ne_of_gt denomSqPos)],
  norm_cast,
  linarith [hSq]
}

theorem bMoreover (m n : ℕ) (mPos : 0 < m) (nPos : 0 < n) (hSq : (m:ℝ)^2 / n^2 > 2) : (((m:ℝ)+2*n)^2) / (m+n)^2 - 2 > 2 - (m^2/n^2) := by {
  rw gt_iff_lt at hSq, rw gt_iff_lt,
  have mPosReal : 0 < (m:ℝ) := nat.cast_pos.mpr mPos,
  have nPosReal : 0 < (n:ℝ) := nat.cast_pos.mpr nPos,
  have nSqPosReal : 0 < (n:real)^2 := by exact_mod_cast (pow_pos nPos 2),
  have denomPos : (((m):real) + n) > 0 := by exact_mod_cast add_pos mPos nPos,
  have denomSqPos : (((m):real) + n)^2 > 0 := pow_pos denomPos 2,
  replace hSq : 2 * (n:real)^2 < m^2 := by {
    rw [<-mul_lt_mul_right nSqPosReal, div_mul_cancel (_^2) (ne_of_gt nSqPosReal)] at hSq,
    exact_mod_cast hSq
  },

  rw [div_sub' _ (2:real) _ (ne_of_gt denomSqPos), sub_div' _ (2:real) _ (ne_of_gt nSqPosReal)],
  rw [<-mul_lt_mul_right nSqPosReal, div_mul_cancel (_-_) (ne_of_gt nSqPosReal)],
  rw div_mul_eq_mul_div,
  rw [<-mul_lt_mul_right denomSqPos, div_mul_cancel _ (ne_of_gt denomSqPos)],

  have left : (2 * (n:real)^2 - m^2) * (m + n) ^ 2 = 2 * n^2 * (m^2 + 2*m*n) - m^2 * (m^2 + 2*m*n) + (-m^2 * n^2 + 2*n^4) := by linarith,
  have right :  (((m:real) + 2 * n)^2 - (m+n)^2 * 2) * n^2 = 0 + (-m^2 * n^2 + 2*n^4) := by linarith,
  rw [left, right, add_lt_add_iff_right (-(m:real)^2 * n^2 + 2*n^4)],
  clear left right,
  rw [sub_eq_add_neg, <-lt_neg_iff_add_neg, neg_neg],

  have : 0 < (m:real) ^ 2 + 2 * ↑m * ↑n := by {
    apply add_pos,
    { exact pow_pos mPosReal 2},
    have : 0 < (2:real), by norm_num,
    apply mul_pos,
    { apply mul_pos, exact this, exact mPosReal },
    exact nPosReal
  },
  rw mul_lt_mul_right this,

  exact hSq
}

lemma mnHelper (m n : ℕ) (nPos : 0 < n): (m:real)^2 / n^2 < 2 ↔ (m:real)/n < sqrt 2 := by {
  rw <-div_pow,
  split; rcases m,
  { intro h, norm_num,
  },
  { intro h,
    have divPos : (m.succ:real) / n > 0, by {
      refine div_pos_iff.mpr (or.inl _),
      split, exact nat.cast_pos.mpr (nat.succ_pos m), exact nat.cast_pos.mpr nPos
    },
    rw [<-(real.sqrt_sqr (le_of_lt divPos)), real.sqrt_lt (le_of_lt $ pow_pos divPos 2)],
    exact h
  },
  { intro h, norm_num
  },
  intro h,
  have divPos : (m.succ:real) / n > 0, by {
    refine div_pos_iff.mpr (or.inl _),
    split, exact nat.cast_pos.mpr (nat.succ_pos m), exact nat.cast_pos.mpr nPos
  },
  rw [<-real.sqrt_lt (le_of_lt $ pow_pos divPos 2), real.sqrt_sqr (le_of_lt divPos)],
  exact h
}

theorem c (m n : ℕ) (h₁ : (m:real) / n < sqrt 2) (nPos : 0 < n) : ∃ (m' n' : ℕ), (m:ℝ) / n < m' / n' ∧ (m':real) / n' < sqrt 2 := by {
  let i := (m:ℝ)^2/n^2,
  let j := ((m:ℝ)+2*n)^2 / (m+n)^2,
  let k := (((m:ℝ)+2*n) + 2*(m+n))^2 / (m+2*n+(m+n))^2,

  rcases (le_or_gt m 0) with mNonpos | mPos,
  { existsi 1,
    existsi 2,
    have : m = 0 := nat.eq_zero_of_le_zero mNonpos,
    rw this,
    split,
    { norm_num },
    rw <-mnHelper 1 2 zero_lt_two,
    norm_num
  },

  have mPosReal : (0:ℝ) < m := nat.cast_pos.mpr mPos,
  have nPosReal : (0:ℝ) < n := nat.cast_pos.mpr nPos,
  have iPos : 0 < i := div_pos (pow_pos mPosReal 2) (pow_pos nPosReal 2),
  have sumPos : 0 < m + n := add_pos mPos nPos,
  have mAddTwoNPos : 0 < m + 2*n := by linarith,

  have h1 : i < 2 := (mnHelper m n nPos).mpr h₁,
  have h2 : 2 < ((m:ℝ)+2*n)^2 / (m+n)^2 := a m n nPos h1,
  have h2' : 2 < j := h2,
  have h2Moreover : j - 2 < 2 - i := aMoreover m n mPos nPos h1,
  have h3 : (((m+2*n):real)+2*(m+n))^2 / (m+2*n+(m+n))^2 < 2 := by exact_mod_cast b (m+2*n) (m+n) sumPos mAddTwoNPos (by exact_mod_cast h2),
  have h3' : k < 2 := h3,
  have h3Moreover : 2 - (((m + 2 * n):real) ^ 2) / ↑((m + n) ^ 2) < ↑((m + 2 * n + 2 * (m + n)) ^ 2) / ↑((m + 2 * n + (m + n)) ^ 2) - 2 := by exact_mod_cast bMoreover (m+2*n) (m+n) mAddTwoNPos sumPos (by exact_mod_cast h2),
  have h3Moreover' : 2 - j < k - 2 := by { simp only [nat.cast_bit0, nat.cast_add, nat.cast_one, nat.cast_mul, nat.cast_pow] at h3Moreover, exact h3Moreover },
  existsi (m+2*n + 2*(m+n)),
  existsi (m+2*n + (m+n)),
  split,
  {
    have h4 : (((m:ℝ)+2*n)^2) / (m+n)^2 - 2 < 2 - (m^2/n^2) := by exact_mod_cast aMoreover m n mPos nPos h1,
    have h5 : (((m+2*n):real)+2*(m+n))^2 / (((m+2*n):real)+(m+n))^2 - 2 > 2 - (((m:ℝ)+2*n)^2) / (m+n)^2 := by exact_mod_cast bMoreover (m+2*n) (m+n) mAddTwoNPos sumPos (by exact_mod_cast gt_iff_lt.mpr h2),
    suffices : i < k, by {
      simp only [nat.cast_bit0, nat.cast_add, nat.cast_one, nat.cast_mul],
      nth_rewrite_lhs 0 <-real.sqrt_sqr (le_of_lt mPosReal),
      nth_rewrite_lhs 0 <-real.sqrt_sqr (le_of_lt nPosReal),
      rw <-real.sqrt_div (le_of_lt (pow_pos mPosReal 2)),
      have o : 0 < ((m:ℝ) + 2 * n + 2 * (m + n)) := by linarith,
      have o' : 0 ≤ ((m:ℝ) + 2 * n + (m + n)) := by linarith,
      rw [<-real.sqrt_sqr (le_of_lt o), <-real.sqrt_sqr o', <-real.sqrt_div (pow_nonneg (le_of_lt o) 2)],
      exact (real.sqrt_lt (le_of_lt iPos)).mpr this,
    },
    linarith
  },
  rw [<-mnHelper _ _ (show 0 < m + 2 * n + (m + n), by linarith)], exact_mod_cast h3
}


end chap2problem16
