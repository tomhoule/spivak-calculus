import data.real.irrational
import chap2.problem_13

namespace problem14

open real (sqrt)

example (a b c : ℝ) : a = b + c → a - c = b := sub_eq_of_eq_add
example (a b c : ℝ) : a + b = c → a = c - b := eq_sub_of_add_eq
example (a b : ℝ) : a = b → a^2 = b^2 := congr_arg (λ (a : ℝ), a ^ 2)
example (a b c : ℝ) : a ≠ 0 → a * b = c → b = c/a := euclidean_domain.eq_div_of_mul_eq_right

lemma aHelper (a b : ℝ) : (a - b)^2 = a^2 - 2*a*b + b^2 := by linarith

-- Assuming sqrt 2 + sqrt 6 is rational, show that sqrt 6 has to be rational,
-- which is false.
theorem a : irrational (sqrt 2 + sqrt 6) := by {
  delta irrational, simp only [not_exists, set.mem_range],
  rintros ⟨a, b, bPos, _⟩ h,
  replace h := (congr_arg (λ a, a^2) $ sub_eq_of_eq_add h),
  simp only at h,
  rw [real.sqr_sqrt (show (2:real) ≥ 0, by norm_num), aHelper, real.sqr_sqrt (show (6:real) ≥ 0, by norm_num)] at h,
  rw [rat.num_denom', rat.mk_eq_div] at h,
  rcases (em $ a = 0) with aZero | aNonzero,
  { rw aZero at h, simp only [int.cast_zero, zero_div, zero_mul, sub_zero, mul_zero, rat.cast_zero, pow_two, zero_add] at h, have : (6:real) ≠ 2, by norm_num, exact absurd h this },
  have aNeZero : (a:rat) ≠ 0 := int.cast_ne_zero.mpr aNonzero,
  have bNeZero : (b:rat) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_lt bPos).symm,
  have : (a:rat) / (b:int) ≠ 0 := div_ne_zero aNeZero bNeZero,
  push_cast at h,
  have h' : (↑a / ↑b) * sqrt 6 = 2 + ((↑a / ↑b)^2)/2, by nlinarith [h, this],
  clear h,
  replace h' := euclidean_domain.eq_div_of_mul_eq_right (by exact_mod_cast this) h',
  norm_cast at h',
  have h : irrational (sqrt 6) := by exact_mod_cast chap2problem13.sqrt6Irrational,
  unfold irrational at h,
  rw set.mem_range at h,
  have notH : ∃ (y : ℚ), ↑y = sqrt 6 := ⟨_, h'.symm⟩,
  exact absurd notH h
}

theorem b : irrational (sqrt 2 + sqrt 3) := by {
  delta irrational, simp only [not_exists, set.mem_range],
  rintros ⟨a, b, bPos, _⟩ h,
  rw [rat.num_denom', rat.mk_eq_div] at h,
  push_cast at h,
  replace h := (congr_arg (λ a, a^2) $ sub_eq_of_eq_add h),
  simp only at h,
  rw [real.sqr_sqrt (show (2:real) ≥ 0, by norm_num), aHelper, real.sqr_sqrt (show (3:real) ≥ 0, by norm_num)] at h,
  rcases (em $ a = 0) with aZero | aNonzero,
  { rw aZero at h, simp only [int.cast_zero, zero_div, zero_mul, sub_zero, mul_zero, rat.cast_zero, pow_two, zero_add] at h, have : (3:real) ≠ 2, by norm_num, exact absurd h this },
  have aNeZero : (a:rat) ≠ 0 := int.cast_ne_zero.mpr aNonzero,
  have bNeZero : (b:rat) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_lt bPos).symm,
  have : (a:rat) / (b:int) ≠ 0 := div_ne_zero aNeZero bNeZero,
  have h' : (↑a / ↑b) * sqrt 3 = (1 + (↑a / ↑b) ^ 2) / 2, by nlinarith [h, this],
  clear h,
  replace h' := euclidean_domain.eq_div_of_mul_eq_right (by exact_mod_cast this) h',
  norm_cast at h',
  have h : irrational (sqrt 3) := by exact_mod_cast chap2problem13.sqrt3Irrational,
  unfold irrational at h,
  rw set.mem_range at h,
  have notH : ∃ (y : ℚ), ↑y = sqrt 3 := ⟨_, h'.symm⟩,
  exact absurd notH h

}

end problem14
