import data.real.basic
import data.real.irrational

namespace problem13

open real (sqrt)

example (a b c : ℝ) : a / 0 = 0 := div_zero a

-- I'm going to skip this for now

theorem sqrt3Irrational : irrational (sqrt 3) := by {
  rintros ⟨⟨num, denom, denomPos, hCoprimes⟩, hEq⟩,
  replace hEq : _^2 = (sqrt 3)^2 := congr_fun (congr_arg pow hEq) 2,
  rw [<-rat.cast_pow, real.sqr_sqrt (show 0 ≤ (3:real), by norm_num)] at hEq,

  rw [pow_two, rat.num_denom', rat.mk_eq_div, div_mul_div, <-pow_two, <-pow_two] at hEq,
  push_cast at hEq,
  rw div_eq_iff sorry at hEq,
  have h1 : sqrt ((num:real)^2) = sqrt (3* denom^2) := congr_arg sqrt hEq,
  rw [real.sqrt_mul sorry, real.sqrt_sqr sorry, real.sqrt_sqr sorry] at h1,

  -- rw [pow_two, rat.num_denom', rat.mul_def (ne.symm $ ne_of_lt $ nat.cast_lt.mpr denomPos) (ne.symm $ ne_of_lt $ nat.cast_lt.mpr denomPos)] at hEq,
  sorry
}

end problem13
