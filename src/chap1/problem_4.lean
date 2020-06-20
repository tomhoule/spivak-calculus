
import data.rat.basic
import data.real.basic

variables {x : ℤ}

example : (4 - x < 3 - (2*x)) → x < -1 :=
assume h,
have (4 - x < 3 - (x + x)), by rwa [mul_comm, mul_two x] at h,
have 4 < 3 - (x + x) + x, from lt_add_of_sub_right_lt this,
have 4 < 3 + -(x + x) + x, by assumption,
have 4 < 3 + (-x + -x) + x, by rwa [neg_add] at this,
have 4 < 3 + -x, by simpa [add_assoc],
have 4 < 3 - x, by assumption,
have 4 + x < 3, from add_lt_of_lt_sub_right this,
have 4 + x + -4 < 3 + -4, from add_lt_add_right this (-4),
have x < 3 + -4, by simpa [add_comm 4, add_assoc],
show x < -1, by assumption

-- Any x will satisfy this because x^2 is positive by definition.
example : 5 - (x^2) < 8 :=
have 0 ≤ x^2, from pow_two_nonneg x,
have h1 : -(x^2) ≤ 0, from neg_nonpos_of_nonneg this,
have (5 : ℤ) < (8 : ℤ), by simpa,
have -(x^2) + 5 < 8, from add_lt_of_nonpos_of_lt h1 this,
show 5 -(x^2) < 8, by rwa [add_comm] at this

def le_cast_int_to_real : ∀ (a b : ℤ), a < b → (↑a : ℝ) < (↑b : ℝ) :=
assume a b h,
have (↑a : ℚ) < ↑b, from int.cast_lt.elim_right h,
have (↑↑a: ℝ) < ↑↑b, from rat.cast_lt.elim_right this,
show (↑a : ℝ) < ↑b, from by rwa [rat.cast_coe_int, rat.cast_coe_int] at this

def mul_cast_self : ∀ (a : ℤ), (↑(a * a) : ℝ) = (↑a : ℝ) * (↑a : ℝ) := assume a, int.cast_mul a a

-- (iii)
example : 5 - (x^2) < -2 → (real.sqrt (↑7) < abs ↑x) :=
assume h,
have 0 ≤ (7 : ℤ), by simpa,
have sevennonneg : 0 ≤ (↑7 : ℝ), from int.cast_nonneg.elim_right this,
have absx_mul_nonneg : 0 ≤ (abs ↑x : ℝ) * abs ↑x, from (
    have 0 ≤ (abs ↑x : ℝ), from abs_nonneg (↑x),
    mul_nonneg this this
),
have 5 - (x^2) + x^2 < -2 + x^2, from add_lt_add_right h (x^2),
have 5 < -2 + x^2, by simpa,
have 2 + 5 < 2 + (-2 + x^2), from add_lt_add_left this 2,
have 7 < x^2, by simpa,
have 7 < abs x * abs x, by rwa [pow_two, ←abs_mul_abs_self] at this,
have ↑7 < ↑(abs x * abs x), from le_cast_int_to_real 7 (abs x * abs x) this,
have ↑7 < ↑(abs x) * ↑(abs x), by rwa [mul_cast_self (abs x)] at this,
have ↑7 < abs ↑x * abs ↑x, by rwa [int.cast_abs] at this,
have real.sqrt (↑7) < real.sqrt (abs ↑x * abs ↑x), from (iff.elim_right $ real.sqrt_lt sevennonneg absx_mul_nonneg) this,
show real.sqrt (↑7) < abs ↑x, by rwa [real.sqrt_mul_self (abs_nonneg x)] at this
