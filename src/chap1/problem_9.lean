import data.real.basic
import tactic.basic
import tactic.suggest

open real (sqrt)

def lt_cast_int_to_real : ∀ (a b : ℤ), a < b → (a : ℝ) < (b : ℝ) :=
assume a b h,
have (↑a : ℚ) < ↑b, from int.cast_lt.elim_right h,
have (↑↑a: ℝ) < ↑↑b, from rat.cast_lt.elim_right this,
have (↑a : ℝ) < ↑b, from by rwa [rat.cast_coe_int, rat.cast_coe_int] at this,
by exact this

def le_cast_int_to_real : ∀ (a b : ℤ), a ≤ b → (a : ℝ) ≤ (b : ℝ) :=
assume a b h,
have (↑a : ℚ) ≤ ↑b, from int.cast_le.elim_right h,
have (↑↑a: ℝ) ≤ ↑↑b, from rat.cast_le.elim_right this,
have (↑a : ℝ) ≤ ↑b, from by rwa [rat.cast_coe_int, rat.cast_coe_int] at this,
this


example : abs (sqrt (2 : ℝ) + sqrt 3 - sqrt 5 + sqrt 7) = sqrt 2 + sqrt 3 - sqrt 5 + sqrt 7 :=
have 0 ≤ sqrt (2 : ℝ) + sqrt 3 - sqrt 5 + sqrt 7, from (
    have h1 : sqrt (2 : ℝ) + sqrt 3 - sqrt 5 + sqrt 7 = sqrt 2 + sqrt 3 + -(sqrt 5) + sqrt 7, by reflexivity,
    have h2 : sqrt (2 : ℝ) + sqrt 3 + -sqrt 5 + sqrt 7 = sqrt 2 + sqrt 3 + (-(sqrt 5) + sqrt 7), by rw [add_assoc],
    have two : 0 ≤ sqrt 2, from real.sqrt_nonneg 2,
    have three : 0 ≤ sqrt 3, from real.sqrt_nonneg 3,
    have five : (0 : ℤ) ≤ (5 : ℤ), from sup_eq_left.mp rfl,
    have seven : (0 : ℤ) ≤ (7 : ℤ), from sup_eq_left.mp rfl,
    have left : 0 < (- (sqrt 5) + sqrt 7), from (
        have h : 5 < 7, from nat.lt_of_sub_eq_succ rfl,
        have (5 : ℤ) < 7, by exact nat.cast_lt.mpr h,
        have (↑5 : ℝ) < ↑7, from lt_cast_int_to_real 5 7 this,
        have sqrt ↑5 < sqrt ↑7, from (real.sqrt_lt (le_cast_int_to_real 0 5 five) (le_cast_int_to_real 0 7 seven)).elim_right this,
        have 0 < (sqrt ↑7 - sqrt ↑5), from sub_pos.mpr this,
        have 0 < (sqrt ↑7 + -(sqrt ↑5)), from this,
        have 0 < (-(sqrt ↑5) + sqrt ↑7), by rwa [add_comm] at this,
        by simpa only [nat.cast_bit0, nat.cast_bit1, nat.cast_one]
    ),
    have 0 ≤ sqrt 2 + sqrt 3, from add_nonneg two three,
    have 0 ≤ sqrt 2 + sqrt 3 + (-(sqrt 5) + sqrt 7), from add_nonneg this (le_of_lt left),
    by rwa [h1, h2]
),
abs_of_nonneg this
