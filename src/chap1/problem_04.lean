
import data.real.basic
import data.real.pi

open real (pi)

variables {x : ℤ}

example : (4 - x < 3 - (2*x)) → x < -1 :=
assume h,
have (4 - x < 3 - (x + x)), by rwa [mul_comm, mul_two x] at h,
have 4 < 3 - (x + x) + x, from lt_add_of_sub_right_lt this,
have 4 < 3 + -(x + x) + x, by assumption,
have 4 < 3 + (-x + -x) + x, by rwa [neg_add] at this,
have 4 < 3 + -x, by simpa only [add_assoc, add_zero, add_left_neg],
have 4 < 3 - x, by assumption,
have 4 + x < 3, from add_lt_of_lt_sub_right this,
have 4 + x + -4 < 3 + -4, from add_lt_add_right this (-4),
have x < 3 + -4, by simpa only [add_assoc, add_add_neg_cancel'_right],
show x < -1, by assumption

-- Any x will satisfy this because x^2 is non-negative by definition.
example : 5 - (x^2) < 8 :=
have 0 ≤ x^2, from pow_two_nonneg x,
have h1 : -(x^2) ≤ 0, from neg_nonpos_of_nonneg this,
have (5 : ℤ) < (8 : ℤ), by simpa only [],
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
have 0 ≤ (7 : ℤ), by simpa only [],
have sevennonneg : 0 ≤ (↑7 : ℝ), from int.cast_nonneg.elim_right this,
have absx_mul_nonneg : 0 ≤ (abs ↑x : ℝ) * abs ↑x, from (
    have 0 ≤ (abs ↑x : ℝ), from abs_nonneg (↑x),
    mul_nonneg this this
),
have 5 - (x^2) + x^2 < -2 + x^2, from add_lt_add_right h (x^2),
have 5 < -2 + x^2, by simpa only [sub_add_cancel],
have 2 + 5 < 2 + (-2 + x^2), from add_lt_add_left this 2,
have 7 < x^2, by simpa only [add_neg_cancel_left],
have 7 < abs x * abs x, by rwa [pow_two, ←abs_mul_abs_self] at this,
have ↑7 < ↑(abs x * abs x), from le_cast_int_to_real 7 (abs x * abs x) this,
have ↑7 < ↑(abs x) * ↑(abs x), by rwa [mul_cast_self (abs x)] at this,
have ↑7 < abs ↑x * abs ↑x, by rwa [int.cast_abs] at this,
have real.sqrt (↑7) < real.sqrt (abs ↑x * abs ↑x), from (iff.elim_right $ real.sqrt_lt sevennonneg absx_mul_nonneg) this,
show real.sqrt (↑7) < abs ↑x, by rwa [real.sqrt_mul_self (abs_nonneg x)] at this

-- (iv)
example : 0 < (x - 1) * (x - 3) → 3 < x ∨ x < 3 :=
assume h,
have (0 < x - 1 ∧ 0 < x - 3) ∨ (x - 1 < 0 ∧ x - 3 < 0), from pos_and_pos_or_neg_and_neg_of_mul_pos h,
or.elim this
    (λ ⟨xm1pos, xm3pos⟩,
        -- 0 < x-1 only tells us x is at least 2, so we ignore it.
        have 0 + 3 < x - 3 + 3, from add_lt_add_right xm3pos 3,
        have 3 < x + -3 + 3, by assumption,
        have 3 < x + 0, by rwa [add_assoc] at this,
        or.inl $ show 3 < x, by rwa [add_zero] at this
    )
    (λ ⟨xm1neg, xm3neg⟩,
        -- x-1 < 0 only tells us x is less than 1, so we ignore it.
        have x - 3 + 3 < 0 + 3, from add_lt_add_right xm3neg 3,
        have x + -3 + 3 < 3, by rwa [zero_add] at this,
        have x + (-3 + 3) < 3, by rwa [add_assoc] at this,
        or.inr $ show x < 3, by rwa [neg_add_self, add_zero] at this
    )

-- (v)
example : 0 < x^2 - 2*x + 2 :=
have factorized : x^2 - 2*x + 2 = (x - 1)^2 + 1, from eq.symm $ calc
    (x - 1)^2 + 1   = (x-1) * (x-1) + 1 : by rw pow_two
                ... = (x+-1) * (x+-1) + 1 : rfl
                ... = x * x + -1 * x + (x+-1) * (-1) + 1 : by rw [mul_add, add_mul]
                ... = x^2 + -x + (x+-1) * (-1) + 1 : by rw [pow_two, neg_one_mul]
                ... = x^2 + -x + (x * -1 + -1 * -1) + 1 : by rw [add_mul]
                ... = x^2 + -x + (-x + 1) + 1 : by rw [mul_neg_one, neg_one_mul (-(1 : ℤ)), neg_neg]
                ... = x^2 + (-x + -x) + (1 + 1) : by simp [add_assoc]
                ... = x^2 + (-x)*2 + (1+1) : by rw [mul_two (-x)]
                ... = x^2 + -(x*2) + (1+1) : by rw [neg_mul_eq_neg_mul]
                ... = x^2 - (x*2) + 2 : rfl
                ... = x^2 - 2*x + 2 : by rw [mul_comm],
have h1 : 0 ≤ (x-1)^2, from pow_two_nonneg (x-1),
have h2 : (x-1)^2 < (x-1)^2 + 1, from int.lt_succ ((x-1)^2),
have h3 : 0 < (x-1)^2 + 1, from lt_of_le_of_lt h1 h2,
show 0 < (x^2) - 2*x + 2, by rwa [factorized]

open real (sqrt)

-- (vi)
example (x: ℝ) : 2 < x^2 + x + 1 → x > (sqrt 5 - 1) / 2 ∨ x < -(sqrt 5 + 1) / 2 :=
assume h,
have l1 : 0 < x^2 + x - 1, by linarith only [h],
have l2 : (-(1 : ℝ)/2)^2 = 1/4, by ring,
have (x + 1/2)^2 = x^2 + x + 1/4, by ring,
have lr : 5/4 < (x + 1/2)^2, by linarith only [l1, this],
have sqrtFour : sqrt 4 = 2, from (real.sqrt_eq_iff_mul_self_eq (show (0 : real) <= 4, by norm_num) (show (0 : real) <= 2, by norm_num)).elim_right (show 2*2 = (4 : real), by norm_num),
have lNonneg : (0 : ℝ) ≤ 5/4, by norm_num,
have rNonneg : 0 ≤ (x + 1/2)^2, from pow_two_nonneg _,
have sqrt (5 / 4) < sqrt ((x + 1/2)^2) , by rwa [<-(real.sqrt_lt lNonneg rNonneg)] at lr,
have sqrt 5 / sqrt 4 < abs (x+1/2), by rwa [<-real.sqrt_div (show (0 : ℝ) ≤ 5, by norm_num) 4, <-real.sqrt_sqr_eq_abs],
have sqrt 5 / 2 < abs (x+1/2), by rwa [sqrtFour] at this,
or.elim (le_or_gt 0 (x + 1/2))
    (λ hNonneg,
        have sqrt 5 / 2 < x + 1/2, by rwa [abs_of_nonneg hNonneg] at this,
        or.inl $ by linarith only [this]
    )
    (λ hNeg,
        have sqrt 5 / 2 < -(x + 1/2), by rwa [abs_of_neg hNeg] at this,
        or.inr $ by linarith only [this]
    )

def complete_the_square : ∀ (a n m : ℤ), a^2 + (n + m) * a + n * m = (a + m) * (a + n) :=
assume a n m,
calc
a^2+(n+m)*a+n*m = a*a + (n+m)*a + n*m : by rw pow_two
            ... = a*a + a*n + a*m + n*m : by ring
            ... = a * (a + n) + (a + n) * m : by ring
            ... = (a + m) * (a + n) : by ring

-- (vii)
example : 16 < x^2 - x + 10 → (3 < x ∨ x < -2) :=
assume h,
have 16 - 16 < x^2 - x + 10 - 16, from sub_lt_sub_right h 16,
have 16 - 16 < x^2 + -x + 10 + -16, by assumption,
have checkpoint : 0 < x^2 + -x + -6, by rwa [add_assoc] at this,
have helper : x^2 + (-3 + 2) * x + (-3) * 2 = x^2 + -x + -6, by ring,
have factored : 0 < (x + 2) * (x - 3), by rwa [←helper, complete_the_square x (-3) 2] at checkpoint,
or.elim (decidable.le_or_lt 0 (x + 2))
    (λ (h : 0 ≤ x+2),
        have 0 < x-3, from pos_of_mul_pos_left factored h,
        or.inl $ show 3 < x, by simpa only [sub_pos]
    )
    (λ (h : x + 2 < 0),
        have x + 2 - 2 < 0 -2, from sub_lt_sub_right h 2,
        have x + 0 < -2, by rwa [add_sub_assoc] at this,
        have x < -2, by rwa [add_zero] at this,
        or.inr $ this
    )

-- (viii)

example (x : ℝ) : 0 < x^2 + x + 1 :=
or.elim (le_or_gt 0 x)
    (λ xNonneg,
        have 0 ≤ x^2, from pow_two_nonneg x,
        have 0 ≤ x^2 + x, from add_nonneg this xNonneg,
        show 0 < x^2 + x + 1, from lt_add_of_le_of_pos this zero_lt_one
    )
    (λ xNeg,
        or.elim (lt_or_ge (-1) x)
            (λ xGtNegOne,
                have h1 : 0 < x + 1, by linarith [xGtNegOne],
                have h2 : 0 ≤ x^2, from pow_two_nonneg x,
                suffices 0 < x^2 + (x + 1), by rwa [add_assoc],
                lt_add_of_le_of_pos h2 h1
            )
            (λ (xLtNegOne : x ≤ -1),
                have h1 : 0 ≤ -x, by linarith only [xLtNegOne],
                have 1 ≤ -x, from le_neg.mp xLtNegOne,
                have -x ≤ -x * -x, from le_mul_of_one_le_left h1 this,
                have 0 ≤ x^2 + x, by linarith only [this],
                lt_add_of_le_of_pos this zero_lt_one
            )
    )

-- (ix)

example (x : ℝ) : 0 < (x - pi) * (x + 5) * (x - 3) → pi < x :=
assume h,
have left : 0 < (x - pi) → pi < x, from assume h, by linarith only [h],
have middle : 0 < (x + 5) → -5 < x, from assume h, by linarith only [h],
have right : 0 < x - 3 → 3 < x, from assume h, by linarith only [h],
by begin
    rcases (lt_trichotomy 0 (x - pi)) with leftPos | leftZero | leftNeg,
    all_goals { rcases (lt_trichotomy 0 (x + 5)) with middlePos | middleZero | middleNeg },
    all_goals { rcases (lt_trichotomy 0 (x - 3)) with rightPos | rightZero | rightNeg },
    any_goals { have lhsPos : 0 < (x - pi) * (x+5), by linarith },
    any_goals { have lhsNeg : 0 > (x - pi) * (x+5), by linarith },
    any_goals { have lhsZero : 0 = (x - pi) * (x+5), by linarith },
    any_goals { specialize left leftPos },
    any_goals { specialize right rightPos },
    any_goals { specialize middle middlePos },
    -- Weed out the zero cases.
    all_goals { try {
        have : (x - pi) * (x + 5) * (x - 3) = 0, by linarith,
        have : ¬ 0 < (x - pi) * (x + 5) * (x - 3), from sorry,
        exact (false.elim $ absurd h this)
    } },
    -- Weed out the negative cases.
    any_goals {
        have : (x - pi) * (x + 5) * (x - 3) < 0, by linarith,
        sorry
        -- have : ¬ 0 < (x - pi) * (x + 5) * (x - 3), from sorry,
        -- exact absurd h this
    },
    -- any_goals { assumption },
    sorry,
    sorry,
    sorry
end
