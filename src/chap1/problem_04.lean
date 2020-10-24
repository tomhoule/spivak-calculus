
import data.real.basic
import data.real.pi
import analysis.special_functions.pow

open real (pi)

variables {x : ℤ}

example : (4 - x < 3 - (2*x)) ↔ x < -1 :=
iff.intro
(
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

)
(assume h, by linarith only [h])

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

example (x : ℝ) : 0 < (x - pi) * (x + 5) * (x - 3) → pi < x ∨ (-5 < x ∧ x < 3) :=
assume h,
have leftP : 0 < (x - pi) → pi < x, from assume h, by linarith only [h],
have middleP : 0 < (x + 5) → -5 < x, from assume h, by linarith only [h],
have rightP : 0 < x - 3 → 3 < x, from assume h, by linarith only [h],
have leftN : 0 > (x - pi) → pi > x, from assume h, by linarith only [h],
have middleN : 0 > (x + 5) → -5 > x, from assume h, by linarith only [h],
have rightN : 0 > x - 3 → 3 > x, from assume h, by linarith only [h],
by begin
    rcases (lt_trichotomy 0 (x - pi)) with leftPos | leftZero | leftNeg;
    rcases (lt_trichotomy 0 (x + 5)) with middlePos | middleZero | middleNeg;
    rcases (lt_trichotomy 0 (x - 3)) with rightPos | rightZero | rightNeg,
    -- Eliminate the zero cases
    any_goals {
        have hZero : 0 = (x - pi) * (x + 5) * (x - 3), by rw [<-rightZero, mul_zero] <|> rw [<-leftZero, zero_mul, zero_mul] <|> rw [<-middleZero, mul_zero, zero_mul],
        have : ¬ (0: ℝ) < 0, from lt_irrefl 0,
        have : ¬ 0 < (x - pi) * (x + 5) * (x - 3), by {
            conv at this in (_ < _) {
                to_rhs,
                rw hZero
            },
            assumption
        },
        exact (false.elim $ absurd h this)
    },
    -- Eliminate the negative cases
    any_goals {
        have hNeg : (x - pi) * (x + 5) * (x - 3) < 0, by linarith <|>
            simp only [mul_pos_of_neg_of_neg, mul_neg_of_pos_of_neg, leftNeg, middleNeg, rightNeg] <|>
            simp only [mul_pos, mul_neg_of_pos_of_neg, leftPos, middlePos, rightNeg] <|>
            simp only [mul_pos, mul_neg_of_pos_of_neg, leftPos, middlePos, rightNeg] <|>
            simp only [mul_neg_of_neg_of_pos, leftNeg, middlePos, rightPos],
        have : ¬ 0 < (x - pi) * (x + 5) * (x - 3), by exact asymm hNeg,
        exact (false.elim $ absurd h this)
    },
    all_goals {
        try { specialize leftP leftPos },
        try { specialize middleP middlePos },
        try { specialize rightP rightPos },
        try { specialize leftN leftNeg },
        try { specialize middleN middleNeg },
        try { specialize rightN rightNeg },
    },
    any_goals { left, linarith },
    right, constructor, assumption'
end

-- (x)

open real (rpow)

example (x : ℝ) : 0 < (x - rpow 2 (1/3)) * (x - rpow 2 (1/2)) → x < rpow 2 (1/3) \/ x > rpow 2 (1/2) :=
assume h,
have (1: ℝ)/3 < 1/2, by norm_num,
have h1 : rpow 2 (1/3) < rpow 2 (1/2), from real.rpow_lt_rpow_of_exponent_lt one_lt_two this,
or.elim3 (lt_trichotomy x (rpow 2 (1/3)))
    (λ xLt,
        or.elim3 (lt_trichotomy x (rpow 2 (1/2)))
            (λ xLt2, or.inl xLt)
            (λ xEq,
                have x - rpow 2 (1/2) = 0, from sub_eq_zero.mpr xEq,
                -- Zero case
                have h1 : 0 = (x - rpow 2 (1/3)) * (x - rpow 2 (1/2)), from eq.symm $ by rw [this, mul_zero],
                have ¬ (0: ℝ) < 0, from lt_irrefl 0,
                have ¬ 0 < (x - rpow 2 (1/3)) * (x - rpow 2 (1/2)), by {
                    conv at this {
                        congr,
                        to_rhs,
                        rw h1
                    },
                    assumption
                },
                false.elim $ absurd h this
            )
            -- Negative case
            (λ xGt,
                have h1 : 0 < (x - rpow 2 (1/3)), by linarith,
                have 0 > (x - rpow 2 (1/2)), by linarith,
                have 0 > (x - rpow 2 (1/3)) * (x - rpow 2 (1/2)), from linarith.mul_neg this h1,
                have ¬ 0 < (x - rpow 2 (1/3)) * (x - rpow 2 (1/2)), from asymm this,
                false.elim $ absurd h this
            )
    )
    (λ xEq,
        have x - rpow 2 (1/3) = 0, from sub_eq_zero.mpr xEq,
        -- Zero case
        have h1 : 0 = (x - rpow 2 (1/3)) * (x - rpow 2 (1/2)), from eq.symm $ by rw [this, zero_mul],
        have ¬ (0: ℝ) < 0, from lt_irrefl 0,
        have ¬ 0 < (x - rpow 2 (1/3)) * (x - rpow 2 (1/2)), by {
            conv at this {
                congr,
                to_rhs,
                rw h1
            },
            assumption
        },
        false.elim $ absurd h this
    )
    (λ xGt,
        or.elim3 (lt_trichotomy x (rpow 2 (1/2)))
            (λ xLt,
                have h1 : 0 < (x - rpow 2 (1/3)), by linarith,
                have 0 > (x - rpow 2 (1/2)), by linarith,
                have 0 > (x - rpow 2 (1/3)) * (x - rpow 2 (1/2)), from linarith.mul_neg this h1,
                have ¬ 0 < (x - rpow 2 (1/3)) * (x - rpow 2 (1/2)), from asymm this,
                false.elim $ absurd h this
            )
            (λ xEq,
                have x - rpow 2 (1/2) = 0, from sub_eq_zero.mpr xEq,
                -- Zero case
                have h1 : 0 = (x - rpow 2 (1/3)) * (x - rpow 2 (1/2)), from eq.symm $ by rw [this, mul_zero],
                have ¬ (0: ℝ) < 0, from lt_irrefl 0,
                have ¬ 0 < (x - rpow 2 (1/3)) * (x - rpow 2 (1/2)), by {
                    conv at this {
                        congr,
                        to_rhs,
                        rw h1
                    },
                    assumption
                },
                false.elim $ absurd h this
            )
            (λ xGt2, or.inr $ has_lt.lt.gt xGt2)
    )

-- (xi)

def ex_xi : ∀ (x : ℕ), (2:ℝ)^x < 8 → x < 3
| 0 h := by linarith
| 1 h := by linarith
| 2 h := by linarith
| 3 h := by linarith
| (n+3) h := (
    have (3:ℕ) ≤ (n+3), by linarith,
    have helper1 : (2:ℝ)^3 ≤ 2^(n+3), from pow_le_pow (le_of_lt $ one_lt_two) this,
    have helper2 : (2:ℝ)^3 = 8, by norm_num,
    have h : (2:ℝ)^(n+3) < 8, from h,
    have h1 : ¬(2:ℝ)^(n+3) ≥ 8, from not_le.mpr h,
    have h2 : 8 ≤ (2:ℝ)^(n+3), from (eq.symm helper2).trans_le helper1,
    false.elim $ absurd h2 h1
)

-- (xii)

def ex_xii : ∀ (x : ℕ), ↑x + (3 : ℤ)^x < 4 → x = 0
| 0 := congr_fun rfl
| 1 :=
    assume h,
    have (1: ℤ) + 3^1 = 4, by norm_num,
    have (4: ℤ) < 4, by {
        conv {
            to_rhs,
            rw [<-this]
        },
        assumption
    },
    false.elim $ lt_irrefl 4 $ this
| (n+2) := (
    assume (h : ↑(n+2) + (3:ℤ)^(n+2) < 4),
    have oneCase : (1: ℤ) + 3^1 = 4, by norm_num,
    have left : 1 < n+2, by linarith,
    have 3^1 ≤ (3:ℤ)^(n+2), from pow_le_pow (by norm_num) (le_of_lt left),
    have left : (1:ℤ) < n+2, by linarith,
    have (1:ℤ) + 3^1 ≤ (n+2) + 3^(n+2), from add_le_add (le_of_lt left) this,
    have (4:ℤ) ≤ (n+2) + 3^(n+2), by rwa [oneCase] at this,
    have ¬(n+2 : ℤ) + 3^(n+2) < 4, from not_lt.mpr this,
    false.elim $ absurd h this
)

-- (xiii)

example (x : ℝ) : x ≠ 0 → x ≠ 1 → (0 < x⁻¹ + (1 - x)⁻¹ ↔ 0 < x ∧ x < 1) :=
begin
intros hZero hOne,
split,
{
    intro h,
    have : 1 - x ≠ 0, from sub_ne_zero.mpr (ne.symm hOne),
    have h1 : x⁻¹ + (1-x)⁻¹ = (x + (1 -x)) / (x * (1 - x)), from inv_add_inv hZero this,
    have h2 : (x + (1 -x)) / (x * (1 - x)) = 1 / (x * (1 - x)), by ring,
    have : 0 < 1 / (x * (1 - x)), by rwa [h1, h2] at h,
    have : 0 < (x * (1 - x)), from one_div_pos.mp this,
    have h3 : x^2 < x, by linarith only [this],
    have h4 : 0 < x, from gt_of_gt_of_ge h3 (pow_two_nonneg x),
    have : x < 1, from by_contradiction (
        assume (h : ¬ (x < 1)),
        have 1 ≤ x, from not_lt.mp h,
        have x ≤ x * x, from (le_mul_iff_one_le_left h4).mpr this,
        have x ≤ x^2, by rwa [<-pow_two] at this,
        have ¬(x^2 < x), from not_lt.mpr this,
        absurd h3 this
    ),
    exact ⟨h4, this⟩
},
intro h,
rcases h with ⟨xPos, xLtOne⟩,
have left : 0 < x⁻¹, exact inv_pos.mpr xPos,
have : 0 < (1 - x), by linarith only [xLtOne],
have right : 0 < (1 - x)⁻¹, exact inv_pos.mpr this,
exact add_pos left right
end

-- (xiv)

example (x : ℝ) : x < -1 ∨ x > 1 ↔ 0 < (x - 1) / (x + 1) :=
begin
    split,
    {

        intros h,
        rcases h with xLt | xGt,
        {
            have numerator : x - 1 < 0, by linarith only [xLt],
            have denom : x + 1 < 0, by linarith only [xLt],
            exact div_pos_of_neg_of_neg numerator denom,
        },
        {
            have numerator : 0 < x - 1, by linarith only [xGt],
            have denom : 0 < x + 1, by linarith only [xGt],
            exact div_pos numerator denom
        }
    },
    intro h,
    rcases (lt_or_ge x (-1)) with xLtNegOne | xGeNegOne;
    rcases (le_or_gt x 1) with xLeOne | xGtOne,
    any_goals { { left, exact xLtNegOne } <|> { right, exact xGtOne } },
    have : 0 ≥ (x - 1) / (x + 1), apply div_nonpos_of_nonpos_of_nonneg, linarith only [xLeOne], linarith only [xGeNegOne],
    exact (false.elim $ absurd h (not_lt_of_ge this))
end
