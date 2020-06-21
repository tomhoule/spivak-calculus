
import data.rat.basic
import data.real.basic
import tactic.norm_num

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


-- (vi)
example : 2 < x^2 + x + 1 → 0 < x^2 + x - 1 :=
assume h,
have 2 + -2 < x^2 + x + 1 + -2, from add_lt_add_right h (-2),
have 0 < x^2 + x + -1, by rwa [add_assoc] at this,
have 0 < x^2 + x - 1, by assumption,
-- I don't know how to go further with lean at this point. You could use the quadratic formula to
-- get the roots, then take any value of x in the intervals to find out the sign, and take the
-- positive ones. But that's not a proof.
this

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
        or.inl $ show 3 < x, by simpa
    )
    (λ (h : x + 2 < 0),
        have x + 2 - 2 < 0 -2, from sub_lt_sub_right h 2,
        have x + 0 < -2, by rwa [add_sub_assoc] at this,
        have x < -2, by rwa [add_zero] at this,
        or.inr $ this
    )

--- (viii)
example : 0 < x^2 + x + 1 := sorry -- can't factorize, we would have to use the quadratic formula here

--- (ix)
constant π : ℤ -- just because I can

example : 0 < (x - π) * (x + 5) * (x - 3) := sorry -- these three being the roots
-- begin
-- intro h,
-- have h1 : (0 < (x - π) * (x + 5) ∧ 0 < x - 3) ∨
--             (((x - π) * (x + 5) < 0)) ∧ x - 3 < 0, from pos_and_pos_or_neg_and_neg_of_mul_pos h,
-- cases h1,
-- {
--     have h2 : (0 < x - π ∧ 0 < x + 5) ∨ (x - π < 0 ∧ x + 5 < 0), from pos_and_pos_or_neg_and_neg_of_mul_pos h1.left,
--     cases h2,
--     { sorry },
--     sorry
-- },
-- -- have h2 : (0 < x - π ∧ 0 < x + 5) ∨ (x - π < 0 ∧ x + 5 < 0), from neg_of_mul_neg_left sorry,
-- sorry
-- end

-- This is painful, I am stopping this exercise here. It feels like I don't have the tools to do
-- interesting proofs on inequalities. It would involve computational/visual methods.
