import data.real.basic
import chap1.problem_18

variables { x1 x2 y1 y2 a : ℝ }

open real (sqrt)

-- (a)

-- The statement in 3ed is wrong, since it doesn't include 0 ≤ a. This was time
-- consuming to figure out on my own.
def schwarz_equality :
0 ≤ a →
x1 = a*y1 →
x2 = a*y2 →
x1*y1 + x2*y2 = sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) :=
λ aNonneg h1 h2,
have aSquareNonneg : 0 ≤ a^2, from pow_two_nonneg a,
have sumNonneg : 0 ≤ y1^2 + y2^2, by simp only [pow_two_nonneg, add_nonneg],
calc
    x1*y1 + x2*y2   = a*y1*y1 + a*y2*y2 : by rw [h1, h2]
                ... = a*(y1^2 + y2^2) : by linarith
                ... = a * sqrt ((y1^2 + y2^2) * (y1^2 + y2^2)) : by rw [<-pow_two, real.sqrt_sqr sumNonneg]
                ... = sqrt (a^2) * sqrt ((y1^2 + y2^2) * (y1^2 + y2^2)) : by rw [real.sqrt_sqr aNonneg]
                ... = sqrt (a^2 * (y1^2 + y2^2) * (y1^2 + y2^2)) : by rw [<-real.sqrt_mul aSquareNonneg, mul_assoc]
                ... = sqrt (a^2 * (y1^2 + y2^2)) * sqrt (y1^2 + y2^2) : by rw [mul_comm _ (y1^2 + y2^2), real.sqrt_mul sumNonneg, mul_comm (sqrt (y1^2 + y2^2))]
                ... = sqrt (a^2 * y1^2 + a^2 * y2^2) * sqrt (y1^2 + y2^2) : by rw [mul_add]
                ... = sqrt ((a*y1)^2 + (a*y2)^2) * sqrt (y1^2 + y2^2) : by rw [<-mul_pow, <-mul_pow]
                ... = sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) : by rw [h1, h2]
--     )
--     (λ aNeg,
--     have l1 : abs a^2 = a^2, from (
--         have l1 : abs a^2 = abs (a^2), from pow_abs a 2,
--         have l2 : abs (a^2) = a^2, from abs_of_nonneg (pow_two_nonneg a),
--         eq.trans l1 l2
--     ),
--     calc
--         x1*y1 + x2*y2   = a*y1*y1 + a*y2*y2 : by rw [h1, h2]
--                     ... = a*(y1^2 + y2^2) : by linarith
--                     ... = a * sqrt ((y1^2 + y2^2) * (y1^2 + y2^2)) : by rw [<-pow_two, real.sqrt_sqr sumNonneg]
--                     ... = - -a * sqrt ((y1^2 + y2^2) * (y1^2 + y2^2)) : by rw [neg_neg a]
--                     ... = -(abs a) * sqrt ((y1^2 + y2^2) * (y1^2 + y2^2)) : by rw [abs_of_neg aNeg]
--                     ... = -sqrt (abs a^2) * sqrt ((y1^2 + y2^2) * (y1^2 + y2^2)) : by rw [real.sqrt_sqr (abs_nonneg a)]
--                     ... = -1 * sqrt (a^2) * sqrt ((y1^2 + y2^2) * (y1^2 + y2^2)) : by rw [neg_one_mul, l1]
--                     ... = -1 * sqrt (a^2 * (y1^2 + y2^2) * (y1^2 + y2^2)) : by rw [mul_assoc (-1 : real), <-real.sqrt_mul aSquareNonneg, mul_assoc]
--                     ... = -1 * (sqrt (a^2 * (y1^2 + y2^2)) * sqrt (y1^2 + y2^2)) : by rw [mul_comm _ (y1^2 + y2^2), real.sqrt_mul sumNonneg, mul_comm (sqrt (y1^2 + y2^2))]
--                     ... = -1 * sqrt (a^2 * y1^2 + a^2 * y2^2) * sqrt (y1^2 + y2^2) : by rw [<-mul_assoc, mul_add]
--                     ... = -1 * sqrt ((a*y1)^2 + (a*y2)^2) * sqrt (y1^2 + y2^2) : by rw [<-mul_pow, <-mul_pow]
--                     ... = -1 * sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) : by rw [h1, h2]
--     )
-- eq.symm $ calc
--     sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) = sqrt ((a*y1)^2 + (a*y2)^2) * sqrt (y1^2 + y2^2) : by rw [h1, h2]
--                                         ... = sqrt (a^2*(y1^2 + y2^2)) * sqrt (y1^2 + y2^2) : by simp only [mul_pow, mul_add]
--                                         ... = sqrt (a^2) * sqrt (y1^2 + y2^2) * sqrt (y1^2 + y2^2) : by rw [real.sqrt_mul (aSquareNonneg)]
--                                         ... = sqrt (a^2) * sqrt ((y1^2 + y2^2) * (y1^2 + y2^2)) : by rw [mul_assoc, real.sqrt_mul (sumNonneg)]
--                                         ... = sqrt (a^2) * (y1^2 + y2^2) : by rw [real.sqrt_mul_self (sumNonneg)]
--                                         ... = sqrt (a^2) * y1^2 + sqrt (a^2) * y2^2 : by rw mul_add
--                                         ... = sqrt (a^2) * sqrt ((y1^2)^2) + sqrt (a^2) * sqrt ((y2^2)^2) : by rw [real.sqrt_sqr (pow_two_nonneg y1), real.sqrt_sqr (pow_two_nonneg y2)]
--                                         ... = sqrt (a^2 * (y1^2)^2) + sqrt (a^2 * (y2^2)^2) : by rw [real.sqrt_mul (aSquareNonneg), real.sqrt_mul (aSquareNonneg)]
--                                         ... = sqrt ((a * y1 * y1)^2) + sqrt ((a * y2 * y2)^2) : by rw [helper y1, helper y2]
--                                         ... = sqrt ((x1 * y1)^2) + sqrt ((x2 * y2)^2) : by rw [h1, h2]
--                                         -- ... = abs a * (y1^2 + y2^2) : by rw [real.sqrt_sqr_eq_abs]
--                                         -- ... = abs a * y1^2 + abs a * y2^2 : by linarith
--                                         -- ... = abs a * abs (y1^2) + abs a * abs (y2^2) : by rw [abs_of_nonneg (pow_two_nonneg y1), abs_of_nonneg (pow_two_nonneg y2)]
--                                         -- ... = abs (a * y1^2) + abs (a * y2^2) : by rw [<-abs_mul, <-abs_mul]
--                                         -- ... = abs (a * y1 * y1) + abs (a * y2 * y2) : by rw [pow_two, pow_two, mul_assoc a y1, mul_assoc a y2]
--                                         -- ... = abs (x1 * y1) + abs (x2 * y2) : by rw [h1, h2]
--                                         ... = x1*y1 + x2*y2 : by rw [real.sqrt_sqr sorry, real.sqrt_sqr sorry]
-- eq.symm $ calc
--     sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) = sqrt ((x1^2 + x2^2) * (y1^2 + y2^2)) : ((x1 ^ 2 + x2 ^ 2).sqrt_mul' sumNonneg).symm
--                                         ... = sqrt (x1^2 * y1^2 + x1^2 * y2^2 + x2^2 * y1^2 + x2^2 * y2^2) : by rw helper'
--                                         ... = sqrt ((a * y1)^2 * y1^2 + (a * y1)^2 * y2^2 + (a*y2)^2 * y1^2 + (a*y2)^2 * y2^2) : by rw [h1, h2]
--                                         ... = sqrt (a^2 * y1^2 * y1^2 + a^2 * y1^2 * y2^2 + a^2 * y2^2 * y1^2 + a^2 * y2^2 * y2^2) : by rw [mul_pow, mul_pow]
--                                         ... = x1*y1 + x2*y2 : sorry

def schwarz_equality_zero : y1 = 0 ∧ y2 = 0 → x1*y1 + x2*y2 = sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) :=
λ ⟨y1Zero, y2Zero⟩,
have left : x1*y1 + x2*y2 = 0, by { rw [y1Zero, y2Zero], norm_num },
have right : sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) = 0, by { rw [y1Zero, y2Zero], norm_num },
eq.trans left (eq.symm right)

def schwarz_equality_zero_x : x1 = 0 ∧ x2 = 0 → x1*y1 + x2*y2 = sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) :=
λ ⟨x1Zero, x2Zero⟩,
have left : x1*y1 + x2*y2 = 0, by { rw [x1Zero, x2Zero], norm_num },
have right : sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) = 0, by { rw [x1Zero, x2Zero], norm_num },
eq.trans left (eq.symm right)


def schwarz_1_helper_1 :
¬(y1 = 0 ∧ y2 = 0) → ¬(∃ a, x1 = a * y1 ∧ x2 = a * y2) →
0 < (a*y1 - x1)^2 + (a*y2 - x2)^2 :=
λ hNonzero hANotExists,
have hDisj : y1 ≠ 0 ∨ y2 ≠ 0, from not_and_distrib.elim_left hNonzero,
have ¬(a*y1 - x1 = 0 ∧ a*y2 - x2 = 0), from (
    suffices a*y1 - x1 ≠ 0 ∨ a*y2 - x2 ≠ 0, from not_and_distrib.mpr this,
    or.elim (em (a*y1-x1 = 0))
        (λ h,
            or.elim (em (a*y2 - x2 = 0))
                (λ h,
                    have left : x1 = a*y1, by linarith,
                    have right : x2 = a*y2, by linarith,
                    have ∃ a, x1 = a * y1 ∧ x2 = a * y2, from ⟨a, ⟨left, right⟩⟩,
                    false.elim $ hANotExists this
                )
                (λ h, or.inr h)
        )
        (λ h, or.inl h)
),
have a*y1 - x1 ≠ 0 ∨ a*y2 - x2 ≠ 0, from not_and_distrib.elim_left this,
or.elim this
    (λ h,
        have h1 : 0 < (a*y1 - x1)^2, from pow_two_pos_of_ne_zero (a * y1 - x1) h,
        have 0 ≤ (a*y2 - x2)^2, from pow_two_nonneg (a*y2-x2),
        lt_add_of_pos_of_le h1 this
    )
    (λ h,
        have h1 : 0 < (a*y2 - x2)^2, from pow_two_pos_of_ne_zero (a * y2 - x2) h,
        have 0 ≤ (a*y1 - x1)^2, from pow_two_nonneg (a*y1-x1),
        lt_add_of_le_of_pos this h1
    )

def schwarz_1_helper_2 : ∀ a,
¬(y1 = 0 ∧ y2 = 0) →
¬(∃ a, x1 = a * y1 ∧ x2 = a * y2) →
0 < a^2*(y1^2+y2^2) - 2*a*(x1*y1 + x2*y2) + (x1^2 + x2^2) :=
λ a hNonzero hANotExists,
have 0 < (a*y1 - x1)^2 + (a*y2 - x2)^2, from schwarz_1_helper_1 hNonzero hANotExists,
by linarith only [this]

def schwarz_1 : ¬(y1 = 0 ∧ y2 = 0) →
¬(∃ a, x1 = a * y1 ∧ x2 = a * y2) →
(x1*y1 + x2*y2) < sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) :=
assume h1 h2,
have sumYPos : 0 < y1^2 + y2^2, begin
    cases (not_and_distrib.elim_left h1),
    {
        have : 0 < y1^2, from pow_two_pos_of_ne_zero y1 h,
        apply add_pos_of_pos_of_nonneg, exact this, exact pow_two_nonneg y2
    },
    have : 0 < y2^2, from pow_two_pos_of_ne_zero y2 h,
    apply add_pos_of_nonneg_of_pos,
    exact pow_two_nonneg y1, exact this
end,
have sumYNonzero : y1^2 + y2^2 ≠ 0, from ne.symm $ ne_of_lt sumYPos,
have sumYSquarePos : 0 < (y1^2 + y2^2)^2, from pow_pos sumYPos 2,

-- Restate the previous result.
have l1 : ∀ a, 0 < a^2*(y1^2+y2^2) - 2*a*(x1*y1 + x2*y2) + (x1^2 + x2^2), from λ a, schwarz_1_helper_2 a h1 h2,

-- We now have to factorize the x out (more general than the a in the previous
-- schema). We take a to be x, then (y1^2 + y2^2) * (a^2 + a*b + c). Then pos
-- mul pos. What. The. Heck.
let
    b := (-2*(x1*y1+x2*y2)) / (y1^2+y2^2),
    c := (x1^2 + x2^2) / (y1^2+y2^2)
in
-- Factorize with a neat a^2+b*a+c
have l2 : ∀ a, 0 < (y1^2+y2^2) * ((a^2) + b*a + c), from (
    λ a,
    have helper1 : ((x1^2 + x2^2) * (y1^2+y2^2) / (y1^2+y2^2)) = (y1^2+y2^2) * ((x1^2+x2^2) / (y1^2+y2^2)), by { ring },
    have helper2 : ((-2*(x1*y1 + x2*y2))*(a * (y1^2+y2^2) / (y1^2+y2^2))) = (y1^2+y2^2) * a * (-2*(x1*y1 + x2*y2)/ (y1^2+y2^2)), by ring,
    calc
    0   < a^2*(y1^2+y2^2) - 2*a*(x1*y1 + x2*y2) + (x1^2 + x2^2) : l1 a
    ... = (y1^2+y2^2) * a^2 + (-2*(x1*y1 + x2*y2))*a + (x1^2 + x2^2) : by linarith
    ... = (y1^2+y2^2) * a^2 + ((-2*(x1*y1 + x2*y2))*(a * (y1^2+y2^2) / (y1^2+y2^2))) + ((x1^2 + x2^2) * (y1^2+y2^2) / (y1^2+y2^2)) : by rw [mul_div_cancel a sumYNonzero, mul_div_cancel (x1^2 + x2^2) sumYNonzero]
    ... = (y1^2+y2^2) * a^2 + (y1^2+y2^2) * (a * b) + (y1^2+y2^2) * c : by rwa [helper1, helper2, mul_assoc]
    ... = (y1^2+y2^2) * ((a^2) + b*a + c) : by simp only [mul_add, mul_comm a b]
),
have l3 : ∀ a, 0 < (a^2) + b*a + c, from λ a, pos_of_mul_pos_left (l2 a) (le_of_lt sumYPos),
have l4 : b^2 - 4*c < 0, from ((@part_b b c).elim_right l3),
have l5 : b^2 < 4*c, by linarith,
have cPos : 0 < c, from (
    have 0 ≤ b^2, from pow_two_nonneg b,
    have 0 < 4*c, from gt_of_gt_of_ge l5 this,
    by linarith only [this]
),
have sumXSquarePos : 0 < (x1^2 + x2^2), from (
    have l1 : 0 < (x1^2 + x2^2) * (y1^2+y2^2)⁻¹, from calc
        0   < c : cPos
        ... = (x1^2 + x2^2) * (y1^2+y2^2)⁻¹ : division_def,
    have 0 < (y1^2+y2^2)⁻¹, from inv_pos.mpr sumYPos,
    pos_of_mul_pos_right l1 (le_of_lt this)
),
have (-2*(x1*y1+x2*y2))^2 / (y1^2+y2^2)^2 < 4 * ((x1^2 + x2^2) / (y1^2+y2^2)), by rwa [div_pow] at l5,
have (-2*(x1*y1+x2*y2))^2 / (y1^2+y2^2)^2 = 4 * ((x1*y1+x2*y2)^2 / (y1^2+y2^2)^2), by ring,
have (x1*y1+x2*y2)^2 / (y1^2+y2^2)^2 < ((x1^2 + x2^2) / (y1^2+y2^2)), by linarith [this],
have ((x1*y1+x2*y2)^2 / (y1^2+y2^2)^2) * (y1^2+y2^2)^2 < ((x1^2 + x2^2) / (y1^2+y2^2)) * (y1^2+y2^2)^2, from mul_lt_mul this (le_of_eq rfl) sumYSquarePos (le_of_lt cPos),
have helper1 : ((x1^2 + x2^2) / (y1^2+y2^2)) * (y1^2+y2^2)^2 = (x1^2 + x2^2) * (y1^2+y2^2), from (
    calc
    ((x1^2 + x2^2) / (y1^2+y2^2)) * (y1^2+y2^2)^2 = (x1^2 + x2^2) / (y1^2+y2^2) * (y1^2+y2^2) * (y1^2+y2^2) : by rw [pow_two (y1^2+y2^2), mul_assoc]
    ... = (x1^2 + x2^2) * (y1^2+y2^2) / (y1^2+y2^2) * (y1^2+y2^2) : by ring
    ... = (x1^2 + x2^2) * (y1^2+y2^2) : by rw [mul_div_cancel _ sumYNonzero]
),
have helper2 : ((x1*y1+x2*y2)^2 / (y1^2+y2^2)^2) * (y1^2+y2^2)^2 = (x1*y1+x2*y2)^2, from (
    calc
    ((x1*y1+x2*y2)^2 / (y1^2+y2^2)^2) * (y1^2+y2^2)^2 = ((x1*y1+x2*y2)^2 * (y1^2+y2^2)^2) / (y1^2+y2^2)^2 : by ring
    ... = (x1*y1+x2*y2)^2 : by rw [mul_div_cancel _ (ne.symm $ ne_of_lt sumYSquarePos)]
),
have (x1*y1+x2*y2)^2 < (x1^2 + x2^2) * (y1^2+y2^2), by rwa [<-helper1, <-helper2],
have sqrt ((x1*y1+x2*y2)^2) < sqrt ((x1^2 + x2^2) * (y1^2+y2^2)), from (real.sqrt_lt (pow_two_nonneg (x1*y1+x2*y2)) (le_of_lt $ mul_pos sumXSquarePos sumYPos)).mpr this,
have abs (x1*y1 + x2*y2) < sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2), by rwa [real.sqrt_sqr_eq_abs, real.sqrt_mul (le_of_lt sumXSquarePos)] at this,
(abs_lt.elim_left this).right


-- have l2 : ∀ a, 0 < (a * sqrt (y1^2+y2^2))^2 + b*(a * sqrt (y1^2+y2^2)) + c, from (
--     λ a,
--     calc
--         0   < a^2*(y1^2+y2^2) - 2*a*(x1*y1 + x2*y2) + (x1^2 + x2^2) : l1 a
--         ... = (a * sqrt (y1^2+y2^2))^2 - 2*a*(x1*y1 + x2*y2) + (x1^2 + x2^2) : by rw [mul_pow a _ 2, real.sqr_sqrt (le_of_lt sumYPos)]
--         ... = (a * sqrt (y1^2+y2^2))^2 + b*(a * sqrt (y1^2+y2^2)) + c : sorry
-- ),
-- have l1' : ∀ a, (a * sqrt (y1^2+y2^2))^2 = a ^ 2 * (y1 ^ 2 + y2 ^ 2), by simp only [mul_pow _ _ 2, real.sqr_sqrt sumYNonneg, forall_const, eq_self_iff_true],

-- have sumXNonneg : 0 ≤ x1^2 + x2^2, by simp only [pow_two_nonneg, add_nonneg],
-- have sqrtYSum : (sqrt (y1^2 + y2^2))^2 = y1^2 + y2^2, from real.sqr_sqrt sumYNonneg,
-- have sqrtXSum : (sqrt (x1^2 + x2^2))^2 = x1^2 + x2^2, from real.sqr_sqrt sumXNonneg,
-- have equiv_1 : 2*a*(x1*y1 + x2*y2) < a^2*(y1^2+y2^2) + (x1^2 + x2^2), by linarith,

-- Translate the helper 2 inequality to a b²-4c < 0, so we can deduce
-- 0 < x² + bx + c

-- -- Translate the helper 2 inequality to x^2 + b*x + c, then figure out the
-- -- b² - 4c. (see problem 18 b)
-- let x := a*sqrt (y1^2+y2^2),
--     b := 2 * (sqrt (y1^2+y2^2))⁻¹ * (x1*y1 + x2*y2)
-- in
-- have x^2 = a^2*(y1^2+y2^2), from (
--     calc
--     x^2 = a^2 * (sqrt (y1^2+y2^2))^2 : by rw [mul_pow a]
--     ... = a^2*(y1^2+y2^2) : by rw [real.sqr_sqrt sumYNonneg]
-- ),
-- have sqrt (y1^2+y2^2) * (sqrt (y1^2+y2^2))⁻¹ = 1, from sorry,
-- have b*x = 2*a*(x1*y1 + x2*y2), from (
--     calc
--     b*x = (2 * (sqrt (y1^2+y2^2))⁻¹ * (x1*y1 + x2*y2)) * (a*sqrt (y1^2+y2^2)) : rfl
--     ... = 2 * a * (sqrt (y1^2+y2^2) * (sqrt (y1^2+y2^2))⁻¹ * (x1*y1 + x2*y2)) : by linarith
--     ... = 2 * a * (1 * (x1*y1 + x2*y2)) : by rw [<-this]
--     ... = 2*a*(x1*y1 + x2*y2) : by linarith
-- ),
-- sorry

-- Figure out the x, b and c we need for schwarz with part_b, then work backwards
-- from there.
-- suffices 0 < (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2)) - (x1*y1 + x2*y2), by linarith only [this],
-- let x := a * (y1^2 + y2^2),
--     b := (x1*y1 + x2*y2) / (y1^2 + y2^2),
--     c := x1^2 + x2^2
-- in


-- x^2 + b*x + c := sqrt (y1^2 + y2^2) + (sqrt (x1^2 + x2^2)) + ((x1*y1 + x2*y2)
-- - sqrt y1^2 + y2^2)
-- λsqrt(y1^2+y2^2)

-- have middle : (y1^2+y2^2) * (x1^2 + x2^2) = (y1*x1)^2 + (y1*x2)^2 + (y2*x1)^2 + (y2*x2)^2, by linarith,
-- have (a*sqrt (y1^2+y2^2) - sqrt (x1^2 + x2^2))^2 = a^2*(y1^2+y2^2) - 2*a*sqrt ((y1^2+y2^2) * (x1^2 + x2^2)) + (x1^2 + x2^2), from (
--     calc
--     (a*sqrt (y1^2+y2^2) - sqrt (x1^2 + x2^2))^2 = (a^2*(sqrt (y1^2+y2^2))^2) - 2*(a*sqrt (y1^2+y2^2))*(sqrt (x1^2 + x2^2)) + (sqrt (x1^2 + x2^2))^2 : by linarith [sqrtYSum]
--     ... = (a^2*(y1^2+y2^2)) - 2*(a*sqrt (y1^2+y2^2))*(sqrt (x1^2 + x2^2)) + (x1^2 + x2^2) : by rw [sqrtYSum, sqrtXSum]
--     ... = (a^2*(y1^2+y2^2)) - 2*a*(sqrt (y1^2+y2^2) * sqrt (x1^2 + x2^2)) + (x1^2 + x2^2) : by linarith
--     ... = a^2*(y1^2+y2^2) - 2*a*sqrt ((y1^2+y2^2) * (x1^2 + x2^2)) + (x1^2 + x2^2) : by rwa [real.sqrt_mul sumYNonneg]
-- ),
-- sorry
-- suffices 0 < (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2)) - (x1*y1 + x2*y2), by linarith only [this],
-- have 0 < sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) - (x1*y1 + x2*y2), from sorry,
-- by linarith
-- calc
--     0   < a^2*(y1^2+y2^2) - 2*a*(x1*y1 + x2*y2) + (x1^2 + x2^2) : schwarz_1_helper_2 h1 h2
--     ... < (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2)) - (x1*y1 + x2*y2) : sorry

-- (b)

private def b_helper (x y : ℝ) : 2*x*y ≤ x^2 + y^2 :=
have 0 ≤ (x - y)^2, from pow_two_nonneg (x - y),
have 0 ≤ x^2 + y^2 - (2*x*y), by linarith only [this],
sub_nonneg.mp this

def schwarz_2 : x1*y1 + x2*y2 ≤ sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) :=
begin

cases (em (x1 = 0 ∧ x2 = 0)),
{ exact ((le_of_eq $ schwarz_equality_zero_x h)) },
cases (em (y1 = 0 ∧ y2 = 0)),
{ exact (le_of_eq $ schwarz_equality_zero h_1) },

have sumSqXPos : 0 < x1^2 + x2^2, by {
    cases (not_and_distrib.mp h),
    { exact add_pos_of_pos_of_nonneg (pow_two_pos_of_ne_zero x1 h_2) (pow_two_nonneg x2) },
    exact add_pos_of_nonneg_of_pos (pow_two_nonneg x1) (pow_two_pos_of_ne_zero x2 h_2)
},
have sumSqYPos : 0 < y1^2 + y2^2, by {
    cases (not_and_distrib.mp h_1),
    { exact add_pos_of_pos_of_nonneg (pow_two_pos_of_ne_zero y1 h_2) (pow_two_nonneg y2) },
    exact add_pos_of_nonneg_of_pos (pow_two_nonneg y1) (pow_two_pos_of_ne_zero y2 h_2)
},
have mulSqrtPos : 0 < sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2), from mul_pos (real.sqrt_pos.elim_right sumSqXPos) (real.sqrt_pos.elim_right sumSqYPos),
have sq1 : (x1 / sqrt (x1^2 + x2^2))^2 = x1^2 / (x1^2 + x2^2), by field_simp [real.sqr_sqrt (le_of_lt sumSqXPos)],
have sq2 : (x2 / sqrt (x1^2 + x2^2))^2 = x2^2 / (x1^2 + x2^2), by field_simp [real.sqr_sqrt (le_of_lt sumSqXPos)],
have sq3 : (y1 / sqrt (y1^2 + y2^2))^2 = y1^2 / (y1^2 + y2^2), by field_simp [real.sqr_sqrt (le_of_lt sumSqYPos)],
have sq4 : (y2 / sqrt (y1^2 + y2^2))^2 = y2^2 / (y1^2 + y2^2), by field_simp [real.sqr_sqrt (le_of_lt sumSqYPos)],
have mul1 : (x1 / sqrt (x1^2 + x2^2)) * (y1 / sqrt (y1^2 + y2^2)) = (x1 * y1) / (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2)), by rw [div_mul_div],
have mul2 : (x2 / sqrt (x1^2 + x2^2)) * (y2 / sqrt (y1^2 + y2^2)) = (x2 * y2) / (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2)), by rw [div_mul_div],

have ones :
    2 * (x1 / sqrt (x1^2 + x2^2)) * (y1 / sqrt (y1^2 + y2^2))
    ≤ (x1 / sqrt (x1^2 + x2^2))^2 + (y1 / sqrt (y1^2 + y2^2))^2,
from b_helper (x1 / sqrt (x1^2 + x2^2)) (y1 / sqrt (y1^2 + y2^2)),

have twos :
    2 * (x2 / sqrt (x1^2 + x2^2)) * (y2 / sqrt (y1^2 + y2^2))
    ≤ (x2 / sqrt (x1^2 + x2^2))^2 + (y2 / sqrt (y1^2 + y2^2))^2,
from b_helper (x2 / sqrt (x1^2 + x2^2)) (y2 / sqrt (y1^2 + y2^2)),

have :
    2 * (x1 / sqrt (x1^2 + x2^2)) * (y1 / sqrt (y1^2 + y2^2))
    + 2 * (x2 / sqrt (x1^2 + x2^2)) * (y2 / sqrt (y1^2 + y2^2))
    ≤ (x1 / sqrt (x1^2 + x2^2))^2 + (y1 / sqrt (y1^2 + y2^2))^2
    + ((x2 / sqrt (x1^2 + x2^2))^2 + (y2 / sqrt (y1^2 + y2^2))^2),
from add_le_add ones twos,

have l1 :
    2
    * (
        (x1 / sqrt (x1^2 + x2^2)) * (y1 / sqrt (y1^2 + y2^2))
        + (x2 / sqrt (x1^2 + x2^2)) * (y2 / sqrt (y1^2 + y2^2))
    )
    ≤ x1^2 / (x1^2 + x2^2) + y1^2 / (y1^2 + y2^2)
    + x2^2 / (x1^2 + x2^2) + y2^2 / (y1^2 + y2^2),
by linarith [sq1, sq2, sq3, sq4],

have left :
    (x1 / sqrt (x1^2 + x2^2)) * (y1 / sqrt (y1^2 + y2^2))
    + (x2 / sqrt (x1^2 + x2^2)) * (y2 / sqrt (y1^2 + y2^2))
    = (x1*y1 + x2*y2) / (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2)),
from (
    calc
    (x1 / sqrt (x1^2 + x2^2)) * (y1 / sqrt (y1^2 + y2^2))
    + (x2 / sqrt (x1^2 + x2^2)) * (y2 / sqrt (y1^2 + y2^2))
    = (x1 * y1) / (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2)) + (x2 * y2) / (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2)) : by rw [mul1, mul2]
    ... = (x1*y1 + x2*y2) / (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2)) : by rw [div_add_div_same]
),

have right :
    x1^2 / (x1^2 + x2^2) + y1^2 / (y1^2 + y2^2)
    + x2^2 / (x1^2 + x2^2) + y2^2 / (y1^2 + y2^2)
    = 2,
from (
    calc
    x1^2 / (x1^2 + x2^2) + y1^2 / (y1^2 + y2^2)
    + x2^2 / (x1^2 + x2^2) + y2^2 / (y1^2 + y2^2)
    = x1^2 / (x1^2 + x2^2) + (x2^2 / (x1^2 + x2^2)) + (y1^2 / (y1^2 + y2^2) + (y2^2 / (y1^2 + y2^2))) : by ring
    ... = 1 + 1 : by field_simp [div_self (ne.symm $ ne_of_lt sumSqXPos), div_self (ne.symm $ ne_of_lt sumSqYPos)]
    ... = 2 : norm_num.one_succ
),

have :
    2 * ((x1*y1 + x2*y2) / (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2))) ≤ 2,
by rwa [left, right] at l1,

have :
    2 * ((x1*y1 + x2*y2) / (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2))) * (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2)) ≤ 2 * (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2)),
from (mul_le_mul_right mulSqrtPos).elim_right this,

have :
    ((x1*y1 + x2*y2) / (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2))) * (sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2)) ≤ sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2),
by linarith,

rwa [
    div_mul_cancel (x1*y1 + x2*y2) (ne.symm $ ne_of_lt mulSqrtPos)
] at this
end

-- c

def schwarz_3_aux : (x1^2 + x2^2)*(y1^2 + y2^2) = (x1*y1 + x2*y2)^2 + (x1*y2 - x2*y1)^2 :=
calc
    (x1^2 + x2^2)*(y1^2 + y2^2) = x1^2 * (y1^2 + y2^2) + x2^2 * (y1^2 + y2^2) : by linarith
    ... = x1^2 * y1^2 + x1^2 * y2^2 + (x2^2 * y1^2 + x2^2 * y2^2) : by rw [mul_add (x1^2), mul_add (x2^2)]
    ... = (x1 * y1)^2 + x1^2*y2^2 + (x2^2 * y1^2 + (x2 * y2)^2) : by rw [mul_pow x1, mul_pow x2]
    ... = (x1*y1 + x2*y2)^2 + (x1*y2 - x2*y1)^2 : by linarith

def schwarz_3 : x1*y1 + x2*y2 ≤ sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2) :=
begin
have sumXSqNonneg : 0 ≤ x1^2 + x2^2, from add_nonneg (pow_two_nonneg x1) (pow_two_nonneg x2),
have sumYSqNonneg : 0 ≤ (y1^2 + y2^2), from add_nonneg (pow_two_nonneg y1) (pow_two_nonneg y2),
have : 0 ≤ (x1*y2 - x2*y1)^2, from pow_two_nonneg (x1*y2 - x2*y1),
have : (x1*y1 + x2*y2)^2 ≤ (x1*y1 + x2*y2)^2 + (x1*y2 - x2*y1)^2, from le_add_of_nonneg_right this,
have : (x1*y1 + x2*y2)^2 ≤ (x1^2 + x2^2)*(y1^2 + y2^2), by rwa [←schwarz_3_aux] at this,

-- Now take the sqrt of both sides.
have leftNonneg : 0 ≤ (x1*y1 + x2*y2)^2, from pow_two_nonneg (x1 * y1 + x2 * y2),
have rightNonneg : 0 ≤ (x1^2 + x2^2) * (y1^2 + y2^2), from mul_nonneg sumXSqNonneg sumYSqNonneg,

have : sqrt ((x1*y1 + x2*y2)^2) ≤ sqrt ((x1^2 + x2^2)*(y1^2 + y2^2)), by rwa [real.sqrt_le leftNonneg rightNonneg],
have : abs (x1*y1 + x2*y2) ≤ sqrt (x1^2 + x2^2) * sqrt (y1^2 + y2^2), by rwa [real.sqrt_sqr_eq_abs (x1*y1 + x2*y2), real.sqrt_mul sumXSqNonneg (y1^2 + y2^2)] at this,

exact (abs_le.elim_left this).right
end
