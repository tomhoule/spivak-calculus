import data.real.basic
import tactic.basic
import tactic.suggest

open real (sqrt)

variables { x y z : ℝ }

def i : abs (x*y) = abs x * abs y :=
or.elim (le_or_gt 0 x)
    (λ xnonneg,
        or.elim (le_or_gt 0 y)
            (λ ynonneg,
                calc
                    abs (x*y)   = x*y : abs_of_nonneg (mul_nonneg xnonneg ynonneg)
                            ... = abs x * abs y : by rw [abs_of_nonneg xnonneg, abs_of_nonneg ynonneg]
            )
            (λ yneg,
                or.elim (eq_or_lt_of_le xnonneg)
                    (λ xzero,
                        have x*y = 0, from mul_eq_zero_of_left (eq.symm xzero) y,
                        have l1 : abs (x*y) = 0, from abs_eq_zero.mpr this,
                        have abs x * abs y = 0, from (
                            calc
                            abs x * abs y = abs 0 * abs y : by rw xzero
                                    ... = 0 * abs y : by rw abs_zero
                                    ... = 0 : by rw zero_mul
                        ),
                        by rwa [l1, this]
                    )
                    (λ xpos,
                        have x*y < 0, from linarith.mul_neg yneg xpos,
                        have absxy : abs (x*y) = -(x*y), from abs_of_neg this,
                        have absp : abs x * abs y = x * (-y), by rw [abs_of_pos xpos, abs_of_neg yneg],
                        have -(x*y) = x * (-y), by linarith,
                        by rw [absxy, absp, this]
                    )
            )
    )
    (λ xneg,
        or.elim3 (lt_trichotomy 0 y)
            (λ ypos,
                have x*y < 0, from mul_neg_of_neg_of_pos xneg ypos,
                have absxy : abs (x*y) = -(x*y), from abs_of_neg this,
                have absp : abs x * abs y = -x * y, by rw [abs_of_pos ypos, abs_of_neg xneg],
                have -(x*y) = -x * y, by linarith,
                by rw [absxy, absp, this]

            )
            (λ yzero,
                have x*y = 0, from mul_eq_zero_of_right x (eq.symm yzero),
                have l1 : abs (x*y) = 0, from abs_eq_zero.mpr this,
                have abs x * abs y = 0, from (
                    calc
                    abs x * abs y = abs x * abs 0 : by rw yzero
                            ... = abs x * 0 : by rw abs_zero
                            ... = 0 : by rw mul_zero
                ),
                by rwa [l1, this]
            )
            (λ yneg,
                have 0 < x*y, from mul_pos_of_neg_of_neg xneg yneg,
                eq.symm $ calc
                    abs x * abs y   = -x * -y : by rw [abs_of_neg xneg, abs_of_neg yneg]
                                ... = x * y : neg_mul_neg x y
                                ... = abs (x*y) : by rw [abs_of_pos this]
            )
    )

def ii : x ≠ 0 → abs (1/x) = 1/(abs x) :=
assume xnonzero,
have absxpos : 0 < abs x, from abs_pos_iff.mpr xnonzero,
have absxnonzero : 0 ≠ abs x, from ne_of_lt absxpos,
have l1 : (abs x) * (abs x)⁻¹ = 1, from mul_inv_cancel (ne.symm absxnonzero),
have l2 : 0 < x*x, from mul_self_pos xnonzero,
have l3 : 0 < 1/(x*x), from one_div_pos.mpr l2,
have l4 : (1/(x*x)) * x = 1/x, from (
    calc
    (1/(x*x)) * x   = (1/(x*x)) * (x/1) : by rw [div_one]
                ... = (1*x)/(x*x*1) : by rw [div_mul_div]
                ... = x / (x*x) : by rw [mul_one, one_mul]
                ... = 1/x : div_mul_left xnonzero
),
have (abs x)⁻¹ = abs (1/x), from (
    calc
    (abs x)⁻¹   = (abs x)⁻¹ * 1 : by rw mul_one
            ... = (abs x)⁻¹ * (abs x * (abs x)⁻¹) : by rw l1
            ... = (abs x)⁻¹ * (abs x)⁻¹ * abs x : by simp only [mul_assoc, mul_comm (abs x)]
            ... = 1/(abs x) * (1/(abs x)) * abs x : by rw [←one_div (abs x)]
            ... = 1/((abs x) * (abs x)) * abs x : by rw [div_mul_div, one_mul]
            ... = 1/(abs (x * x)) * abs x : by rw [abs_mul]
            ... = 1/(x * x) * abs x : by rw [abs_of_pos l2]
            ... = abs (1/(x * x)) * abs x : by rw [abs_of_pos l3]
            ... = abs (1/(x * x) * x) : by rw [abs_mul]
            ... = abs (1/x) : by rw l4
),
eq.symm $ by rwa [one_div]

def iii : y ≠ 0 → abs x / abs y = abs (x/y) :=
assume ynonzero,
have 0 < abs y, from abs_pos_iff.mpr ynonzero,
have absynonzero : 0 ≠ abs y, from ne_of_lt this,
calc
    abs x / abs y   = abs x * (1/(abs y)) : by rw [div_eq_mul_one_div]
                ... = abs x * abs (1/y) : by rw [ii ynonzero]
                ... = abs (x * (1/y)) : by rw abs_mul
                ... = abs (x/y) : by simpa only [one_div]

def iv : abs (x - y) ≤ abs x + abs y :=
calc
    abs (x - y) ≤ abs (x + -y) : by refl
            ... ≤ abs x + abs (-y) : abs_add x (-y)
            ... ≤ abs x + abs y : by rw [abs_neg]

def v : abs x - abs y ≤ abs (x - y) :=
have abs (y - (y-x)) ≤ abs y + abs (y-x), from iv,
have abs (y + x - y) ≤ abs y + abs (y-x), by rwa [sub_sub_assoc_swap] at this,
have abs x ≤ abs y + abs (y-x), by rwa [add_comm y x, add_sub_assoc, sub_self y, add_zero x] at this,
have abs x - abs y ≤ abs (y-x), by linarith,
by rwa [abs_sub]

def vi : abs (abs x - abs y) ≤ abs (x - y) :=
or.elim (le_or_gt 0 (abs x - abs y))
    (λ absxynonneg,
        have l1 : abs (abs x - abs y) = abs x - abs y, from abs_of_nonneg absxynonneg,
        have abs x - abs y ≤ abs (x - y), from v,
        by rwa [←l1] at this
    )
    (λ absxyneg,
        have abs (abs x - abs y) = -(abs x - abs y), from abs_of_neg absxyneg,
        have l1 : abs (abs x - abs y) = abs y - abs x, by linarith,
        have abs y - abs x ≤ abs (y - x), from v,
        show abs (abs x - abs y) ≤ abs (x-y), by rwa [←l1, abs_sub y x] at this
    )

def vii : abs (x + y + z) ≤ abs x + abs y + abs z :=
have l1 : abs (x + y + z) ≤ abs (x + y) + abs z, from abs_add (x+y) z,
have abs (x + y) ≤ abs x + abs y, from abs_add x y,
have l3 : abs (x + y) + abs z ≤ abs x + abs y + abs z, from add_le_add_right this (abs z),
le_trans l1 l3

-- def vii' : abs (x + y + z) = abs x + abs y + abs z ↔
-- (0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z)
-- -- (x < 0 ∧ y < 0 ∨ z < 0)
-- :=
-- iff.intro
-- (

-- )
-- or.elim (le_or_gt 0 x)
--     (λ xnonneg,
--         or.elim (le_or_gt 0 y)
--             (λ ynonneg,
--                 or.elim (le_or_gt 0 z)
--                     (λ znonneg, sorry)
--                     (λ zneg, sorry)
--             )
--             (λ yneg,
--                 or.elim (le_or_gt 0 z)
--                     (λ znonneg, sorry)
--                     (λ zneg, sorry)
--             )
--     )
--     (λ xneg,
--         or.elim (le_or_gt 0 y)
--             (λ ynonneg,
--                 or.elim (le_or_gt 0 z)
--                     (λ znonneg, sorry)
--                     (λ zneg, sorry)
--             )
--             (λ yneg,
--                 or.elim (le_or_gt 0 z)
--                     (λ znonneg, sorry)
--                     (λ zneg,
--                         have l1: abs x + abs y + abs z = -x + -y + -z, by rwa [abs_of_neg xneg, abs_of_neg yneg, abs_of_neg zneg],
--                         have x + y + z < 0, by linarith,
--                         have l2 :abs (x + y + z) = -(x + y + z), from abs_of_neg this,
--                         have -(x + y + z) = -x + -y + -z, by linarith,
--                         have abs (x + y + z) = abs x + abs y + abs z, by rwa [l1, l2, this],
--                         sorry
--                     )
--             )
--     )
