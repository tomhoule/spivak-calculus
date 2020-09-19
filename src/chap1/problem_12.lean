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

def ii : x ≠ 0 → abs (1/x) = 1/(abs x) := sorry

def iii : y ≠ 0 → abs x / abs y = abs (x/y) := sorry

def iv : abs (x - y) ≤ abs x + abs y := sorry

def v : abs x - abs y ≤ abs (x-y) := sorry

def vi : abs (abs x - abs y) ≤ abs (x-y) := sorry

def vii : abs (x + y + z) ≤ abs x + abs y + abs z := sorry
