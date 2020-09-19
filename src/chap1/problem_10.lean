import data.real.basic
import tactic.basic
import tactic.suggest

open real (sqrt)

variables { a b c x y : ℝ }

-- (i)

-- The proof could be made much smaller by using le_or_gt instead of
-- lt_trichotomy all over the place.
example :
abs (a + b) - abs b = a ∨
abs (a + b) - abs b = -a ∨
abs (a + b) - abs b = -a - 2*b ∨
abs (a + b) - abs b = a + 2*b :=
have l1 : (b = 0) → (abs (a + b) - abs b = a ∨ abs (a + b) - abs b = -a), from (
    assume (bzero : b = 0),
    have h : abs (a + b) - abs b = abs a, from calc
        abs (a + b) - abs b = abs (a + 0) - abs 0 : by rw [bzero]
                        ... = abs a - 0 : by rw [add_zero, abs_zero]
                        ... = abs a : by rw [sub_zero],
    or.elim (le_or_gt 0 a)
        (λ anonneg,
            have abs a = a, from abs_of_nonneg anonneg,
            or.inl (by rwa [this] at h)
        )
        (λ aneg,
            have abs a = -a, from abs_of_neg aneg,
            or.inr (by rwa [this] at h)
        )
),
begin
    cases (lt_trichotomy 0 a) with apos aelse,
        {
            cases (lt_trichotomy 0 b) with bpos belse,
                {
                    have aplusbpos : 0 < a + b, from add_pos apos bpos,
                    have absab : abs (a + b) = a + b, by rwa [abs_of_pos],
                    have absb : abs b = b, by rwa [abs_of_pos],
                    have l1 : abs (a + b) - abs b = (a + b) - b, by rw [absab, absb],
                    have l2 : (a + b) - b = a, by linarith,
                    left, by rw [l1, l2]

                },
            cases belse with bzero bneg,
                { cases (l1 (eq.symm bzero)) with isa isminusa,
                { left, exact isa },
                { right, left, exact isminusa },
                },
            have l1 : abs b = -b, from abs_of_neg bneg,
            cases (le_or_gt 0 (a+b)) with abnonneg abneg,
                {
                    have : abs (a + b) = a + b, from abs_of_nonneg abnonneg,
                    have : abs (a+b) - abs b = a + 2*b, from (
                        calc
                        abs (a+b) - abs b = a + b - -b : by rw [l1, this]
                                        ... = a + 2*b : by linarith
                    ),
                    right, right, right, exact this
                },
            have : abs (a + b) = -(a + b), from abs_of_neg abneg,
            have : abs (a+b) - abs b = -a, from (
                calc
                abs (a+b) - abs b = -(a + b) - -b : by rw [l1, this]
                                ... = -a : by linarith
            ),
            right, left, exact this
        },
    cases aelse with azero aneg,
        {
            have : abs (a+b) - abs b = a, from (
                calc
                abs (a + b) - abs b = abs (0+b) - abs b : by rw azero
                                ... = abs b - abs b : by rw zero_add
                                ... = 0 : by rw [sub_self]
                                ... = a : by rw [azero]
            ),
            left, assumption
        },
    {
        cases (lt_trichotomy 0 b) with bpos belse,
            {
                have l1 : abs b = b, from abs_of_pos bpos,
                cases (lt_or_ge 0 (a+b)) with abpos abnonpos,
                    {
                        have : abs (a+b) = a + b, from abs_of_nonneg (le_of_lt abpos),
                        have : abs (a + b) - abs b = a, from (
                            calc
                            abs (a + b) - abs b = a + b - b : by rw [l1, this]
                                            ... = a : by linarith
                        ),
                        left, exact this
                    },
                have : abs (a+b) = -(a + b), from abs_of_nonpos abnonpos,
                have : abs (a + b) - abs b = -a - (2*b), from (
                calc
                    abs (a + b) - abs b = -(a + b) - b : by rw [l1, this]
                                    ... = -a + -b - b : by rw [neg_add]
                                    ... = -a - 2*b : by linarith
                ),
                right, right, left, exact this
            },
        cases belse with bzero bneg,
            { cases (l1 (eq.symm bzero)) with isa isminusa,
              { left, exact isa },
              { right, left, exact isminusa },
            },
        have : a + b < 0, from add_neg aneg bneg,
        have l1 : abs (a + b) = -(a + b), from abs_of_neg this,
        have l2 : abs b = -b, from abs_of_neg bneg,
        have : abs (a + b) - abs b = -a, from (
            calc
            abs (a + b) - abs b = -(a+b) - -b : by rw [l1, l2]
                            ... = -a + -b - -b : by rw [neg_add]
                            ... = -a + (-b - -b) : by rw [add_sub_assoc]
                            ... = -a + 0 : by rw sub_self
                            ... = -a : by rw add_zero
        ),
        right, left, exact this
    }
end

-- (ii)
example :
abs (abs x - 1) = x - 1 ∨
abs (abs x - 1) = -x + 1 ∨
abs (abs x - 1) = -x - 1 ∨
abs (abs x - 1) = x + 1 :=
or.elim (le_or_gt 0 x)
    (λ xnonneg,
        or.elim (le_or_gt 0 (x - 1))
            (λ nonneg,
                have abs (abs x - 1) = x - 1, by rw [abs_of_nonneg xnonneg, abs_of_nonneg nonneg],
                or.inl this
            )
            (λ neg,
                have abs (abs x - 1) = -(x-1), by rw [abs_of_nonneg xnonneg, abs_of_neg neg],
                or.inr $ or.inl (by linarith)
            )
    )
    (λ xneg,
        or.elim (le_or_gt 0 (-x-1))
            (λ nonneg,
                have abs (abs x - 1) = -x-1, by rw [abs_of_neg xneg, abs_of_nonneg nonneg],
                or.inr $ or.inr $ or.inl this
            )
            (λ neg,
                have abs (abs x - 1) = -(-x-1), by rw [abs_of_neg xneg, abs_of_neg neg],
                or.inr $ or.inr $ or.inr (by linarith)
            )
    )

-- (iii)
example :
abs x - abs (x^2) = x - x^2 ∨
abs x - abs (x^2) = -x - x^2 :=
have l1 : 0 ≤ x^2, from pow_two_nonneg x,
or.elim (le_or_gt 0 x)
    (λ xnonneg,
        have abs x - abs (x^2) = x - x^2, by rw [abs_of_nonneg xnonneg, abs_of_nonneg l1],
        or.inl this
    )
    -- if x is negative, abs x - x^2 = -x - x^2
    (λ xneg,
        have abs x - abs (x^2) = -x - x^2, by rw [abs_of_neg xneg, abs_of_nonneg l1],
        or.inr this
    )

-- (iv)
example :
a - abs (a - abs a) = a ∨
a - abs (a - abs a) = 3*a
:=
or.elim (le_or_gt 0 a)
    (λ anonneg,
        have a - abs (a - abs a) = a, from (
            calc
            a - abs (a - abs a) = a - abs (a - a) : by rw [abs_of_nonneg anonneg]
                            ... = a - abs 0 : by rw [sub_self]
                            ... = a : by rw [abs_zero, sub_zero]
        ),
        or.inl this
    )
    (λ aneg,
        have a - abs (a - abs a) = 3*a, from (
            have twoaneg : 2*a < 0, by linarith,
            calc
            a - abs (a - abs a) = a - abs (a - -a) : by rw [abs_of_neg aneg]
                            ... = a - abs (a + a) : by rw [sub_neg_eq_add]
                            ... = a - abs (2*a) : by rw [two_mul]
                            ... = a - -(2*a) : by rw [abs_of_neg twoaneg]
                            ... = a + (2*a) : by rw sub_neg_eq_add
                            ... = 3*a : by linarith
        ),
        or.inr this
    )
