import data.real.basic
import tactic.basic
import tactic.suggest

open real (sqrt)

variables { a b c x y : ℝ }

-- (i)
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
    or.elim3 (lt_trichotomy 0 a)
        (λ apos,
            have abs a = a, from abs_of_pos apos,
            or.inl (by rwa [this] at h)
        )
        (λ azero,
            have abs a = a, by rwa [←azero, abs_zero],
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
example : abs (abs x - 1) = 1 := sorry

-- (iii)
example :
abs x - abs (x^2) = x - x^2 ∨
abs x - abs (x^2) = x + x^2 :=
have 0 ≤ x^2, from pow_two_nonneg x,
have l1: abs (x^2) = x^2, from abs_of_nonneg this,
-- if x is negative, abs x - x^2 = -x - x^2
or.elim (lt_or_ge 0 x)
    sorry
    sorry

-- (iv)
example :
a - abs (a - abs a) = 1 :=
sorry
