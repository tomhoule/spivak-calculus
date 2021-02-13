import data.real.sqrt

variables { x : ℝ }

-- (i)

example : abs (x - 3) = 8 ↔ x = 11 ∨ x = -5 :=
begin
split,
{
    intro h,
    rcases (le_or_gt 0 (x-3)) with hNonneg | hNeg,
    {
        have : abs (x - 3) = (x - 3), from abs_of_nonneg hNonneg,
        left, linarith
    },
    have : abs (x-3) = 3 - x, simp only [abs_of_neg hNeg, neg_sub],
    right, linarith
},
intro h,
rcases h with xEleven | xNegFive,
{
    have : abs (x - 3) = x - 3, exact abs_of_pos (by linarith only [xEleven]),
    linarith only [this, xEleven]
},
have : abs (x-3) = -(x-3), exact abs_of_nonpos (by linarith only [xNegFive]),
linarith only [this, xNegFive]
end

-- (ii)

def self_or_neg_self_of_abs (x : ℝ) : (0 ≤ x ∧ abs x = x) ∨ (0 ≥ x ∧ abs x = -x) :=
or.elim (le_or_gt 0 x)
    (λ hNonneg, or.inl ⟨hNonneg, abs_of_nonneg hNonneg⟩)
    (λ hNeg, or.inr ⟨le_of_lt hNeg, abs_of_neg hNeg⟩)

example : abs (x-3) < 8 ↔ x < 11 ∧ x > -5 :=
begin
split,
{
    intro h,
    rcases (self_or_neg_self_of_abs (x-3)) with hNonneg | hNeg,
    {
        constructor, linarith, linarith,
    },
    constructor, linarith, linarith
},
intro h,
rcases h with ⟨xLtEleven, xGtNegFive⟩,
rcases (self_or_neg_self_of_abs (x-3)) with ⟨_, hAbs⟩ | ⟨_, hAbs⟩,
{ linarith only [hAbs, xLtEleven, xGtNegFive] },
linarith only [hAbs, xGtNegFive]
end

-- (iii)

example : abs (x+3) < 2 ↔ x < -1 ∧ x > -5 :=
begin
split,
{
    intro h,
    rcases (le_or_gt 0 (x+3)) with hNonneg | hNeg,
    {
        have : abs (x + 3) = x + 3, from abs_of_nonneg hNonneg,
        have : x + 3 < 2, rwa [this] at h,
        constructor, linarith, linarith
    },
    have : abs (x+3) = -x + -3, simp only [abs_of_neg hNeg, neg_add],
    constructor, linarith, linarith
},
intro h,
rcases h with ⟨xLt, xGt⟩,
have h' : (x + 3) > -2, linarith only [xGt],
rcases (le_or_gt (x+3) 0) with hLe | hGt,
{
    have : abs (x+3) = -(x+3), exact abs_of_nonpos (by linarith only [hLe]),
    linarith only [this, h', xLt]
},
have : abs (x + 3) = x + 3, exact abs_of_nonneg (by linarith only [hGt]),
linarith only [this, h', xLt]
end

-- (iv)

example : x < 1 ∨ 2 < x ↔ 1 < abs (x - 1) + abs (x - 2) :=
begin
    split,
    {
        intros h,
        rcases h with hLt | hGt,
        {
            have : x - 1 < 0, linarith only [hLt],
            have left : 0 < abs (x-1), exact abs_pos_of_neg this,
            have : abs (x-2) = -(x-2), from abs_of_neg (by linarith only [this]),
            have right : 1 < abs (x - 2), linarith only [this, hLt],
            linarith only [hLt, left, right]
        },
        have leftAbs : abs (x-1) = x-1, exact abs_of_pos (by linarith only [hGt]),
        have right : 0 < x - 2, linarith only [hGt],
        linarith only [hGt, leftAbs, (abs_of_pos right)]
    },
    -- Right part of the iff
    intro h,
    rcases (lt_or_ge x 1) with xLt | xGe,
    {
        have left : abs (x - 1) = -(x - 1), exact (abs_of_nonpos $ by linarith only [xLt]),
        have right : abs (x - 2) = -(x-2), exact (abs_of_nonpos $ by linarith only [xLt]),
        left, linarith
    },
    have left : abs (x - 1) = x - 1, exact (abs_of_nonneg $ by linarith only [xGe]),
    rcases (le_or_gt x 2) with xLe | xGt,
    {
        have right : abs (x - 2) = -(x-2), exact (abs_of_nonpos $ by linarith only [xLe]),
        right, linarith only [h, right, left]
    },
    have right : abs (x - 2) = x - 2, exact (abs_of_nonneg $ by linarith only [xGt]),
    right, linarith
end

-- (v)

example : ¬(abs (x - 1) + abs (x + 1) < 2) :=
begin
    intro h,
    rcases (le_or_gt x (-1)) with xLt | xGe,
    {
        have left : abs (x - 1) = -(x-1), exact abs_of_nonpos (by linarith only [xLt]),
        have right : abs (x + 1) = -(x + 1), exact abs_of_nonpos (by linarith only [xLt]),
        have : abs (x - 1) + abs (x + 1) ≥ 2, linarith only [left, right, xLt],
        exact (not_lt_of_ge this) h
    },
    have right : abs (x + 1) = x + 1, exact abs_of_nonneg (by linarith only [xGe]),
    rcases (le_or_gt x 1) with xLeOne | xGtOne,
    {
        have left : abs (x - 1) = -(x-1), exact abs_of_nonpos (by linarith only [xLeOne]),
        have : abs (x - 1) + abs (x + 1) ≥ 2,
        calc
        abs (x - 1) + abs (x + 1)   = -(x-1) + (x+1) : by rw [left, right]
                                ... ≥ 2 : by linarith,
        exact (not_lt_of_ge this) h
    },
    have left : abs (x - 1) = (x-1), exact abs_of_pos (by linarith only [xGtOne]),
    have : abs (x - 1) + abs (x + 1) = 2*x, linarith only [left, right, xGe],
    have : abs (x - 1) + abs (x + 1) > 2, linarith only [this, xGtOne],
    exact (not_lt_of_gt this) h
end

-- (vi)

example : ¬(abs (x-1) + abs (x+1) < 1) :=
begin
    intro h,
    rcases (le_or_gt x 1) with xLe | xGt,
    {
        have left : abs (x-1) = -(x-1), exact abs_of_nonpos (by linarith only [xLe]),
        rcases (le_or_gt x (-1)) with xLe' | xGt',
        {
            have right : abs (x+1) = -(x+1), exact abs_of_nonpos (by linarith only [xLe']),
            linarith
        },
        have right : abs (x + 1) = x+1, exact abs_of_nonneg (by linarith only [xGt']),
        linarith only [left, right, h]
    },
    have left : abs (x-1) = x-1, exact abs_of_nonneg (by linarith only [xGt]),
    have right : abs (x+1) = x+1, exact abs_of_nonneg (by linarith only [xGt]),
    linarith
end

-- (vii)

example : abs (x-1) * abs (x+1) = 0 ↔ x = 1 ∨ x = -1 :=
begin
    split,
    {
        intro h,
        rcases (lt_trichotomy x (-1)) with xLt | xEq | xGt,
        {
            have : (x-1) < 0, linarith only [xLt],
            have left : abs (x-1) > 0, exact abs_pos_of_neg this,
            have : (x+1) < 0, linarith only [xLt],
            have right : abs (x+1) > 0, exact abs_pos_of_neg this,
            have : abs (x-1) * abs (x+1) > 0, exact mul_pos left right,
            have : abs (x-1) * abs (x+1) ≠ 0, exact ne_of_gt this,
            contradiction
        },
        { right, assumption },
        {
            rcases (lt_trichotomy x 1) with xLt | xEq | xGt',
            {
                have : (x-1) < 0, linarith only [xLt],
                have left : abs (x-1) > 0, exact abs_pos_of_neg this,
                have : (x+1) > 0, linarith only [xGt],
                have right : abs (x+1) > 0, exact abs_pos_of_pos this,
                have : abs (x-1) * abs (x+1) > 0, exact mul_pos left right,
                have : abs (x-1) * abs (x+1) ≠ 0, exact ne_of_gt this,
                contradiction
            },
            { left, assumption },
            {
                have : (x-1) > 0, linarith only [xGt'],
                have left : abs (x-1) > 0, exact abs_pos_of_pos this,
                have : (x+1) > 0, linarith only [xGt],
                have right : abs (x+1) > 0, exact abs_pos_of_pos this,
                have : abs (x-1) * abs (x+1) > 0, exact mul_pos left right,
                have : abs (x-1) * abs (x+1) ≠ 0, exact ne_of_gt this,
                contradiction
            }
        }
    },
    intro h,
    rcases h with xOne | xNegOne,
    {
        have : abs (x-1) = 0, rw [(show x-1 = 0, by linarith only [xOne]), abs_zero],
        rw [this, zero_mul]
    },
    have : abs (x+1) = 0, rw [(show x+1 = 0, by linarith only [xNegOne]), abs_zero],
    rw [this, mul_zero]
end

-- (viii)

open real (sqrt)

-- def viii_helper1 : abs (x-1) = abs (x+2) / 3 → x = 5/2 ∨ x = 1/4 :=
-- begin
--     intro h,
--     rcases (le_or_gt 0 (x-1)) with hNonneg | hNeg;
--     rcases (le_or_gt 0 (x+2)) with hNonneg' | hNeg',
--     {
--         have : x - 1 = (x + 2) / 3, by rwa [abs_of_nonneg hNonneg, abs_of_nonneg hNonneg'] at h,
--         left, show x = 5/2, by linarith only [this]
--     },
--     {
--         have left : 0 ≤ x, by linarith,
--         have right : 0 > x, by linarith,
--         apply false.elim,
--         apply absurd,
--         exact left,
--         exact not_le.mpr right
--     },
--     {
--         have : -(x-1) = (x+2)/3, by rwa [abs_of_neg hNeg, abs_of_nonneg hNonneg'] at h,
--         right, show x = 1/4, by linarith only [this],
--     },
--     {
--         have : -(x-1) = -(x+2)/3, by rwa [abs_of_neg hNeg, abs_of_neg hNeg'] at h,
--         left, show x = 5/2, by linarith only [this],
--     }
-- end

example :
    (abs (x - 1) * abs (x + 2) = 3) ↔
    x = (sqrt 21 - 1) / 2 ∨ x = -(sqrt 21 + 1)/2 :=
begin
    split,
    {
        intros h,
        have sqrtFour : sqrt 4 = 2, by rw [show 4 = (2:real)^2, by norm_num, real.sqrt_sqr (show (0:real) ≤ 2, by norm_num)],
        rcases (le_or_gt 0 (x-1)) with hNonneg | hNeg;
        rcases (le_or_gt 0 (x+2)) with hNonneg' | hNeg',
        {
            have h' : (x + 1/2) * (x + 1/2) = x^2 + x + 1/4, by linarith,
            have h'' : 0 ≤ (x + 1/2), by linarith only [hNonneg],
            have : (x-1) * (x+2) = 3, by rwa [abs_of_nonneg hNonneg, abs_of_nonneg hNonneg'] at h,
            have : (x + 1/2) * (x + 1/2) - 1/4 = 5, by linarith only [this],
            have : (x + 1/2)^2 = 21/4, by linarith only [this, pow_two (x + 1/2)],
            have : sqrt ((x+1/2)^2) = sqrt (21/4), from congr_arg sqrt this,
            have : (x+1/2) = sqrt 21 / 2, by rwa [real.sqrt_sqr h'', real.sqrt_div (show (0:real) <= 21, by norm_num), sqrtFour] at this,
            left, show x = (sqrt 21 - 1)/ 2, by linarith only [this]
        },
        {
            have xNeg : 0 > x, by linarith only [hNeg'],
            have xNonneg : 0 ≤ x, by linarith only [hNonneg],
            exact absurd xNeg (not_lt.mpr xNonneg)
        },
        {
            have : -(x-1) * (x+2) = 3, by rwa [abs_of_neg hNeg, abs_of_nonneg hNonneg'] at h,
            have : (x+1/2)^2 = -3/4, by linarith only [this, pow_two (x+1/2)],
            have hNeg : (x+1/2)^2 < 0, by linarith only [this],
            have hNonneg : (x+1/2)^2 ≥ 0, from pow_two_nonneg (x+1/2),
            exact absurd hNeg (not_lt.mpr hNonneg)
        },
        have h' : x + 1/2 < 0, by linarith only [hNeg'],
        have : -(x-1) * -(x+2) = 3, by rwa [abs_of_neg hNeg, abs_of_neg hNeg'] at h,
        have : (x + 1/2)^2 = 21/4, by linarith only [this, pow_two (x + 1/2)],
        have : sqrt ((x+1/2)^2) = sqrt (21/4), from congr_arg sqrt this,
        have : abs (x+1/2) = sqrt 21 / 2, by rwa [pow_two, real.sqrt_mul_self_eq_abs, real.sqrt_div (show (0:real) <= 21, by norm_num), sqrtFour] at this,
        have : -(x+1/2) = sqrt 21 / 2, by rwa [abs_of_neg h'] at this,
        right, linarith only [this]
    },
    intro h,
    have : sqrt 16 < sqrt 21, from (real.sqrt_lt (show (0:real) ≤ 16, by norm_num)).elim_right (by norm_num),
    have : 4 < sqrt 21, by rwa [(show 16 = (4:real)^2, by norm_num), real.sqrt_sqr (show (0:real) ≤ 4, by norm_num)] at this,
    have helper1 : (sqrt 21 - 3) * (sqrt 21 + 3) = 12, from (
        have h1 : (0:real) <= 21, by norm_num,
        calc
        (sqrt 21 - 3) * (sqrt 21 + 3) = sqrt 21 * sqrt 21 - 9 : by linarith
        ... = 21 - 9 : by rwa [<-real.sqrt_mul, real.sqrt_mul_self h1]
        ... = 12 : by norm_num
    ),
    rcases h with h | h,
    {
        have left : abs (x - 1) = x - 1, from abs_of_pos (by linarith),
        have right : abs (x + 2) = x + 2, from abs_of_pos (by linarith),
        calc
        abs (x-1) * abs (x+2) = (x-1) * (x+2) : by rwa [left, right]
        ... = ((sqrt 21 - 1)/2 -1) * ((sqrt 21 - 1)/2 + 2) : by rw [h]
        ... = ((sqrt 21 -3)/2) * ((sqrt 21 + 3)/2) : by linarith
        ... = ((sqrt 21 - 3) * (sqrt 21 + 3)) / (2*2) : div_mul_div (sqrt 21 - 3) 2 (sqrt 21 + 3) 2
        ... = ((sqrt 21 - 3) * (sqrt 21 + 3)) / 4 : by norm_num
        ... = 12 / 4 : by rw [helper1]
        ... = 3 : by norm_num
    },
    have left : abs (x-1) = -(x-1), from abs_of_neg (by linarith),
    have right : abs (x+2) = -(x+2), from abs_of_neg (by linarith),
    calc
    abs (x-1) * abs (x+2) = -(x-1) * -(x+2) : by rwa [left, right]
    ... = -((-(sqrt 21 + 1)/2) - 1) * -((-(sqrt 21 + 1)/2) + 2) : by rw [h]
    ... = ((-(sqrt 21 + 1)/2) - 1) * ((-(sqrt 21 + 1)/2) + 2) : neg_mul_neg (-(sqrt 21 + 1) / 2 - 1) (-(sqrt 21 + 1) / 2 + 2)
    ... = ((-sqrt 21 - 3)/2) * ((-sqrt 21 + 3)/2) : by linarith
    ... = ((-sqrt 21 - 3) * (-sqrt 21 + 3)) / (2*2) : div_mul_div (-sqrt 21 - 3) 2 (-sqrt 21 + 3) 2
    ... = ((-sqrt 21 - 3) * (-sqrt 21 + 3)) / 4 : by norm_num
    ... = ((sqrt 21 - 3) * (sqrt 21 + 3)) / 4 : by linarith
    ... = 12 / 4 : by rw [helper1]
    ... = 3 : by norm_num
end
