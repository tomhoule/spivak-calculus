import data.real.basic

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
rcases (self_or_neg_self_of_abs (x-3)) with hNonneg | hNonpos,
{ sorry },
sorry
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

-- Divide both sides by 3, then compute inverses.
example : abs (x - 1) * abs (x + 2) = 3 ↔ x < 1 :=
begin
    split,
    {
        intro h,
        rcases (lt_trichotomy x 1) with xLt | xEq | xGt,
        {
            have left : abs (x-1) = -(x - 1), exact (abs_of_neg $ by linarith only [xLt]),
            -- have right : abs (x+2) = -(x + 2), exact (abs_of_neg $ by linarith only [xLt]),
            -- have : (x - 1) * (x + 2) = 3, by rwa [left, right] at h,
            sorry
        },
        {
            have : abs (x-1) = 0, rw [(show x-1 = 0, by linarith only [xEq]), abs_zero],
            have : abs (x - 1) * abs (x + 2) = 0, rw [this, zero_mul],
            linarith only [this, h]
        },
        have left : abs (x-1) = x - 1, exact (abs_of_pos $ by linarith only [xGt]),
        have right : abs (x+2) = x + 2, exact (abs_of_pos $ by linarith only [xGt]),
        have : (x - 1) * (x + 2) = 3, by rwa [left, right] at h,
        have : x^2 + x = 5, by linarith only [this],
        sorry
     },
    intro h,
    sorry
end
