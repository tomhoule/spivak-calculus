import data.real.basic

variables { x y : ℝ }

def problem_16_i : ((x+y)^2 = x^2 + y^2) ↔ x = 0 ∨ y = 0 :=
begin
    split,
    {
        intro h,
        rcases (em (0 = x)) with xZero | xNonzero,
        { left, exact eq.symm xZero },
        right,
        have : (x+y)^2 = x^2 + 2*x*y + y^2, by linarith,
        have : x^2 + 2*x*y + y^2 = x^2 + y^2, by rwa [this] at h,
        have : x*y = 0, by linarith only [this],
        have : x = 0 ∨ y = 0, from zero_eq_mul.mp (eq.symm this),
        rcases this with xZero | yZero,
        { apply absurd, exact xZero, exact ne.symm xNonzero },
        exact yZero
    },
    intro h,
    rcases h with xZero | yZero,
    {
        have : (x + y)^2 = y^2, by rw [xZero, zero_add],
        have : x^2 + y^2 = y^2, by rw [xZero, zero_pow two_pos, zero_add],
        cc
    },
    have : (x + y)^2 = x^2, by rw [yZero, add_zero],
    have : x^2 + y^2 = x^2, by rw [yZero, zero_pow two_pos, add_zero],
    cc
end

example : ((x+y)^3 = x^3 + y^3) ↔ x = 0 ∨ y = 0 ∨ x = -y :=
begin
    split,
    {
        intro h,
        have : x^3+y^3 = (x + y) * (x^2 - (x * y) + y^2), by linarith,
        have : (x+y)^3 = (x + y) * (x + y)^2, by ring,
        have l1 : (x + y) * (x^2 - (x * y) + y^2) = (x + y) * (x + y)^2, by cc,
        rcases (em (x = -y)) with hXNegY | hXYDiffer,
        { right, right, exact hXNegY },
        have sumNonZero : x + y ≠ 0, { intro h, have : x = -y, by linarith, contradiction },
        have : (x^2 - (x * y) + y^2) = (x + y)^2, from (mul_right_inj' sumNonZero).mp l1,
        have : (x+y)^2 = x^2+y^2, by linarith only [this],
        rcases (problem_16_i.mp this) with hL | hR,
        left, exact hL, right, left, exact hR
    },
    rintro (xZero | yZero | hOpp),
    {
        have : (x + y)^3 = y^3, by rw [xZero, zero_add],
        have : x^3 + y^3 = y^3, by rw [xZero, zero_pow (show 0 < 3, by norm_num), zero_add],
        cc
    },
    {
        have : (x + y)^3 = x^3, by rw [yZero, add_zero],
        have : x^3 + y^3 = x^3, by rw [yZero, zero_pow (show 0 < 3, by norm_num), add_zero],
        cc
    },
    have : (x + y)^3 = 0, by rw [hOpp, neg_add_self, zero_pow (show 0<3, by norm_num)],
    have : x^3 + y^3 = 0, from (
        calc
        x^3 + y^3 = (-y)^3 + y^3 : by rw [hOpp]
        ... = 0 : by linarith
    ),
    cc
end

-- (b)

def problem16_b : ¬(x = 0 ∧ y = 0) ↔ 4*x^2 + 6*x*y + 4*y^2 > 0 :=
begin
split,
{
    intro hNonzero,
    have h1 : 4*x^2 + 6*x*y + 4*y^2 = x^2 + y^2 + 3 * (x + y)^2, by linarith,
    have : 0 ≤ (x+y)^2, from pow_two_nonneg (x+y),
    have h2 : 0 ≤ 3 * (x+y)^2, from mul_nonneg (by norm_num) this,
    have h3 : 0 < x^2 + y^2, {
        rcases (not_and_distrib.mp hNonzero) with xNonzero | yNonzero,
        {
            have : 0 < x^2, from pow_two_pos_of_ne_zero x xNonzero,
            exact add_pos_of_pos_of_nonneg this (pow_two_nonneg y)
        },
        have : 0 < y^2, from pow_two_pos_of_ne_zero y yNonzero,
        exact add_pos_of_nonneg_of_pos (pow_two_nonneg x) this
    },
    have : 0 < x^2 + y^2 + 3 * (x + y)^2, from add_pos_of_pos_of_nonneg h3 h2,
    by rwa [<-h1] at this
},
rintros (h) (⟨xZero, yZero⟩),
have l1 : x^2 = 0, by rw [xZero, zero_pow two_pos],
have l2 : y^2 = 0, by rw [yZero, zero_pow two_pos],
have : 4*x^2 + 6*x*y + 4*y^2 = 0, by norm_num [h, l1, l2, yZero, xZero],
apply absurd,
exact this,
exact ne_of_gt h
end

-- (c)

example : ((x+y)^4 = x^4 + y^4) ↔ x = 0 ∨ y = 0 :=
begin
split,
{
    intro h,
    have : (x+y)^4 = x^4+4*x^3*y+6*x^2*y^2+4*x*y^3+y^4, by ring,
    have : (x+y)^4 = (x^4 + y^4) + (x*y) * (4*x^2 + 6*x*y + 4*y^2), by linarith only [this],
    have : (x*y) * (4*x^2 + 6*x*y + 4*y^2) = 0, by linarith only [this, h],
    have : (x*y) = 0 ∨ (4*x^2 + 6*x*y + 4*y^2) = 0, from zero_eq_mul.mp (eq.symm this),
    rcases this with hL | hR,
    {
        exact zero_eq_mul.mp (eq.symm hL)
    },
    -- rcases y and y are zero
    have : 0 ≤ x^2, from pow_two_nonneg x,
    have : 0 ≤ y^2, from pow_two_nonneg y,
    have : 0 ≤ (x + y)^2, from pow_two_nonneg (x + y),

    have : x^2 + y^2 + 3 * (x + y)^2 = 0, by linarith only [hR],
    have : 0 ≥ 4*x^2 + 6*x*y + 4*y^2, from (eq.symm hR).ge,
    have : ¬(4*x^2 + 6*x*y + 4*y^2 > 0), from not_lt.mpr this,
    have : (x = 0 ∧ y = 0), from not_imp_comm.mp problem16_b.mp this,
    left, exact this.left
},
rintro (xZero | yZero),
{
    have : (x+y)^4 = y^4, by rw [xZero, zero_add],
    have : x^4 + y^4 = y^4, by rw [xZero, zero_pow (show 0 < 4, by norm_num), zero_add],
    cc
},
have : (x+y)^4 = x^4, by rw [yZero, add_zero],
have : x^4 + y^4 = x^4, by rw [yZero, zero_pow (show 0 < 4, by norm_num), add_zero],
cc,
end

-- (d)

def abs_eq_abs' : abs x = abs y → x = y ∨ x = -y :=
assume h,
have h1 : x = abs y ∨ x = -(abs y), from (abs_eq $ abs_nonneg y).mp h,
or.elim (le_or_gt 0 y)
    (λ yNonneg,
        by rwa [abs_of_nonneg yNonneg] at h1
    )
    (λ yNeg,
        have x = -y ∨ x = - -y, by rwa [abs_of_neg yNeg] at h1,
        have x = -y ∨ x = y, by rwa [neg_neg] at this,
        or.swap this
    )

example : ((x+y)^5 = x^5+y^5) ↔ x = 0 ∨ y = 0 ∨ x = -y :=
begin
split,
{
    intro h,
    have : (x+y)^5 = x^5+5*x^4*y+10*x^3*y^2+10*x^2*y^3+5*x*y^4+y^5, by linarith,
    have : x^5+y^5 = x^5 + y^5 + (5*x^4*y+10*x^3*y^2+10*x^2*y^3+5*x*y^4), by linarith only [h, this],
    have : (x*y) * (5*x^3+10*x^2*y+10*x*y^2+5*y^3) = 0, by linarith only [this],
    have : (x*y) = 0 ∨ (5*x^3+10*x^2*y+10*x*y^2+5*y^3) = 0, from zero_eq_mul.mp (eq.symm this),
    rcases this with leftZero | rightZero,
    {
        rcases (zero_eq_mul.mp (eq.symm leftZero)),
        { left, assumption },
        right, left, assumption,
    },
    have l1 : x^3 + 2*x^2*y + 2*x*y^2 + y^3 = 0, by linarith only [rightZero],
    have l2 : (x + y)^3 = x^3 + y^3 + 3*x^2*y + 3*x*y^2, by ring,
    -- Subtract l1 from l2, since we know the left side of l1 = 0.
    have : (x+y)^3 = x^2*y + x*y^2, by linarith only [l1, l2],
    have : (x+y)^3 = (x*y)*(x+y), by linarith only [this],
    have : (x^2 + x*y + y^2) * (x+y) = 0, by linarith only [this],
    have : (x^2 + x*y + y^2) = 0 ∨ (x+y) = 0, from zero_eq_mul.mp (eq.symm this),
    rcases this with leftZero | rightZero,
    {
        rcases (em (x = 0)) with xZero | xNonzero,
        left, exact xZero,
        rcases (em (y = 0)) with yZero | yNonzero,
        right, left, exact yZero,
        have absXPos : abs x > 0, from abs_pos_iff.mpr xNonzero,
        have absYPos : abs y > 0, from abs_pos_iff.mpr yNonzero,
        have xSqPos : x^2 > 0, from pow_two_pos_of_ne_zero x xNonzero,
        have ySqPos : y^2 > 0, from pow_two_pos_of_ne_zero y yNonzero,
        rcases (lt_trichotomy (abs x) (abs y)) with hLt | hEq | hGt,
        swap,
        {
            have : (x = y) ∨ (x = -y), from abs_eq_abs' hEq,
            rcases this with hEq | hOpp,
            swap, right, right, exact hOpp,
            have : x * y = x^2, by conv {
                to_lhs,
                rw <-hEq,
                rw <-pow_two
            },
            linarith,
        },
        all_goals {
          suffices : (x^2 + x*y + y^2) > 0, { apply absurd, exact leftZero, exact (ne_of_gt this) },
        },
        {
            have : abs x * abs y < abs y * abs y, from (mul_lt_mul_right absYPos).mpr hLt,
            have : abs (x*y) < y^2, by rwa [<-abs_mul x y, <-abs_mul y y, abs_mul_self y, <-pow_two y] at this,
            rcases (le_or_gt 0 (x*y)) with hLe | hGt,
            {
                have : (x*y) + y^2 > 0, by linarith [abs_of_nonneg hLe, this],
                linarith
            },
            have : (x*y) + y^2 > 0, by linarith [abs_of_neg hGt, this],
            linarith
        },
        have : abs x * abs y < abs x * abs x, from (mul_lt_mul_left absXPos).mpr hGt,
        have : abs (x*y) < x^2, by rwa [<-abs_mul x y, <-abs_mul x x, abs_mul_self x, <-pow_two x] at this,
        rcases (le_or_gt 0 (x*y)) with hLe | hGt,
        {
            have : x^2 + (x*y) > 0, by linarith [abs_of_nonneg hLe],
            linarith
        },
        have : x^2 + (x*y) > 0, by linarith [abs_of_neg hGt],
        linarith
        -- rcases (lt_trichotomy x y) with xLt | xEq | xGt,
        -- swap,
        -- {
        --     rcases (em (x = 0)) with xZero | xNonzero,
        --     { left, exact xZero },
        --     have xSqPos : x^2 > 0, from pow_two_pos_of_ne_zero x xNonzero,
        --     have ySqPos : y^2 > 0, by rwa [xEq] at xSqPos,
        --     have ySqPos : x*y = x^2, by conv {
        --         to_lhs,
        --         rw <-xEq,
        --         rw <-pow_two
        --     },
        --     have : x^2 + x*y + y^2 > 0, by linarith,
        --     apply absurd, exact leftZero, exact (ne_of_gt this)
        -- },
        -- sorry,
        -- sorry
        -- rcases (lt_trichotomy 0 x) with xPos | xZero | xNeg;
        -- rcases (lt_trichotomy 0 y) with yPos | yZero | yNeg,
        -- any_goals { left, exact (eq.symm xZero) },
        -- any_goals { right, left, exact (eq.symm yZero) },
        -- all_goals {
        --     have xNonzero : x ≠ 0, by linarith,
        --     have yNonzero : y ≠ 0, by linarith,
        --     have xSqPos : x^2 > 0, from pow_two_pos_of_ne_zero x xNonzero,
        --     have ySqPos : y^2 > 0, from pow_two_pos_of_ne_zero y yNonzero,
        -- },
        -- any_goals {
        --     have : 0 < x*y, by { exact mul_pos xPos yPos <|> exact mul_pos_of_neg_of_neg xNeg yNeg },
        --     linarith [add_pos xSqPos this],
        --     done
        -- },
        -- all_goals {
        --     have mulNeg : 0 > x*y, by { exact mul_neg_of_pos_of_neg xPos yNeg <|> exact mul_neg_of_neg_of_pos xNeg yPos },
        -- },
        -- {
        --     rcases (le_or_gt (abs x) (abs y)) with hLe | hGt,
        --     { sorry },
        --     sorry
        -- },
        -- sorry,
    },
    right, right, linarith only [rightZero]
},
rintro (xZero | yZero | xNegY),
{
    have t1 : x + y = y, by rw [xZero, zero_add],
    have t2 : x^5 = 0, by rw [xZero, zero_pow (show (0:nat) < 5, by norm_num)],
    rw [t1, t2, zero_add]
},
{
    have t1 : x + y = x, by rw [yZero, add_zero],
    have t2 : y^5 = 0, by rw [yZero, zero_pow (show 0 < 5, by norm_num)],
    rw [t1, t2, add_zero]
},
have t1 : (x+y)^5 = 0, by rw [xNegY, neg_add_self, zero_pow (show 0 < 5, by norm_num)],
have t2 : x^5 + y^5 = 0, by { rw [xNegY], linarith },
cc
end
