import data.real.basic
import tactic.basic

variables { a b c : ℝ }


-- (a)

noncomputable def numA (b c : ℝ) : ℝ := (-b + real.sqrt (b^2 - 4*c)) / 2
noncomputable def numB (b c : ℝ) : ℝ := (-b - real.sqrt (b^2 - 4*c)) / 2

structure partA (x : ℝ → ℝ → ℝ) :=
(proof : ∀ (b c : ℝ), 0 ≤ b^2 - 4*c → (x b c)^2 + b*(x b c) + c = 0)

noncomputable example : partA numA :=
partA.mk (λ (b : ℝ) (c : ℝ) h,
    calc
        (numA b c)^2 + b*(numA b c) + c = ((-b + real.sqrt (b^2 - 4*c)) / 2) * ((-b + real.sqrt (b^2 - 4*c)) / 2) + b*(numA b c) + c : by rw [pow_two, numA]
        ... = ((-b + real.sqrt (b^2 - 4*c)) * (-b + real.sqrt (b^2 - 4*c))) / (2*2) + b*(numA b c) + c : by rw [div_mul_div]
        ... = (-b + real.sqrt (b^2 - 4*c))^2 / (2*2) + b*(numA b c) + c : by rw [<-pow_two]
        ... = (-b + real.sqrt (b^2 - 4*c))^2 / 4 + b*(numA b c) + c : by norm_num
        ... = ((-b)^2 + 2*(-b * real.sqrt (b^2 - 4*c)) + (real.sqrt (b^2 - 4*c))^2) / 4 + b*(numA b c) + c : by linarith
        ... = (b^2 + 2*(-b * real.sqrt (b^2 - 4*c)) + (b^2 - 4*c)) / 4 + b*(numA b c) + c : by rw [real.sqr_sqrt h, neg_square]
        ... = (2*b^2 - 4*c + 2*-b * real.sqrt (b^2 - 4*c)) / 4 + b*(numA b c) + c : by linarith
        ... = (2*b^2 - 4*c + 2*-b * real.sqrt (b^2 - 4*c)) / 4 + b*((-b + real.sqrt (b^2 - 4*c)) / 2) + c : by rw numA
        ... = 0 : by linarith
)

noncomputable example : partA numB :=
partA.mk (λ (b : ℝ) (c : ℝ) h,
    have (-b - real.sqrt (b^2 - 4*c))^2 = (-b)^2 + (real.sqrt (b^2 - 4*c))^2 - 2*(-b * real.sqrt((b^2)-4*c)), by linarith,
    calc
        (numB b c)^2 + b*(numB b c) + c = ((-b - real.sqrt (b^2 - 4*c)) / 2) * ((-b - real.sqrt (b^2 - 4*c)) / 2) + b*(numB b c) + c : by rw [pow_two, numB]
        ... = ((-b - real.sqrt (b^2 - 4*c)) * (-b - real.sqrt (b^2 - 4*c))) / (2*2) + b*(numB b c) + c : by rw [div_mul_div]
        ... = ((-b - real.sqrt (b^2 - 4*c))^2) / (2*2) + b*(numB b c) + c : by rw [<-pow_two]
        ... = ((-b)^2 + (real.sqrt (b^2 - 4*c))^2 - 2*(-b * real.sqrt((b^2)-4*c))) / (2*2) + b*(numB b c) + c : by rw this
        ... = (b^2 + (b^2 - 4*c) - 2*(-b * real.sqrt((b^2)-4*c))) / (2*2) + b*(numB b c) + c : by rw [real.sqr_sqrt h, neg_square]
        ... = (b^2 + (b^2 - 4*c) - 2*(-b * real.sqrt((b^2)-4*c))) / 4 + b*(numB b c) + c : by norm_num
        ... = (b^2 + (b^2 - 4*c) - 2*(-b * real.sqrt((b^2)-4*c))) / 4 + b*((-b - real.sqrt (b^2 - 4*c)) / 2) + c : by rw [numB]
        ... = 0 : by linarith

)

-- (b)

def part_b : ∀ (x : ℝ), b^2 - 4*c < 0 → 0 < x^2 + b*x + c :=
λ x h,
have completeTheSquare : x^2 + b*x + c = (x + (b/2))^2 + (c - (b^2)/4), from (
    have l1 : (x + (b/2))^2 = x^2 + (b^2)/4 + b*x, by ring,
    have (x + (b/2))^2 + (c - (b^2)/4) = x^2 + (b^2)/4 + b*x + (c - (b^2)/4), by rw [<-l1],
    by linarith only [this]
),
have l1 : 0 < (c - (b^2)/4), by linarith only [h],
have l2 : 0 ≤ (x + (b/2))^2, from pow_two_nonneg (x + b / 2),
have 0 < (x + (b/2))^2 + (c - (b^2)/4), from lt_add_of_le_of_pos l2 l1,
by rwa [←completeTheSquare] at this

-- (c)

def part_c : ∀ (x y : ℝ), ¬(x = 0 ∧ y = 0) → 0 < x^2 + x*y + y^2 :=
λ x y nonZero,
have x ≠ 0 ∨ y ≠ 0, from not_and_distrib.mp nonZero,
or.elim this
    (λ xNonzero,
        have 0 < x^2, from pow_two_pos_of_ne_zero x xNonzero,
        have x^2 - 4*(x^2) < 0, by linarith only [this],
        have 0 < y^2 + x*y + x^2, from @part_b x (x^2) y this,
        by linarith only [this]
    )
    (λ yNonzero,
        have 0 < y^2, from pow_two_pos_of_ne_zero y yNonzero,
        have y^2 - 4*(y^2) < 0, by linarith only [this],
        have 0 < x^2 + y*x + y^2, from @part_b y (y^2) x this,
        by rwa [mul_comm y x] at this
    )

-- (d)

def part_d : ∀ (x y α : ℝ), 0 < α → α < (real.sqrt 4) → ¬(x = 0 ∧ y = 0) → 0 < x^2 + α*x*y + y^2 :=
λ x y α alphaPos alphaLtSqrt4 nonZero,
have real.sqrt 4 * real.sqrt 4 = real.sqrt (4*4), from eq.symm $ real.sqrt_mul (show 0 <= (4 : real), by norm_num) 4,
have lsqrt : real.sqrt 4 * real.sqrt 4 = 4, by rwa [this, real.sqrt_mul_self (show 0 <= (4:real), by norm_num)],
have α * α < real.sqrt 4 * real.sqrt 4, from mul_lt_mul alphaLtSqrt4 (le_of_lt alphaLtSqrt4) alphaPos (real.sqrt_nonneg 4),
have lsq : α^2 < 4, by rwa [<-pow_two, lsqrt] at this,
have x ≠ 0 ∨ y ≠ 0, from not_and_distrib.mp nonZero,
or.elim this
    (λ xNonzero,
        have α^2 * x^2 < 4*x^2, from mul_lt_mul lsq (le_of_eq rfl) (pow_two_pos_of_ne_zero x xNonzero) (by norm_num),
        have (α*x)^2 < 4*x^2, by linarith,
        have (α*x)^2 - 4*(x^2) < 0, from sub_lt_zero.mpr this,
        have 0 < y^2 + (α*x)*y + x^2, from @part_b (α*x) (x^2) y this,
        by linarith only [this]
    )
    (λ yNonzero,
        have α^2 * y^2 < 4*y^2, from mul_lt_mul lsq (le_of_eq rfl) (pow_two_pos_of_ne_zero y yNonzero) (by norm_num),
        have (α*y)^2 < 4*y^2, by linarith,
        have (α*y)^2 - 4*(y^2) < 0, from sub_lt_zero.mpr this,
        have 0 < x^2 + (α*y)*x + y^2, from @part_b (α*y) (y^2) x this,
        by linarith only [this]
    )

-- (e)

-- TODO
