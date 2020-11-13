import data.real.basic
import chap1.problem_21
import chap1.problem_22

variables { x x0 y y0 ε : ℝ }

-- example : abs (x*y0-x0*y) * abs (1/(y*y0)) = abs (x/y - x0/y0) :=
-- begin
-- have : abs (x-x0) * abs (1/y - 1/y0) = abs ((x-x0) * (1/y - 1/y0)), by refine (eq.symm $ abs_mul _ _),
-- have y0Nonzero : y0 ≠ 0, from sorry,
-- have yNonzero : y ≠ 0, from sorry,
-- have : (x*y0-x0*y) * (1/(y*y0)) = (x*y0)/(y*y0) - (x0*y)/(y*y0), by ring,
-- have : (x*y0-x0*y) * (1/(y*y0)) = x/y - x0/y0, {
--     conv at this {
--         to_rhs,
--         rw mul_div_mul_right x y y0Nonzero,
--         rw mul_comm y y0,
--         rw mul_div_mul_right x0 y0 yNonzero
--     },
--     assumption
-- },
-- rwa [<-abs_mul, this]
-- end

example :
    y0 ≠ 0 →
    abs (y-y0) < min (abs y0/2) ((ε / (2 * (abs x0 + 1))*(abs y0)^2)/2) →
    abs (x - x0) < min (ε / (2 * (abs y0⁻¹ + 1))) 1 →
    y ≠ 0 ∧ abs (x/y - x0/y0) < ε
:=
begin
intros y0Nonzero diffYs diffXs,
rcases problem_22 y0Nonzero diffYs with ⟨yNonzero, h⟩,
split, exact yNonzero,
refine problem_21 diffXs _,
rwa [<-norm_num.inv_div_one y, <-norm_num.inv_div_one y0] at h
end
