import data.real.basic

variables { x y : ℝ }

def helper1 : (x-y)^2 = x^2 - 2*x*y + y^2 := by linarith

example : 23/8 ≤ 2*x^2 - 3*x + 4 :=
have x^2 - 2*x*(3/4) + (3/4)^2 = (x - (3/4))^2, by rw [helper1],
have 2 * (x - (3/4))^2 = 2*x^2 - 3*x + 2*(3/4)^2, by linarith only [this],
have 2 * (x - (3/4))^2 - 2*(3/4)^2 = 2*x^2 - 3*x, by linarith only [this],
have 2 * (x - (3/4))^2 - 2*(3/4)^2 + 4 = 2*x^2 - 3*x + 4, by linarith only [this],
have completeTheSquare : 2 * (x - (3/4))^2 - 2*(3/4)^2 + 4 = 2 * (x - (3/4))^2 - 9/8 + 32/8, by norm_num,
have  2 * (x - (3/4))^2 - 9/8 + 32/8 = 2 * (x - (3/4))^2 + 23 / 8, by linarith,
have completeTheSquare : 2 * (x - (3/4))^2 - 2*(3/4)^2 + 4 = 2 * (x - (3/4))^2 + 23 / 8, by cc,
suffices 23/8 ≤ 2 * (x - (3/4))^2 + 23 / 8, by cc,
have t1 : 2 * (x-(3/4))^2 ≥ 0, from mul_nonneg (by norm_num) (pow_two_nonneg (x-(3/4))),
by linarith only [completeTheSquare, t1]

example : x^2 - 3*x + 2*y^2 + 4*y + 2 ≥ -17/4 :=
-- have x^2 - 3*x + 2*y^2 + 4*y + 2 = (x-(3/2))^2 - 9/4 + 2*y^2 + 4*y + 2, by sorry,
-- have (x-(3/2))^2 - 9/4 + 2*y^2 + 4*y + 2 = (x-(3/2))^2 + y^2 + 4*y - 1/4, by sorry,
have (x-(3/2))^2 + y^2 + 4*y - 1/4 = (x-(3/2))^2 + (y + 2)^2 - 17/4, by linarith,
by linarith only [this, pow_two_nonneg (x-(3/2))^2]

example : x^2 + 4*x*y + 5*y^2 - 4*x - 6*y + 7 ≥ 2 :=
have x^2 + 4*x*y + 5*y^2 - 4*x - 6*y + 7 = (x + 2*y - 2)^2 + y^2 + 2*y + 3, by linarith,
have x^2 + 4*x*y + 5*y^2 - 4*x - 6*y + 7 = (x + 2*y - 2)^2 + (y+1)^2 + 2, by linarith,
by linarith only [this, pow_two_nonneg (x + 2*y - 2), pow_two_nonneg ((y+1))]
