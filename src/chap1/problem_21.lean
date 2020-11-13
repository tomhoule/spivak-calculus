import data.real.basic

variables { x x0 y y0 ε a b c : ℝ }

def helper1 : 0 < c → a < b/c → a * c < b :=
assume hNonzero h1,
(lt_div_iff hNonzero).mp h1

example : (x-x0) * (y-y0) = x*y - x*y0 - x0*y + x0*y0 := by linarith
example : (x0-x) * (y-y0) = x0*y - x0*y0 - x*y + x*y0 := by linarith
example : (x0-x) * (y0-y) = x0*y0 -x0*y -x*y0 + x*y := by linarith

example : abs (x-x0) * abs y0 + abs (x - x0) * abs (y - y0) =
abs ((x-x0) * y0) + abs (x - x0) * abs (y - y0)
:= by linarith  [abs_mul (x-x0) y0, abs_mul (x-x0) (y-y0)]

example : (x-x0) * y0 + (x-x0) * (y-y0) = x*y0 + x*y - x*y0 -x0*y := by linarith
example : (y-y0) * x0 + (y-y0) * (x-x0) = y*x0 + x*y - y*x0 -y0*x := by linarith
example : (x-x0) * y0 + (x-x0) * (y-y0) + (y-y0) * x0 + (y-y0) * (x-x0) = (x-x0) * y + (y-y0) * x := by linarith

-- Work with equality only first
example : (x - x0) * (y0 + 1) = x*y0 + x - x0*y0 - x0 := by linarith
example : (y - y0) * (x0 + 1) = y*x0 + y - y0*x0 - y0 := by linarith
example : x*y0 + x - x0*y0 - x0 + y*x0 + y - y0*x0 - y0 =
x-x0 + y-y0 + x*y0 + y*x0 - 2*x0*y0 := by linarith -- use abs_sub maybe? no doesn't help

-- example : (x-x0 * -(y-y0)) = -x * y0 + x*y := by linarith
example : (x-x0) * y + (y-y0) * x0 = x*y - y0*x0 := by linarith -- this!
def helper2 : (x-x0) * y0 + (y-y0) * x = x*y - x0*y0 := by linarith -- this!

def helper3 : 0 ≤ x → 0 ≤ y → x * y ≤ x * (2*(y+1)) :=
assume xNonneg yNonneg,
have h1 : y ≤ 2 * (y+1), by linarith,
have x * y ≤ x * (2*(y+1)), from mul_le_mul (le_of_eq rfl) h1 yNonneg xNonneg,
by rwa [mul_comm, mul_comm] at this

def problem_21 :
    abs (x-x0) < min (ε / (2*(abs y0 + 1))) 1 →
    abs (y-y0) < ε / (2*(abs x0 + 1)) →
    abs (x*y - x0*y0) < ε
:=
begin
intros hX hY,
rcases (lt_min_iff.mp hX) with ⟨xLtε, xLtOne⟩,
have εPos : 0 < ε, {
    have : 0 ≤ abs (y-y0), from abs_nonneg (y-y0),
    have : 0 < ε / (2*(abs x0 + 1)), from lt_of_le_of_lt this hY,
    have h : 0 < ε * (2*(abs x0 + 1))⁻¹, by rwa [div_eq_mul_inv] at this,
    have : 0 < (2*(abs x0 + 1))⁻¹, from inv_pos.mpr (by linarith [abs_nonneg x0]),
    exact (zero_lt_mul_right this).mp h
},
-- Rewrite hY to get ε/2 on the right side
have : 0 < (2*(abs x0 + 1)), by linarith [abs_nonneg x0],
have : abs (y-y0) * (2*(abs x0 + 1)) < ε, from helper1 this hY,
have s1 : abs x0 + abs (x-x0) < abs x0 + 1, from add_lt_add_left xLtOne (abs x0),
have s2 : abs (x0+(x-x0)) ≤ abs x0 + abs (x-x0), from abs_add x0 (x - x0),
have : x0 + (x - x0) = x, by linarith,
have s2 : abs x ≤ abs x0 + abs (x-x0), by rwa [this] at s2,
have s3 : abs x < abs x0 + 1, from lt_of_le_of_lt s2 s1,
have : abs (y-y0) * abs x < ε/2, {
    rcases (eq_or_lt_of_le (abs_nonneg (y-y0))) with yy0Zero | yY0Pos,
    {
        have h : 0 < ε/2, from half_pos εPos,
        have : abs (y-y0) * abs x = 0, by rw [<-yy0Zero, zero_mul],
        rwa <-this at h
    },
    linarith [((mul_lt_mul_right yY0Pos).mpr s3)],
},
have left : abs (y-y0) * abs x < ε/2, by linarith only [this],
-- The right side of the addition of the two inequalities is then easily derived
-- from hX
have right : abs (x-x0) * (2*(abs y0 + 1)) < ε, from helper1 (show 0 < 2*(abs y0 + 1), by linarith [abs_nonneg y0]) xLtε, -- by linarith only [(lt_min_iff.mp hX).right],
have : abs ((y-y0) * x) + abs ((x-x0) * y0) + abs (x-x0) < ε, by linarith only [left, right, abs_mul (y-y0) x, abs_mul (x-x0) y0],
-- observation: abs (x-x0) > 0, so all the more so < ε
calc
    abs (x*y - x0*y0) = abs ((y-y0) * x + (x-x0) * y0) : by simp only [helper2, add_comm]
    ... ≤ abs ((y-y0) * x) + abs ((x-x0) * y0) : abs_add ((y - y0) * x) ((x - x0) * y0)
    ... ≤ abs ((y-y0) * x) + abs ((x-x0) * y0) + abs (x-x0) : le_add_of_nonneg_right (abs_nonneg (x - x0))
    ... < ε : this

-- have left : abs (y-y0) * abs x < ε/2, by linarith only [this],
-- have right : abs (x-x0) * (abs y0 + 1) < ε/2, from sorry, -- by linarith only [(lt_min_iff.mp hX).right],
-- have : abs ((y-y0) * x) + abs ((x-x0) * y0) + abs (x-x0) < ε, by linarith only [left, right, abs_mul (y-y0) x, abs_mul (x-x0) y0],
-- maybe plug abs (x-x0) < 1 in the previous one at this point, not before

-- have t3 : abs (y - y0) < 1, from (lt_min_iff.mp hx).elim_right,
-- -- have : abs (x-x0)^2 < abs (x-x0), from sorry, -- yes
-- -- have : abs (x-x0) > abs (x-x0) * (ε / (2*(abs y0 + 1))), from sorry,
-- have : abs (x-x0) < ε / (2*(abs y0 + 1)), from (lt_min_iff.mp hX).elim_left,
-- have t4 : abs (x-x0) * (2*(abs y0 + 1)) < ε, from helpet3r1 t2 this,
-- have : abs y0 + abs (y-y0) < abs y0 + 1, by linarith,
-- have t5 : 2*(abs y0 + abs (y-y0)) < 2*(abs y0 + 1), by linarith,
-- have xsPos : abs (x - x0) > 0, from sorry,
-- have : abs (x-x0) * (2*(abs y0 + abs (y-y0))) < abs (x-x0) * (2*(abs y0 + 1)), from (mul_lt_mul_left xsPos).mpr t5,
-- have : abs (x-x0) * (2*(abs y0 + abs (y-y0))) < ε, by linarith,
-- have : abs (x-x0) * (abs y0 + abs (y-y0)) < (ε/2), by linarith only [this],
-- have : abs (x-x0) * (abs y0 + abs (y-y0)) = abs ((x-x0) * y0) + abs ((x-x0) * (y-y0)), by linarith [abs_mul (x-x0) y0, abs_mul (x-x0) (y-y0)],
-- we can get the 2 on the right, and have < ε/2. then do the same on the other
-- side.

-- have : 2* ((abs (x-x0) * abs y0) + abs (x - x0) * 1) < ε, by linarith only [this],
-- have : 2* ((abs (x-x0) * abs y0) + abs (x - x0) * abs (y - y0)) < ε, from sorry,
-- note that abs y0 + 1 is abs y0 + (abs x*y/ absx*y)
-- note: maybe use the < min _ 1 fact to replace the + 1 in the denominator with
-- y-y0
-- abs x-x0 * 2*(abs y0 + 1) < ε900

-- 2 * (abs (x -x0) * abs y0) + abs (x-x0)) < ε
-- abs x - x0 * 2*
end
