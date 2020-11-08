import data.real.basic

variables { x x0 y y0 ε a b c d : ℝ }

--
-- # sum the two greater values
--
example : abs (y-y0) < min (abs y0/2) ((ε*(abs y0)^2)/2) → abs (y-y0) * 2 < (abs y0 + ε*(abs y0)^2)/2 :=
begin
intro h,
rcases (lt_min_iff.mp h) with ⟨hLeft, hRight⟩,
have : abs (y-y0) * 4 - abs y0 < ε*(abs y0)^2, by linarith,
linarith
end

--
-- # isolate abs y0 / 2
--
example : a < (ε * (abs y0)^2) / 2 → 0 < ε → 0 < (abs y0) → a * ε⁻¹ * (abs y0)⁻¹ < (abs y0)/2 :=
begin
intros h h' h'',
have : a < (ε * (abs y0 * abs y0)) / 2, by rwa [pow_two] at h,
have : a < ε * (abs y0 * abs y0 / 2), by linarith only [this],
have : a * ε⁻¹ < abs y0 * abs y0 / 2, from (mul_inv_lt_iff h').mpr this,
have : a * ε⁻¹ < abs y0 * (abs y0 / 2), by rwa [mul_div_assoc] at this,
have : a * ε⁻¹ * (abs y0)⁻¹ < abs y0 / 2, from (mul_inv_lt_iff h'').mpr this,
exact this
end

--
-- # isolate ε
--
example : a < (ε * (abs y0)^2) / 2 → 0 < (abs y0 / 2) → 0 < (abs y0) → a * (abs y0)⁻¹ * (abs y0 / 2)⁻¹ < ε :=
begin
intros h h' h'',
have : a < (ε * (abs y0 * abs y0)) / 2, by rwa [pow_two] at h,
have : a < abs y0 * ((abs y0 / 2) * ε), by linarith only [this],
have : a * (abs y0)⁻¹ < (abs y0 / 2) * ε, from (mul_inv_lt_iff h'').mpr this,
exact (mul_inv_lt_iff h').mpr this
end

def isolateε : a < (ε * (abs y0)^2) / 2 → 0 ≠ y0→ a / ((abs y0^2) / 2) < ε :=
begin
intros h h',
have h' : 0 < abs y0, from abs_pos_iff.mpr (ne.symm h'),
have h' : 0 < (abs y0)^2, from pow_two_pos_of_ne_zero (abs y0) (ne.symm $ ne_of_lt h'),
have h' : 0 < (abs y0)^2 / 2, from half_pos h',
have : a < ((abs y0)^2 / 2) * ε, by linarith,
have : a * ((abs y0)^2 / 2)⁻¹ < ε, from (mul_inv_lt_iff h').mpr this,
rwa [<-@div_eq_mul_inv _ _ a _] at this
end

--
-- # absolute value manipulations
--
example : abs (y-y0) ≤ abs y + abs y0 :=
calc
    abs (y-y0) = abs (y+-y0) : by rw [sub_eq_add_neg]
    ... ≤ abs y + abs (-y0) : abs_add y (-y0)
    ... = abs y + abs y0 : by rw [abs_neg]

example : abs y - abs y0 ≤ abs (y-y0) := sub_abs_le_abs_sub y y0


--
-- # inverse manipulations
--
example : (y*y0⁻¹)⁻¹ = y⁻¹*y0 := by simp [inv_inv', mul_inv']

example : y ≠ 0 → y0 ≠ 0 → (y0-y) / (y*y0) = y⁻¹ - y0⁻¹ := λ h h1, eq.symm $ inv_sub_inv h h1

example : y0 ≠ 0 → (y0*y⁻¹ - 1) * y0⁻¹ = y⁻¹ - y0⁻¹ :=
assume hY0,
have (y0*y⁻¹ - 1) * y0⁻¹ = y0*y0⁻¹*y⁻¹ - y0⁻¹, by linarith,
by rwa [mul_inv_cancel hY0, one_mul] at this

example : 0 < a → 0 < a/2 → a < a/2 → (a/2)⁻¹ < a⁻¹ := assume h h' h'', (inv_lt_inv h' h).mpr h''
example : 0 < (a-b) → 0 < 2/b → a-b < (2/b)⁻¹ → 2/b < (a-b)⁻¹ := assume h h' h'', (lt_inv h h').mp h''
example : (y*y0⁻¹ - 1) * y0⁻¹ = y*(y0⁻¹ * y0⁻¹) - 1/y0 := by linarith [inv_eq_one_div y0]

--
-- # the first branch of the min
--
def absYGtHalfY0 : abs (y-y0) < abs y0 / 2 → abs y0 / 2 < abs y :=
begin
intro h,
calc
abs y0 / 2 = abs y0 - (abs y0 / 2) : by linarith
... < abs y0 - abs (y-y0) : by linarith
... = abs y0 - abs (y0-y) : by rwa [abs_sub]
... ≤ abs (y0 - (y0 - y)) : sub_abs_le_abs_sub y0 (y0 - y)
... ≤ abs y : by rw [sub_sub_assoc_swap, add_comm, add_sub_assoc, sub_self y0, add_zero]
end

-- # And now, the proof.
example :
    y0 ≠ 0 →
    abs (y-y0) < min (abs y0/2) ((ε*(abs y0)^2)/2) →
    y ≠ 0 ∧ abs (1/y - 1/y0) < ε
:=
begin
intros y0Nonzero h,
rcases (lt_min_iff.mp h) with ⟨hLeft, hRight⟩,
have absy0Pos : 0 < abs y0, from abs_pos_iff.mpr y0Nonzero,
have absy0Nonzero : abs y0 ≠ 0, from ne_of_gt absy0Pos,
have yNonzero : y ≠ 0, from by_contradiction (
    assume h,
    have yZero : y = 0, from not_not.mp h,
    have abs (y-y0) > abs y0 / 2, from (
        calc
        abs (y-y0) = abs(0-y0) : by rw [yZero]
        ... = abs y0 : by rw [zero_sub, abs_neg]
        ... > abs y0 / 2 : div_two_lt_of_pos (abs_pos_iff.mpr y0Nonzero)
    ),
    absurd (not_lt.mpr (le_of_lt this)) (not_not.mpr hLeft)
),
split, exact yNonzero,

have absYPos : 0 < abs y, from abs_pos_iff.mpr yNonzero,
have denomPos : 0 < (abs y0)^2 / 2, by linarith [pow_pos absy0Pos 2],

have isolateε : abs (y-y0) / ((abs y0^2) / 2) < ε, from isolateε hRight (ne.symm y0Nonzero),
have denomLt : abs y0 * (abs y0 / 2) < abs y0 * abs y, from (mul_lt_mul_left (abs_pos_iff.mpr y0Nonzero)).mpr (absYGtHalfY0 hLeft),
have denomLt : (abs y0^2) / 2 < abs y0 * abs y, by rwa [<-mul_div_assoc, <-pow_two] at denomLt,
have divLe : abs (y-y0) / (abs y0 * abs y) ≤ abs (y-y0) / (abs y0^2 / 2), from div_le_div (abs_nonneg (y-y0)) (le_of_eq rfl) denomPos (le_of_lt denomLt),

calc
abs (1/y - 1/y0) = abs (y⁻¹ - y0⁻¹) : by rw [inv_eq_one_div y, inv_eq_one_div y0]
... = abs (y0⁻¹ - y⁻¹) : by rw [abs_sub]
... = abs ((y-y0) / (y0*y)) : by rw [inv_sub_inv y0Nonzero yNonzero]
... = abs (y-y0) / (abs y0 * abs y) : by rw [abs_div, abs_mul]
... ≤ abs (y-y0) / (abs y0^2 / 2) : divLe
... < ε : isolateε
end
