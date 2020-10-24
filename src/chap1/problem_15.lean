import data.real.basic
import chap1.problem_01
import chap1.problem_06

variables { x y : ℝ }

example : ¬(x = 0 ∧ y = 0) → x^2 + x*y + y^2 > 0 :=
begin
    intro h,
    rcases (lt_trichotomy 0 (x-y)) with hLt | hEq | hGt,
    {
        have : x > y, from sub_pos.mp hLt,
        have : x^3 > y^3, from odd_pow_lt 3 this rfl,
        have hCubePos : 0 < x^3 - y^3, from sub_pos.mpr this,
        have : x^3 - y^3 = (x-y) * (x^2 + x*y + y^2), from cube_cube_sub,
        have : 0 < (x-y) * (x^2 + x*y + y^2), by rwa [this] at hCubePos,
        exact pos_of_mul_pos_left this (le_of_lt hLt)
    },
    {
        have hEq : x = y, from sub_eq_zero.mp (eq.symm hEq),
        rcases (not_and_distrib.mp h) with xNonzero | yNonzero,
        {
            have h' : x^2 + x*y + y^2 = x^2 + x^2 + x^2, by rw [hEq, pow_two],
            have : 0 < x^2, from pow_two_pos_of_ne_zero x xNonzero,
            linarith only [this, h']
        },
        have h' : x^2 + x*y + y^2 = y^2 + y^2 + y^2, by rw [hEq, pow_two],
        have : 0 < y^2, from pow_two_pos_of_ne_zero y yNonzero,
        linarith only [this, h']
    },
    have : 0 < -(x-y), from neg_pos.mpr hGt,
    have hLt : 0 < y - x, by rwa [neg_sub] at this,
    have : y > x, from sub_pos.mp hLt,
    have : y^3 > x^3, from odd_pow_lt 3 this rfl,
    have hCubePos : 0 < y^3 - x^3, from sub_pos.mpr this,
    have : y^3 - x^3 = (y-x) * (y^2 + y*x + x^2), from cube_cube_sub,
    have : 0 < (y-x) * (y^2 + y*x + x^2), by rwa [this] at hCubePos,
    have : 0 < (y-x) * (x^2 + x*y + y^2), by linarith only [this],
    exact pos_of_mul_pos_left this (le_of_lt hLt)
end

example : ¬(x = 0 ∧ y = 0) → x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4 > 0 :=
begin
    intro h,
    rcases (lt_trichotomy 0 (x-y)) with hLt | hEq | hGt,
    {
        have : x > y, from sub_pos.mp hLt,
        have : x^5 > y^5, from odd_pow_lt 5 this rfl,
        have hCubePos : 0 < x^5 - y^5, from sub_pos.mpr this,
        have : x^5 - y^5 = (x-y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4), from pow_pow_sub_five x y,
        have : 0 < (x-y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4), by rwa [this] at hCubePos,
        exact pos_of_mul_pos_left this (le_of_lt hLt)
    },
    {
        have hEq : x = y, from sub_eq_zero.mp (eq.symm hEq),
        rcases (not_and_distrib.mp h) with xNonzero | yNonzero,
        {
            have xSqPos : 0 < x^2, from pow_two_pos_of_ne_zero x xNonzero,
            have hX : x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4 = x^4 + x^3*x + x^2*x^2 + x*x^3 + x^4, by rw [hEq],
            have l1 : x^4 = x^2 * x^2, from pow_bit0 x 2,
            have l2 : x^3 * x = x^2 * x^2, by linarith,
            have l3 : x * x^3 = x^2 * x^2, by rwa [<-mul_comm x (x^3)] at l2,
            have l4 : 0 < x^2 * x^2, from mul_pos xSqPos xSqPos,
            linarith only [hX, l1, l2, l3, l4]
        },
        have ySqPos : 0 < y^2, from pow_two_pos_of_ne_zero y yNonzero,
        have hy : x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4 = y^4 + y^3*y + y^2*y^2 + y*y^3 + y^4, by rw [hEq],
        have l1 : y^4 = y^2 * y^2, from pow_bit0 y 2,
        have l2 : y^3 * y = y^2 * y^2, by linarith,
        have l3 : y * y^3 = y^2 * y^2, by rwa [<-mul_comm y (y^3)] at l2,
        have l4 : 0 < y^2 * y^2, from mul_pos ySqPos ySqPos,
        linarith only [hy, l1, l2, l3, l4]
    },
    have : 0 < -(x-y), from neg_pos.mpr hGt,
    have hLt : 0 < y - x, by rwa [neg_sub] at this,
    have : y > x, from sub_pos.mp hLt,
    have : y^5 > x^5, from odd_pow_lt 5 this rfl,
    have hCubePos : 0 < y^5 - x^5, from sub_pos.mpr this,
    have hR : (y^4 + y^3*x + y^2*x^2 + y*x^3 + x^4) = (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4), by ring,
    have : y^5 - x^5 = (y-x) * (y^4 + y^3*x + y^2*x^2 + y*x^3 + x^4), from pow_pow_sub_five y x,
    have : 0 < (y-x) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4), by rwa [this, hR] at hCubePos,
    exact pos_of_mul_pos_left this (le_of_lt hLt)
end
