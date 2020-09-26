import data.real.basic
import tactic.basic
import tactic.noncomm_ring
import tactic.algebra

variables { x y z : ℝ }

def max' : max x y = (x + y + abs (y - x)) / 2 :=
or.elim (le_or_gt x y)
    (λ xley,
        have 0 ≤ y - x, from sub_nonneg.mpr xley,
        have abs (y-x) = y - x, from abs_of_nonneg this,
        have l2 : x + y + abs (y - x) = x + y + (y - x), by rw [this],
        have l3 : x + y + (y - x) = y + y, by linarith,
        calc
            max x y = y : by rw [max_eq_right xley]
                ... = (y + y) / 2 : by linarith
                ... = (x + y + abs (y - x)) / 2 : by rw [l2, l3]
    )
    (λ xgty,
        have y - x < 0, from sub_lt_zero.mpr xgty,
        have abs (y-x) = -(y - x), from abs_of_neg this,
        have l2 : x + y + abs (y - x) = x + y + -(y - x), by rw [this],
        have l3 : x + y + -(y - x) = x + x, by linarith,
        calc
            max x y = x : by rw [max_eq_left_of_lt xgty]
                ... = (x + x) / 2 : by linarith
                ... = (x + y + abs (y - x)) / 2 : by rw [l2, l3]
    )

def min' : min x y = (x + y - abs (y-x)) / 2 :=
or.elim (le_or_gt x y)
    (λ xley,
        have 0 ≤ y - x, from sub_nonneg.mpr xley,
        have abs (y-x) = y - x, from abs_of_nonneg this,
        have l2 : x + y - abs (y-x) = x + y - (y - x), by rw [this],
        calc
            min x y = x : by rw [min_eq_left xley]
                ... = (x + x) / 2 : by linarith
                ... = (x + y - (y - x)) / 2 : by linarith
                ... = (x + y - abs (y-x)) / 2 : by rw l2
    )
    (λ xgty,
        have y - x < 0, from sub_lt_zero.mpr xgty,
        have abs (y-x) = -(y-x), from abs_of_neg this,
        have abs (y-x) = x-y, by rw [this, neg_sub],
        have l2 : x + y - abs (y-x) = x + y - (x-y), by rw this,
        calc
            min x y = y : by rw [min_eq_right_of_lt xgty]
                ... = (y + y) / 2 : by linarith
                ... = (x + y - (x-y)) / 2 : by linarith
                ... = (x + y - abs (y-x))/2 : by rw l2
    )


def max3 : max x (max y z) = (2*x + y + z + abs (z-y) + abs (y + z + abs (z-y) - 2*x)) / 4 :=
have l1 : 2*x/2 = x, by linarith,
have l2 : (y + z + abs (z-y)) / 2 - (2*x)/2 = (y + z + abs (z-y) - 2*x) / 2, by linarith,
have l3 :
    (2*x)/2 +
    (y + z + abs (z-y)) / 2 +
    (abs (y + z + abs (z-y) - 2*x)) / 2
    =
    ((2*x)
    + (y + z + abs (z-y))
    + (abs (y + z + abs (z-y) - 2*x))) / 2,
    by linarith,
calc
    max x (max y z) = (x + (max y z) + abs ((max y z) - x)) / 2 : by rw max'
                ... =
                (
                    x +
                    ((y + z + abs (z-y)) / 2) +
                    abs (
                        ((y + z + abs (z-y)) / 2) - x
                    )
                ) / 2 : by rw [@max' y z]
                ... =
                (
                    (2*x)/2 +
                    ((y + z + abs (z-y)) / 2) +
                    abs (
                        ((y + z + abs (z-y)) / 2) - (2*x)/2
                    )
                ) / 2 : by rw [l1]
                ... =
                (
                    (2*x)/2 +
                    ((y + z + abs (z-y)) / 2) +
                    abs ((y + z + abs (z-y) - 2*x) / 2)
                ) / 2 : by rw l2
                ... =
                (
                    (2*x)/2 +
                    (y + z + abs (z-y)) / 2 +
                    (abs (y + z + abs (z-y) - 2*x)) / 2
                ) / 2 : by rw [abs_div, abs_two]
                ... =
                (
                    ((2*x)
                    + (y + z + abs (z-y))
                    + (abs (y + z + abs (z-y) - 2*x))) / 2
                ) / 2 : by rw l3
                ... = (2*x + y + z + abs (z-y) + abs (y + z + abs (z-y) - 2*x)) / 4 : by linarith

def min3 : min x (min y z) = (2*x + y + z - abs (z-y) - abs (y+z-abs(z-y)-2*x)) / 4 :=
have l1 : 2*x/2 = x, by linarith,
have l2 : (2*x)/2 + (y + z - abs (z-y))/2 = (2*x + y + z - abs (z-y))/2, by linarith,
have l3 : (y + z - abs (z-y))/2-2*x/2 = (y+z-abs(z-y)-2*x) / 2, by linarith,
calc
    min x (min y z) = (x + (min y z) - abs ((min y z)-x)) / 2 : by rw min'
                ... = (x + (y + z - abs (z-y))/2 - abs ((y + z - abs (z-y))/2-x)) / 2 : by rw min'
                ... = ((2*x)/2 + (y + z - abs (z-y))/2 - abs ((y + z - abs (z-y))/2-2*x/2)) / 2 : by rw l1
                ... = ((2*x + y + z - abs (z-y))/2 - abs ((y+z-abs(z-y)-2*x) / 2)) / 2 : by rw [l2, l3]
                ... = ((2*x + y + z - abs (z-y))/2 - (abs (y+z-abs(z-y)-2*x)) / 2) / 2 : by rw [abs_div, abs_two]
                ... = (2*x + y + z - abs (z-y) - abs (y+z-abs(z-y)-2*x)) / 4 : by linarith
