import data.real.basic
import tactic.basic

variables { a b : ℝ }

-- (a)
def abs_neg' : abs a = abs (-a) :=
or.elim (le_or_gt 0 a)
    (λ anonneg,
        have l1 : abs a = a , from abs_of_nonneg anonneg,
        have -a ≤ 0, from neg_nonpos.mpr anonneg,
        have abs (-a) = - -a, from abs_of_nonpos this,
        have l3 : abs (-a) = a, by rwa [neg_neg] at this,
        eq.trans l1 (eq.symm l3)
    )
    (λ aneg,
        have l1 : abs a = -a, from abs_of_neg aneg,
        have 0 < -a, from neg_pos.mpr aneg,
        have abs (-a) = -a, from abs_of_pos this,
        eq.trans l1 (eq.symm this)
    )

-- (b)
def part_b : (-b ≤ a ∧ a ≤ b) ↔ abs a ≤ b :=
iff.intro
    (λ ⟨negBLeA, aLeB⟩,
        or.elim (le_or_gt 0 a)
            (λ aNonneg,
                have abs a = a, from abs_of_nonneg aNonneg,
                by rwa [←this] at aLeB
            )
            (λ aneg,
                have -b ≤ - -a, by rwa [←neg_neg a] at negBLeA,
                have -b ≤ - abs a, by rwa [←abs_of_neg aneg] at this,
                neg_le_neg_iff.elim_left this
            )
    )
    (λ absALeB,
        have bnonneg : 0 ≤ b, from le_trans (abs_nonneg a) absALeB,
        have l1 : -b ≤ 0, from neg_nonpos.mpr bnonneg,
        or.elim (le_or_gt 0 a)
            (λ anonneg,
                have l2 : abs a = a, from abs_of_nonneg anonneg,
                have left : -b ≤ a, from le_trans l1 anonneg,
                have right : a ≤ b, by rwa [l2] at absALeB,
                ⟨left, right⟩
            )
            (λ aneg,
                have l2 : abs a = -a, from abs_of_neg aneg,
                have 0 ≤ b - abs a, from sub_nonneg.mpr absALeB,
                have 0 ≤ b + - - a, by rwa [l2] at this,
                have left : -b ≤ a, by linarith only [this],
                have right : a ≤ b, from le_trans (le_of_lt aneg) bnonneg,
                ⟨left, right⟩
            )
    )

example : -(abs a) ≤ a ∧ a ≤ abs a :=
have abs a ≤ abs a, from le_of_eq rfl,
part_b.elim_right this

-- (c)
def neg_abs_le_self : -abs a ≤ a :=
or.elim (le_or_gt 0 a)
    (λ anonneg,
        have h₁ : abs a = a, from abs_of_nonneg anonneg,
        have -a ≤ a, from neg_le_self anonneg,
        (congr_arg has_neg.neg h₁).trans_le this
    )
    (λ aneg,
        have h₁ : abs a = -a, from abs_of_neg aneg,
        have -(abs a) = a, from neg_eq_iff_neg_eq.elim_right (eq.symm h₁),
        le_of_eq this
    )

def part_c : abs (a + b) ≤ abs a + abs b :=
have left : -(abs a + abs b) ≤ a + b, from (
    have l1 : -(abs a + abs b) = -abs a + -abs b, from neg_add (abs a) (abs b),
    have -abs a + -abs b ≤ a + b, from add_le_add neg_abs_le_self neg_abs_le_self,
    by rwa [←l1] at this
),
have right : a + b ≤ abs a + abs b, from add_le_add (le_abs_self a) (le_abs_self b),
part_b.elim_left ⟨left, right⟩
