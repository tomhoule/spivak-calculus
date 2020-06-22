import algebra.ordered_field
import algebra.group_with_zero_power
import tactic.basic
import tactic.algebra
import tactic.suggest
import tactic.linarith

variables {α : Type } [discrete_linear_ordered_field α]
variables {a b c d : α}

open int

-- (i)
example : a < b → c < d → a + c < b + d :=
assume altb cltd,
have h1: a + c < b + c, from add_lt_add_right altb c,
have h2: b + c < b + d, from add_lt_add_left cltd b,
lt_trans h1 h2

-- (ii)
example : a < b → -b < -a :=
assume h,
have 0 < b - a, from sub_pos_of_lt h,
have 0 - b < b -a -b, from sub_lt_sub_right this b,
have 0 + -b < b + -a + -b, by assumption,
have -b < b + -b + -a, by rwa [zero_add, add_assoc, add_comm (-a), ←add_assoc] at this,
by rwa [add_neg_self b, zero_add] at this

-- (iii)
example : a < b → d < c → a - c < b - d :=
assume altb dltc,
have h1 : a - c < b - c, from sub_lt_sub_right altb c,
have h2 : b - c < b - d, from (
    have d - b < c - b, from sub_lt_sub_right dltc b,
    have -(b - d) < -(b - c), by rwa [←neg_sub b d, ←neg_sub b c] at this,
    neg_lt_neg_iff.elim_left this
),
lt_trans h1 h2

-- (iv)
example : a < b → 0 < c → a*c < b*c :=
assume altb cpos,
have 0 < b - a, from sub_pos_of_lt altb,
have 0 < c * (b - a), from mul_pos cpos this,
have 0 < (b*c) - (a*c), by rwa [mul_sub, mul_comm c b, mul_comm c a] at this,
have 0 + (a*c) < b*c - a*c + a*c, from add_lt_add_right this (a*c),
by simpa

-- (v), alias mul_lt_mul_right
example : a < b → c < 0 → b*c < a*c :=
assume altb cneg,
have 0 < b - a, from sub_pos_of_lt altb,
have c * (b - a) < 0, from mul_neg_of_neg_of_pos cneg this,
have b*c - a*c < 0, by rwa [mul_sub, mul_comm c b, mul_comm c a] at this,
have b*c - a*c + a*c < 0 + a*c, from add_lt_add_right this (a*c),
by simpa

-- (vi)
example : ∀ (a : ℤ), 1 < a → a < a^2 :=
assume a onelta,
have apos : 0 < a, by linarith,
-- by iv
have 1 * a < a * a, from (mul_lt_mul_right apos).elim_right onelta,
show a < a^2, by rwa [one_mul, ←pow_two] at this

-- (vii)
example : 0 < a → a < 1 → a^2 < a :=
assume apos altone,
have a * a < 1 * a, from (mul_lt_mul_right apos).elim_right altone,
show a^2 < a, by rwa [one_mul, ←pow_two] at this

-- (viii),
def p5viii : 0 ≤ a → 0 ≤ c → a < b → c < d → a*c < b*d :=
assume anonneg cnonneg altb cltd,
have dpos : 0 < d, from gt_of_gt_of_ge cltd cnonneg,
have bpos : 0 < b, from gt_of_gt_of_ge altb anonneg,
have bdpos : 0 < b*d, from mul_pos bpos dpos,
begin
cases eq_or_lt_of_le anonneg ; cases eq_or_lt_of_le cnonneg,
repeat {
    have : a * c = 0, by rw [←h, zero_mul] <|> rw [←h_1, mul_zero],
    show a*c < b*d, by rwa [←this] at bdpos
},
have h1 : a*c < b*c, from (mul_lt_mul_right h_1).elim_right altb,
have h2 : b*c < b*d, from (mul_lt_mul_left bpos).elim_right cltd,
exact lt_trans h1 h2
end

-- (ix)
example : 0 ≤ a → a < b → a^2 < b^2 :=
assume anonneg altb,
have a * a < b * b, from p5viii anonneg anonneg altb altb,
by rwa [←pow_two, ←pow_two] at this

-- (x)
example : 0 ≤ a → 0 ≤ b → a^2 < b^2 → a < b :=
assume anonneg bnonneg asqltbsq,
have unpowed : a * a < b * b, by rwa [pow_two, pow_two] at asqltbsq,
have asqnonneg : 0 ≤ a^2, from pow_nonneg anonneg 2,
have bsqpos : 0 < b^2, from gt_of_gt_of_ge asqltbsq asqnonneg,
sorry
