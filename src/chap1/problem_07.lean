import algebra.ordered_field
import data.real.sqrt
import tactic.basic
import tactic.suggest

open real (sqrt)

section problem7

variables {a b : ℝ} {n : ℕ}
variables {apos : 0 < a} {altb : a < b}

lemma part_1 : a < sqrt (a*b) :=
have anonneg : 0 ≤ a, from le_of_lt apos,
have bpos : 0 < b, from lt_trans apos altb,
have bnonneg : 0 ≤ b, from le_of_lt bpos,
have prod_lt : a * a < a * b, from (mul_lt_mul_left apos).mpr altb,
have asqnonneg : 0 ≤ a * a, from mul_nonneg anonneg anonneg,
have abnonneg : 0 ≤ a * b, from mul_nonneg anonneg bnonneg,
have final_lt : sqrt (a*a) < sqrt (a*b), from (real.sqrt_lt asqnonneg).mpr prod_lt,
have a = sqrt (a^2), from eq.symm $ real.sqrt_sqr (le_of_lt apos),
have a = sqrt (a*a), by rwa [pow_two] at this,
show a < sqrt (a*b), by rwa [←this] at final_lt

lemma sq_add : (a+b)^2 = a^2 + 2*(a*b) + b^2 :=
calc
    (a+b)^2 = (a+b) * (a+b) : by rw [pow_two]
        ... = a * (a + b) + b * (a+b) : add_mul a b (a + b)
        ... = a * a + a * b + (b * a + b * b) : by rw [mul_add, mul_add]
        ... = a^2 + a*b + (b*a + b^2) : by rw [pow_two, pow_two]
        ... = a^2 + a*b + (a*b + b^2) : by rw [mul_comm]
        ... = a^2 + (a*b + a*b) + b^2 : by simp only [add_assoc]
        ... = a^2 + (a*b)*2 + b^2 : by rw [mul_two]
        ... = a^2 + 2*(a*b) + b^2 : by rw [mul_comm]

lemma sq_sub : (a-b)^2 = (a^2 + b^2) - 2*(a*b) :=
calc
    (a-b)^2 = (a - b) * (a - b) : by rw pow_two
        ... = (a * a - a*b) - (b * a - b * b) : by rw [sub_mul, mul_sub, mul_sub]
        ... = (a^2 - a*b) - (a*b - b^2) : by rw [pow_two, pow_two, mul_comm b a]
        ... = (a^2 - a*b) + b^2 - a*b : by rw [sub_sub_assoc_swap]
        ... = a^2 + -(a*b) + b^2 + -(a*b) : rfl
        ... = (a^2 + b^2) + (-(a*b) + -(a*b)) : by simp only [add_assoc, add_comm (-(a * b))]
        ... = (a^2 + b^2) + (-(a*b))*2 : by rw [mul_two (-(a*b))]
        ... = (a^2 + b^2) + -((a*b)*2) : by simp only [neg_mul_eq_neg_mul_symm]
        ... = (a^2 + b^2) - (a*b)*2 : rfl
        ... = (a^2 + b^2) - 2*(a*b) : by rwa [mul_comm]

lemma part_2 : real.sqrt (a*b) < (a+b) / 2 :=
have bpos : 0 < b, from lt_trans apos altb,
have aplusbpos : 0 < a + b, from add_pos apos bpos,

-- Prove l3
have l1 : (sqrt a - sqrt b)^2 = ((sqrt a)^2 + (sqrt b)^2) - 2*(sqrt a * sqrt b), from sq_sub,
have l2 : ((sqrt a)^2 + (sqrt b)^2) - 2*(sqrt a * sqrt b) = a + b - 2*(sqrt a * sqrt b), by rw [pow_two (sqrt a), pow_two (sqrt b), real.mul_self_sqrt (le_of_lt apos), real.mul_self_sqrt (le_of_lt bpos)],
have l3 : a + b - 2*(sqrt a * sqrt b) = (sqrt a - sqrt b)^2, by rw [l1, l2],

-- Prove that (sqrt a - sqrt b)^2 is positive
have sqrt a < sqrt b, from (real.sqrt_lt (le_of_lt apos)).elim_right altb,
have (sqrt a - sqrt b) < 0, from sub_neg_of_lt this,
have 0 < (sqrt a - sqrt b) * (sqrt a - sqrt b), from mul_pos_of_neg_of_neg this this,
have 0 < (sqrt a - sqrt b)^2, by rwa [←pow_two] at this,

-- Use l3 to rewrite this to our goal
have 0 < a + b - 2*(sqrt a * sqrt b), by rwa [←l3] at this,
have 0 + 2*(sqrt a * sqrt b) < a + b - 2*(sqrt a * sqrt b) + 2*(sqrt a * sqrt b), from add_lt_add_right this (2*(sqrt a * sqrt b)),
have 2*(sqrt a * sqrt b) < a + b, by simpa only [sub_add_cancel, zero_add],
have 2*(sqrt a * sqrt b) / 2 < (a + b) / 2, from div_lt_div this (le_of_eq rfl) (le_of_lt aplusbpos) zero_lt_two,
have (sqrt a * sqrt b)*2 / 2 < (a + b) / 2, by rwa [mul_comm] at this,
have sqrt a * sqrt b < (a + b) / 2, by rwa [mul_div_cancel (sqrt a * sqrt b) two_ne_zero] at this,
by rwa [←real.sqrt_mul (le_of_lt apos)] at this

lemma part_3 : (a+b)/2 < b :=
have beq : (b+b)/2 = b, from half_add_self b,
have bpos : 0 < b, from lt_trans apos altb,
have bplusbpos : 0 < b + b, from add_pos bpos bpos,
have a + b < b + b, from add_lt_add_right altb b,
have (a + b)/2 < (b + b)/2, from div_lt_div this (le_of_eq rfl) (le_of_lt bplusbpos) zero_lt_two,
show (a+b)/2 < b, by rwa [beq] at this

end problem7
