import algebra.ordered_field
import algebra.group_with_zero_power
import data.real.basic
import tactic.basic
import tactic.suggest


section problem7

variables {a b : ℝ} {n : ℕ}
variables {apos : 0 < a} {altb : a < b}

def part_1 : a < real.sqrt (a*b) :=
have anonneg : 0 ≤ a, from le_of_lt apos,
have bpos : 0 < b, from lt_trans apos altb,
have bnonneg : 0 ≤ b, from le_of_lt bpos,
have prod_lt : a * a < a * b, from (mul_lt_mul_left apos).mpr altb,
have asqnonneg : 0 ≤ a * a, from mul_nonneg anonneg anonneg,
have abnonneg : 0 ≤ a * b, from mul_nonneg anonneg bnonneg,
have final_lt : real.sqrt (a*a) < real.sqrt (a*b), from (real.sqrt_lt asqnonneg abnonneg).mpr prod_lt,
have a = real.sqrt (a^2), from eq.symm $ real.sqrt_sqr (le_of_lt apos),
have a = real.sqrt (a*a), by rwa [pow_two] at this,
show a < real.sqrt (a*b), by rwa [←this] at final_lt

def part_2 : real.sqrt (a*b) < (a+b) / 2 :=
have real.sqrt (a*b) * 2 = real.sqrt (a*b) + real.sqrt (a*b), from mul_two (real.sqrt (a*b)),
have abpos : 0 < a * b, from sorry,

-- a < (a + b) / 2 < b < a + b
-- a < sqrt(a*b) < b

-- then show that real.sqrt (a*b) * real.sqrt (a*b) < (a+b) / 2 * real.sqrt (a*b)
-- a*b < ((a+b)*real.sqrt(a*b))/2
-- a*b < a*real.sqrt(a) *real.sqrt(b) + b * real.sqrt(a) *real.sqrt(b)/2
sorry

def part_3 : (a+b)/2 < b :=
have beq : (b+b)/2 = b, from half_add_self b,
have bpos : 0 < b, from lt_trans apos altb,
have bplusbpos : 0 < b + b, from add_pos bpos bpos,
have a + b < b + b, from add_lt_add_right altb b,
have (a + b)/2 < (b + b)/2, from div_lt_div this (le_of_eq rfl) (le_of_lt bplusbpos) two_pos,
show (a+b)/2 < b, by rwa [beq] at this

end problem7