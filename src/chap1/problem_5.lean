import algebra.ordered_field
import tactic.basic
import tactic.algebra
import tactic.suggest

variables {α : Type } [linear_ordered_field α]
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
example : a < b → d < c → a - c < b - d := sorry
