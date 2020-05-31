import data.rat.basic
import algebra.field

namespace properties
    variables (α : Type) [field α]
    variables (a b c : α)
    variables (x : ℚ)

    -- P1
    def add_assoc : a + (b + c) = (a + b) + c := by rw [add_assoc a b c]

    -- P2
    def add_zero : a + 0 = a := add_zero a
    def zero_add : 0 + a = a := zero_add a

    -- P3
    def add_opp : a + (-a) = 0 := by rw [add_comm, add_left_neg a]
    def opp_add : (-a) + a = 0 := add_left_neg a

    example : (a + b = a) → b = (0 : α) :=
    assume h,
    calc
        b = 0 + b : by rw zero_add
            ... = (-a + a) + b : by rw opp_add
            ... = -a + (a + b) : by rw add_assoc
            ... = -a + a : by rw h
            ... = 0 : by rw opp_add

    example : (x + 3 = 5) → (x = 2) :=
    assume h,
    calc
        x   = x + (0) : by rw add_zero
        ... = x + (3 + -3) : by rw add_opp
        ... = 5 + -3 : by rw [add_assoc, h]
        ... = 2 : by reflexivity

    -- P4
    def add_comm : a + b = b + a := add_comm a b

end properties
