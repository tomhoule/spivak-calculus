import data.rat.basic
import algebra.field
import algebra.ordered_field

namespace properties
    open field

    variables (α : Type) [linear_ordered_field α]
    variables (a b c : α)
    variables (x : ℚ)

    -- P1
    def add_assoc' : a + (b + c) = (a + b) + c := by rw [add_assoc a b c]

    -- P2
    def add_zero' : a + 0 = a := add_zero a
    def zero_add' : 0 + a = a := zero_add a

    -- P3
    def add_opp : a + (-a) = 0 := by rw [add_comm, add_left_neg a]
    def opp_add : (-a) + a = 0 := add_left_neg a

    def add_b_eq_self : (a + b = a) → b = (0 : α) :=
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
        x   = x + 0 : by rw add_zero
        ... = x + (3 + -3) : by rw add_right_neg
        ... = (x + 3) + -3 : by rw [add_assoc]
        ... = 5 + -3 : by rw [h]
        ... = 2 : by reflexivity

    -- P4
    def add_comm' : a + b = b + a := add_comm a b

    -- P5
    def mul_assoc' : a * (b * c) = (a * b) * c := by rw mul_assoc a b c

    -- P6
    def mul_one' : a * 1 = a := mul_one a
    def one_mul' : 1 * a = a := one_mul a

    -- P7
    def mul_inverse : ∀ (x : α), x ≠ 0 → x * (x⁻¹) = 1 := assume hx hxpos, mul_inv_cancel hxpos
    def inverse_mul : ∀ (x : α), x ≠ 0 → (x⁻¹) * x = 1 := assume hx hxpos, inv_mul_cancel hxpos

    -- P8
    def mul_comm' : a * b = b * a := mul_comm a b

    example : (a ≠ 0) → (a * b = a * c) → b = c :=
    assume hnzero h,
        calc
            b   = 1 * b : by rw one_mul
            ... = (a⁻¹ * a) * b : by rw [inverse_mul α a hnzero]
            ... = a⁻¹ * (a * b) : by rw [mul_assoc']
            ... = a⁻¹ * (a * c) : by rw [h]
            ... = c : by rw [mul_assoc', inverse_mul α a hnzero, one_mul]

    example : a ≠ 0 → (a * b = 0) → (a = 0 ∨ b = 0) :=
    assume hnzero h,
    or.inr $ calc
        b = 1 * b : by rw one_mul b
        ... = (a⁻¹ * a) * b : by rw [inverse_mul α a hnzero]
        ... = a⁻¹ * (a * b) : by rw [mul_assoc']
        ... = a⁻¹ * 0 : by rw h
        ... = 0 : by rw mul_zero -- mul_zero isn't defined yet! see page 7

    -- P9
    def mul_distrib' : a * (b + c) = (a * b) + (a * c) := mul_add a b c

    def add_self_is_mul_two : a + a = 2 * a :=
    calc
        a + a   = (a * 1) + a : by rw mul_one'
            ... = (a * 1) + (a * 1) : by rw mul_one'
            ... = a * (1 + 1) : by rw [←mul_distrib']
            ... = a *  2 : by refl
            ... = 2 * a : by rw mul_comm'

    def two_is_not_zero : (2 : α) ≠ (0 : α) :=
    have zero_lt_2 : (0 : α) < (2 : α), from zero_lt_two,
    ne.symm $ ne_of_lt zero_lt_2

    example : (a - b = b - a) → a = b :=
    assume h,
    have a_is_twice_b_minus_a : a = ((2 * b) + -a), from (
        calc
        a = a + 0 : by rw [add_zero a]
        ... = a + (-b + b) : by rw [opp_add]
        ... = (a + -b) + b : by rw [add_assoc']
        ... = (a - b) + b : rfl
        ... = (b - a) + b : by rw h
        ... = (b + -a) + b : rfl
        ... = (b + b) + -a : by rw [add_comm', add_assoc]
        ... = 2 * b  + -a : by rw add_self_is_mul_two
    ),
    have twice_a_is_twice_b : 2 * a = 2 * b, from (
        calc
          2 * a = a + a : by rw add_self_is_mul_two
            ... = ((2 * b) + -a) + a : by rw [←a_is_twice_b_minus_a]
            ... = (2 * b) + (-a + a) : by rw [add_assoc]
            ... = (2 * b) + 0 : by rw [opp_add]
            ... = 2 * b : by rw add_zero
    ),
    calc
        a   = a * 1 : by rw mul_one
        ... = a * (2 * 2⁻¹) : by rw [mul_inverse α 2 (two_is_not_zero α)]
        ... = (2 * b) * 2⁻¹ : by rw [mul_assoc', mul_comm' α a 2, twice_a_is_twice_b]
        ... = b * (2 * 2⁻¹) : by rw [mul_comm' α 2 b, mul_assoc']
        ... = b * 1 : by rw [mul_inverse α 2 (two_is_not_zero α)]
        ... = b : by rw [mul_one]

    def mul_zero' : a * 0 = 0 :=
    have a * 0 = a * 0 + a * 0, from (
        calc
        a * 0   = a * (0 + 0) : by rw [zero_add']
            ... = (a * 0) + (a * 0) : by rw [mul_distrib']
    ),
    show a * 0 = 0, from add_b_eq_self α (a * 0) (a * 0) (eq.symm this)

    def neg_mul_distrib : (-a) * b = -(a * b) :=
    have (-a) * b + a * b = 0, from (
        calc
        (-a) * b + a * b    = b * (-a) + b * a : by rw [mul_comm' α (-a) b, mul_comm' α a b]
                        ... = b * (-a + a) : by rw [←mul_distrib']
                        ... = b * 0 : by rw opp_add
                        ... = 0 : by rw mul_zero'
    ),
    eq.symm $ calc
        -(a * b)    = -(a * b) + 0 : by rw add_zero
                ... = -(a * b) + ((-a) * b + a * b) : by rw this
                ... = -(a * b) + a * b + ((-a) * b) : by simp
                ... = 0 + (-a) * b : by rw opp_add
                ... = (-a) * b : by rw zero_add

end properties
