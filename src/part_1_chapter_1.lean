import data.rat.basic
import algebra.field
import algebra.ordered_field
import algebra.ordered_group
import algebra.order

namespace properties
    open field

    variables (α : Type) [discrete_linear_ordered_field α]
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

    example : -1 * a = -a :=
    calc
    -1 * a  = -(1 * a) : by rw neg_mul_distrib
        ... = -a : by rw [one_mul']


    def neg_mul_neg_eq_pos_mul_pos : (-a) * (-b) = a * b :=
    have (-a) * (-b) + -(a * b) = 0, from (
        calc
        (-a) * (-b) + -(a * b)  = (-a) * (-b) + (-a) * b : by rw ←neg_mul_distrib
                            ... = -a * (-b + b) : by rw mul_distrib'
                            ... = (-a) * 0 : by rw opp_add
                            ... = 0 : by rw mul_zero'
    ),
    eq.symm $ calc
    a * b   = a * b + 0 : by rw [add_zero]
        ... = a * b + (-a * -b + -(a * b)) : by rw this
        ... = (a * b) + -(a * b) + (-a * -b) : by simp
        ... = (-a) * (-b) : by rw [add_opp, zero_add]

    example : ∀ (x : α),  (x^2) - (3 * x) + 2 = (x - 1) * (x - 2) :=
    λ x,
    calc
    (x^2) - (3*x) + 2   = (x * x) - (3*x) + 2 : by rw [pow_succ, pow_one]
                    ... = (x * x) + -(3 * x) + 2 : by refl
                    ... = (x * x) + (-3 * x) + 2 : by rw [←(neg_mul_distrib α 3 x)]
                    ... = (x * x) + (-(2 + 1) * x) + 2 : by refl
                    ... = (x * x) + ((-2 + -1) * x) + 2 : by rw [neg_add]
                    ... = (x * x) + (x * (-2 + -1)) + 2 : by rw [mul_comm' α (-2 + -1) x]
                    ... = (x * x) + ((x * -2) + (x * -1)) + 2 : by rw [mul_distrib']
                    ... = (x * x) + ((x * -2) + (x * -1) + 2) : by rw [add_assoc]
                    ... = (x * x) + ((x * -2) + (x * -1) + (1 * 2)) : by rw [one_mul]
                    ... = (x * x) + ((x * -2) + (x * -1) + (-1 * -2)) : by rw [neg_mul_neg_eq_pos_mul_pos]
                    ... = (x * x) + ((x * -2) + (-1 * x) + (-1 * -2)) : by rw [mul_comm' α x (-1)]
                    ... = (x * x) + ((x * -2) + (((-1) * x) + ((-1) * (-2)))) : by rw [add_assoc' α (x * -2)]
                    ... = (x * x) + ((x * -2) + (-1 * (x + -2))) : by rw mul_distrib'
                    ... = (x * x) + ((x * -2) + -(x + -2)) : by rw [neg_one_mul]
                    ... = (x * x) + ((x * -2) + -(x - 2)) : by refl
                    ... = (x * x) + (x * -2) + -(x - 2) : by rw [add_assoc']
                    ... = (x * (x +- 2)) + -(x - 2) : by rw [mul_distrib']
                    ... = (x * (x - 2)) + -(x - 2) : by refl
                    ... = (x - 2) * x + -(x - 2) : by rw mul_comm'
                    ... = (x - 2) * x + -1 * (x - 2) : by rw [neg_one_mul]
                    ... = (x - 2) * x + (x - 2) * (- 1) : by rw [mul_comm' α (-1)]
                    ... = (x - 2) * (x + -1) : by rw mul_distrib'
                    ... = (x - 2) * (x - 1) : by refl
                    ... = (x - 1) * (x - 2) : by rw mul_comm'

    -- P10
    def trichotomy_law : a < 0 ∨ a = 0 ∨ 0 < a := lt_trichotomy a 0

    -- P11 - closure under addition
    def add_closure : 0 < a → 0 < b → 0 < (a + b) := assume hapos hbpos, add_pos hapos hbpos

    -- P12 - closure under multiplication
    def mul_closure : 0 < a → 0 < b → 0 < (a * b) := assume hapos hbpos, mul_pos hapos hbpos

    def P : set α := λ a, 0 < a

    def a_b_trichotomy : a - b = 0 ∨ (a - b) ∈ (P α) ∨ b - a ∈ (P α) :=
    or.elim (lt_trichotomy a b)
        (λ haltb,
            have 0 < b - a, from (iff.elim_right sub_pos) haltb,
            or.inr $ or.inr $ this
        )
        (λ rest, or.elim rest
            (λ haeqb,
                have a - b = a - a, by rw haeqb,
                have a - b = 0, by rw [this, sub_self],
                or.inl this
            )
            (λ hblta,
                have 0 < a - b, from (iff.elim_right sub_pos) hblta,
                or.inr $ or.inl $ this
            )
        )


    def lt_trans' : a < b → b < c → a < c :=
    assume hab hbc,
    have hbapos :  0 < b - a, from sub_pos.elim_right hab,
    have hcbpos : 0 < c - b, from sub_pos.elim_right hbc,
    have lt : 0 < (c - b) + (b - a), from add_closure α (c - b) (b - a) hcbpos hbapos,
    have (c - b) + (b - a) = c - a, from (
        calc
        (c - b) + (b - a) = (c + -b) + (b + -a) : rfl
                      ... = c + (-b + (b + -a)) : by rw [add_assoc]
                      ... = c + ((-b + b) + -a) : by rw [add_assoc]
                      ... = c + (0 + -a) : by rw [opp_add]
                      ... = c + - a : by rw [zero_add']
                      ... = c - a : rfl
    ),
    have 0 < c - a, from eq.subst this lt,
    show a < c, from sub_pos.elim_left this

    -- The product of two negative numbers is positive.
    def neg_mul_neg_pos : a < 0 → b < 0 → 0 < (a * b) :=
    assume aneg bneg,
    have aneg : - - a < 0, from eq.substr (neg_neg a) aneg,
    have bneg : - - b < 0, from eq.substr (neg_neg b) bneg,
    have min_a_pos : 0 < -a, from neg_lt_zero.elim_left aneg,
    have min_b_pos : 0 < -b, from neg_lt_zero.elim_left bneg,
    have mul_neg : 0 < (-a) * (-b), from mul_closure α (-a) (-b) min_a_pos min_b_pos,
    have -a * -b = a * b, from neg_mul_neg_eq_pos_mul_pos α a b,
    show 0 < (a * b), from eq.subst this mul_neg

    def any_number_squared_is_positive : a ≠ 0 → 0 < a ^ 2 :=
    assume anotzero,
    have mul_of_square : a ^ 2 = a * a, from (
        calc
        a ^ 2   = a * (a ^ 1) : by rw pow_succ
            ... = a * a : by rw [pow_one]
    ),
    have 0 < a * a, from or.elim (trichotomy_law α a)
        (λ hneg, neg_mul_neg_pos α a a hneg hneg)
        (λ rest, or.elim rest
            (λ hzero, absurd hzero anotzero)
            (λ hpos, mul_closure α a a hpos hpos)
        ),
    eq.substr mul_of_square this

    example : (0 : α) < (1 : α) :=
    have one_squared_is_one : (1 : α) ^ 2 = 1, from (
        calc
        (1: α) ^ 2   = (1 : α) * ((1 : α) ^ 1) : pow_succ (1 : α) (1 : ℕ)
            ... = 1 * 1 : by rw [pow_one]
            ... = 1 : by rw [mul_one]
    ),
    have onenezero : (1 : α) ≠ (0 : α), from one_ne_zero,
    have (0 : α) < (1 ^ 2), from any_number_squared_is_positive α 1 onenezero,
    eq.subst one_squared_is_one this

    def le_dichotomy : a ≤ 0 ∨ 0 ≤ a :=
    or.elim (trichotomy_law α a)
        (λ aneg, or.inl $ le_of_lt aneg)
        (λ rest,
        or.elim rest
            (λ azero, or.inl $ le_of_eq azero)
            (λ apos, or.inr $ le_of_lt apos)
        )

    def theorem_one_helper_1 : 0 ≤ b → -a + -b ≤ -a + b :=
    assume hnonneg,
    have -b ≤ 0, from neg_nonpos.elim_right hnonneg,
    have left : -a + -b ≤ -a, from add_le_iff_nonpos_right.elim_right this,
    have right : -a ≤ -a + b, from le_add_of_nonneg_right hnonneg,
    le_trans left right

    def theorem_one_helper_2 : a ≤ 0 → a + b ≤ -a + b :=
    assume anonpos,
    have left : a + b ≤ b, from add_le_iff_nonpos_left.elim_right anonpos,
    have 0 ≤ -a, from neg_nonneg.elim_right anonpos,
    have right : b ≤ -a + b, from (
        have b + 0 ≤ b + -a, from add_le_add (le_refl b) this,
        have that : b + 0 ≤ -a + b, from eq.subst (add_comm b (-a)) this,
        have (has_le.le (b + 0)) = (has_le.le b), by rw [add_zero],
        show b ≤ -a + b, from eq.subst this that
    ),
    le_trans left right

    def theorem_one_helper_3 : ∀ a b : α, a ≤ 0 → 0 ≤ b → abs (a + b) ≤ (abs a) + (abs b) :=
    begin
        intros a b hanonpos hbnonneg,
        have absa : abs a = -a, from abs_of_nonpos hanonpos,
        have absb : abs b = b, from abs_of_nonneg hbnonneg,
        cases (le_dichotomy α (a + b)),
        {   have abssum : abs (a + b) = -(a + b), from abs_of_nonpos h,
            rw [abssum, absa, absb],
            show -(a + b) ≤ -a + b, from (
                have l1 : -(a + b) = -a + -b, by rw neg_add,
                have l2 : -a + -b ≤ -a + b, from theorem_one_helper_1 α a b hbnonneg,
                eq.substr l1 l2
            )
        },
        have abssum : abs (a + b) = a + b, from abs_of_nonneg h,
        rw [abssum, absa, absb],
        show a + b ≤ -a + b, from theorem_one_helper_2 α a b hanonpos
    end

    def theorem_one : abs (a + b) ≤ (abs a) + (abs b) :=
    begin
        cases (le_dichotomy α a),
        all_goals { cases (le_dichotomy α b) },
            {   have absa : abs a = -a, from abs_of_nonpos h,
                have absb : abs b = -b, from abs_of_nonpos h_1,
                have abssum : abs (a + b) = -(a + b), from (
                    have a + b ≤ 0, from add_nonpos h h_1,
                    abs_of_nonpos this
                ),
                have : abs (a + b) = abs a + abs b, from (
                    calc
                    abs (a + b) = -(a + b) : abssum
                            ... = -a + -b : by rw [neg_add]
                            ... = abs a + abs b : by rw [absa, absb]
                ),
                exact le_of_eq this
            },
            { exact theorem_one_helper_3 α _ _ h h_1 },
            {   have l1 : abs (b + a) ≤ (abs b) + (abs a), from theorem_one_helper_3 α _ _ h_1 h,
                have l2 : abs (b + a) ≤ (abs a) + (abs b), from eq.subst (add_comm (abs b) (abs a)) l1,
                exact eq.subst (add_comm b a) l2
            },
        {   have absa : abs a = a, from abs_of_nonneg h,
            have absb : abs b = b, from abs_of_nonneg h_1,
            have abssum : abs (a + b) = a + b, from (
                have 0 ≤ a + b, from add_nonneg h h_1,
                abs_of_nonneg this
            ),
            have : abs (a + b) = abs a + abs b, from (
                calc
                abs (a + b) = a + b : abssum
                        ... = abs a + abs b : by rw [absa, absb]
            ),
            exact le_of_eq this
        },
    end

end properties
