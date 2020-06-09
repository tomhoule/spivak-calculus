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
    have right : -a ≤ -a + b, from le_add_of_nonneg_right' hnonneg,
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

    -- //////// --
    -- PROBLEMS --
    -- \\\\\\\\ --

    -- Problem 1

    def problem_1_i : ∀ x : α, a ≠ 0 → a * x = a → x = 1 :=
    λ x apos h,
    -- prove by mul_inverse. x = a * a⁻¹
    calc
        x   = x * 1 : eq.symm $ mul_one' α x
        ... = x * (a * a⁻¹) : by rw mul_inverse α a apos
        ... = a * x * a ⁻¹ : by rw [mul_assoc', mul_comm' α x]
        ... = a * a⁻¹ : by rw h
        ... = 1 : mul_inverse α a apos

    def problem_1_ii : ∀ x y : α, (x^2) - (y^2) = (x - y) * (x + y) :=
    λ x y,
    eq.symm $ calc
        (x - y) * (x + y)   = ((x - y) * x) + ((x - y) * y) : by rw [mul_distrib' α (x-y)]
                        ... = ((x + -y) * x) + (( x + -y) * y) : by refl
                        ... = (x * (x + -y)) + (y * (x + -y)) : by rw [mul_comm' α _ x, mul_comm' _ y]
                        ... = ((x * x) + (x * -y)) + ((y * x) + (y * -y)) : by rw [mul_distrib', mul_distrib']
                        ... = ((x ^ 2) + (x * -y)) + ((y * x) + (y * -y)) : by rw [pow_two]
                        ... = (x ^ 2) + ((x * -y) + ((y * x) + (y * -y))) : by rw [add_assoc' α (x^2)]
                        ... = (x ^ 2) + ((x * -y) + ((x * y)) + (y * -y)) : by rw [mul_comm' α y, add_assoc (x * -y)]
                        ... = (x ^ 2) + (x * (y + -y)) + (y * -y) : by simp
                        ... = (x ^ 2) + (x * 0) + (y * -y) : by rw [add_opp]
                        ... = (x ^ 2) + (y * -y) : by rw [mul_zero', add_zero']
                        ... = (x ^ 2) + (y * (y * -1)) : by rw [mul_neg_one y]
                        ... = (x ^ 2) + (y * (-1 * y)) : by rw [mul_comm' α y (-1)]
                        ... = (x ^ 2) + ((y * -1) * y) : by rw [mul_assoc']
                        ... = (x ^ 2) + (-1 * (y * y)) : by rw [mul_comm' α y, mul_assoc']
                        ... = (x ^ 2) + -(y * y) : by rw [neg_one_mul]
                        ... = (x ^ 2) + -(y ^ 2) : by rw [←pow_two]
                        ... = (x ^ 2) - (y ^ 2) : rfl

    -- same in the other direction.
    example : ∀ x y : α, (x^2) - (y^2) = (x - y) * (x + y) :=
    λ x y,
    calc
        (x^2) - (y^2)   = (x^2) + -(y^2) : rfl
                    ... = (x^2) + (-y*y) : by rw [pow_two y, neg_mul_distrib]
                    ... = (x^2) + 0 + (-y * y) : by rw add_zero
                    ... = (x^2) + (x * 0) + (-y * y) : by rw mul_zero
                    ... = (x^2) + (x * (-y + y)) + (-y * y) : by rw [opp_add]
                    ... = (x^2) + ((x * -y) + (x * y)) + (-y * y) : by rw [mul_add]
                    ... = ((x * x) + (x * -y)) + (x * y) + (-y * y) : by rw [pow_two, ←add_assoc]
                    ... = (x * (x + -y)) + (x * y) + (-y * y) : by rw [mul_add]
                    ... = (x * (x + -y)) + ((y * x) + (y * -y)) : by rw [add_assoc, ←mul_comm x, mul_comm (-y)]
                    ... = (x * (x + -y)) + (y * (x + -y)) : by rw [mul_add y]
                    ... = ((x + -y) * x) + ((x + -y) * y) : by rw [mul_comm x, mul_comm y]
                    ... = (x + -y) * (x + y) : by rw [mul_add]
                    ... = (x - y) * (x + y) : rfl

    -- def neg_symm : a = -b → -a = b :=
    -- assume h,
    -- eq.symm $ calc
    --     b   = - - b : eq.symm $ neg_neg b
    --     ... = -a : by rw h

    -- def abs_eq' : abs a = abs b a = b ∨ a = -b :=
    -- assume h,
    -- or.elim (le_dichotomy α a)
    --     (λ anonpos,
    --     have aneg : abs a = -a, from abs_of_nonpos anonpos,
    --     or.elim (le_dichotomy α b)
    --         (λ bnonpos,
    --             have bneg : abs b = -b, from abs_of_nonpos bnonpos,
    --             have abs a = -b, from eq.substr h bneg,
    --             have -a = -b, from eq.subst aneg this,
    --             or.inl $ eq_of_neg_eq_neg this
    --         )
    --         (λ bnonneg,
    --             have abs b = b, from abs_of_nonneg bnonneg,
    --             have abs a = b, from eq.subst this h,
    --             (iff.elim_left $ (abs_eq bnonneg)) this
    --         )
    --     )
    --     (λ anonneg,
    --         have abs a = a, from abs_of_nonneg anonneg,
    --         have a = abs b, from eq.subst this h,
    --         have abs b = a, from eq.symm this,
    --         have b = a ∨ b = -a, from  (iff.elim_left $ (@abs_eq α _ b a anonneg)) this,
    --         have a = b ∨ b = -a, from or.imp_left eq.symm this,
    --         show a = b ∨ a = -b, from or.imp_right (λ (x : b = -a), eq.symm $ neg_symm α b a x) this
    --     )

    def problem_1_iii : a^2 = b^2 → a = b ∨ a = -b :=
    assume h,
    have (a - b) * (a + b) = 0, from (
        eq.symm $ calc
        0   = (a^2) - (a^2) : by rw sub_self
        ... = (a^2) - (b^2) : by rw h
        ... = (a - b) * (a + b) : by rw problem_1_ii
    ),
    or.elim (zero_eq_mul.elim_left (eq.symm $ this))
        (λ h, or.inl $ sub_eq_zero.elim_left h)
        (λ h, or.inr $ add_eq_zero_iff_eq_neg.elim_left h)

    def a_b_sq : (a + b)^2 = a^2 + a * b + a * b + b^2 :=
    calc
        (a + b)^2   = (a + b) * (a + b) : pow_two (a + b)
                ... = (a + b) * a + (a + b) * b : by rw mul_add
                ... = a * (a + b) + b * (a + b) : by simp [mul_comm]
                ... = a * a + a * b + b * a + b * b : by simp [mul_add, add_assoc]
                ... = a^2 + a * b + b * a + b^2 : by simp [pow_two]
                ... = a^2 + a * b + a * b + b^2 : by rw mul_comm

    def problem_1_iv : a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) :=
    have aux : ∀ x y : α, x^3 = (x * (x - y) * (x + y)) + (x * y^2), from (
        λ x y,
        calc
        x^3 = x * (x^2) : by rw pow_succ
        ... = x * (x^2) + 0 : by rw add_zero
        ... = x * (x^2) + (x * 0) : by rw mul_zero
        ... = x * (x^2) + (x * (-(y^2) + y^2)) : by rw opp_add
        ... = x * (x^2 + (-(y^2) + y^2)) : by rw ←mul_add
        ... = x * ((x^2 - (y^2)) + y^2) : by { rw [←add_assoc], reflexivity }
        ... = x * ((x - y) * (x + y) + y^2) : by rw problem_1_ii
        ... = (x * ((x - y) * (x + y))) + (x * y^2) : by rw mul_add
        ... = (x * (x - y) * (x + y)) + (x * y^2) : by simp [mul_assoc]
    ),
    have l1 : a^3 = (a * (a - b) * (a + b)) + (a * b^2), from aux a b,
    have l2 : b^3 = (b * (b - a) * (b + a)) + (b * a^2), from aux b a,
    have (b - a) * (b + a) = -(a - b) * (a + b), from (
        calc
        (b - a) * (b + a)   = (b - a) * (a + b) : by rw add_comm
                        ... = -(a - b) * (a + b) : by rw neg_sub
    ),
    have l2 : b^3 = (b * -(a - b) * (a + b)) + (b * a^2), by simp [mul_assoc, this, l2],
    calc
        a^3 - b^3   = ((a * (a - b) * (a + b)) + (a * b^2)) + -((b * -(a - b) * (a + b)) + (b * a^2)) : by { rw [l1, l2], refl }
                ... = ((a * (a - b) * (a + b)) + (a * b^2)) + -(b * -(a - b) * (a + b)) + -(b * a^2) : by rw [neg_add, <-add_assoc]
                ... = (a * (a - b) * (a + b)) + (a * b^2) + -b * -(a - b) * (a + b) + -(b * a^2) : by simp [add_assoc, neg_mul_distrib]
                -- Move the (a * b^2) and the (-b * a^2) together.
                ... = (a * (a - b) * (a + b)) + ((a * b^2) + -b * -(a - b) * (a + b)) + -(b * a^2) : by rw [<-add_assoc]
                ... = (a * (a - b) * (a + b)) + (-b * -(a - b) * (a + b) + (a * b^2)) + -(b * a^2) : by simp [add_comm]
                ... = a * (a - b) * (a + b) + -b * -(a - b) * (a + b) + ((a * b^2) + -(b * a^2)) : by simp [add_assoc]
                -- done. flatten them.
                ... = a * (a - b) * (a + b) + -b * -(a - b) * (a + b) + ((a * b * b) + -(b * a * a)) : by simp [pow_two, mul_assoc]
                ... = a * (a - b) * (a + b) + -b * -(a - b) * (a + b) + ((a * b * b) - (a * b * a)) : by { rw [mul_comm b, mul_assoc a b a, mul_comm b a, <-mul_assoc], refl }
                ... = a * (a - b) * (a + b) + -b * -(a - b) * (a + b) + ((a * b) * (b - a)) : by rw [<-mul_sub (a * b) b a]
                -- We flattened everything, now let's try to bring the (a - b) out and simplify
                ... = a * (a - b) * (a + b) + b * (a - b) * (a + b) + ((a * b) * (b - a)) : by rw neg_mul_neg_eq_pos_mul_pos
                ... = a * (a - b) * (a + b) + b * (a - b) * (a + b) + ((a * b) * -(a - b)) : by rw [neg_sub]
                ... = a * (a - b) * (a + b) + b * (a - b) * (a + b) + ((a * b) * (-1 * (a - b))) : by rw [neg_one_mul]
                -- Look ma, we have a - b in every term now!
                ... = (a - b) * a * (a + b) + (a - b) * b * (a + b) + (a - b) * - 1 * (a * b) : by simp [mul_assoc, mul_comm]
                ... = (a - b) * (a * (a + b)) + (a - b) * (b * (a + b)) + (a - b) * (- 1 * (a * b)) : by repeat { rw mul_assoc }
                ... = (a - b) * ((a * (a + b)) + (b * (a + b))) + (a - b) * (- 1 * (a * b)) : by rw [<-mul_add]
                ... = (a - b) * (((a * (a + b)) + (b * (a + b))) + (- 1 * (a * b))) : by rw [<-mul_add]
                ... = (a - b) * ((((a + b) * a) + ((a + b) * b)) + (- 1 * (a * b))) : by rw [mul_comm a, mul_comm b]
                ... = (a - b) * (((a + b) * (a + b)) + (- 1 * (a * b))) : by rw [←mul_add]
                ... = (a - b) * ((a + b)^2 + (- 1 * (a * b))) : by rw [pow_two]
                ... = (a - b) * ((a + b)^2 + -(a * b)) : by rw [neg_one_mul]
                ... = (a - b) * ((a^2 + a * b + a * b + b^2) + -(a * b)) : by rw a_b_sq
                ... = (a - b) * (a^2 + a * b + (a * b + -(a * b)) + b^2) : by simp [add_assoc]
                ... = (a - b) * (a^2 + a * b + 0 + b^2) : by rw [←add_opp]
                ... = (a - b) * (a^2 + a * b + b^2) : by rw add_zero


    -- have aux : ∀ x y : α, x^3 = ((x + y) * (x * (x - y))) + (x * y^2), from (
    --     λ x y,
    --     calc
    --     x^3 = x * x^2 : by rw pow_succ
    --     ... = x * x^2 + 0 : by rw add_zero
    --     ... = x * x^2 + x * 0 : by rw mul_zero
    --     ... = x * x^2 + x * (y^2 + - (y^2)) : by rw add_opp
    --     ... = x * (x^2 + (y^2 + -(y^2))) : by rw ←mul_add
    --     ... = x * (x^2 - (y^2) + y^2) : by { rw [add_comm (y^2), ←add_assoc (x^2)], reflexivity }
    --     ... = x * (((x - y) * (x + y)) + y^2) : by rw [problem_1_ii]
    --     ... = (x * ((x - y) * (x + y))) + (x * y^2) : by rw mul_add
    --     ... = (x * ((x + y) * (x - y))) + (x * y^2) : by rw mul_comm (x + y)
    --     ... = (((x + y) * x) * (x - y)) + (x * y^2) : by rw [←mul_assoc x, mul_comm x]
    --     ... = ((x + y) * (x * (x - y))) + (x * y^2) : by rw [mul_assoc]
    -- ),
    -- have l1 : a^3 = ((a + b) * (a * (a - b))) + (a * b^2), from aux a b,
    -- have l2 : b^3 = ((a + b) * (b * (b - a))) + (b * a^2), by { rw [add_comm a], exact aux b a },
    -- calc
    --     -- blech
    --     a^3 - b^3   = (a + b) * (a * (a - b)) + (a * b^2) + -(((a + b) * (b * (b - a))) + (b * a^2)): by { rw [l1, l2], refl }
    --             ... = (a + b) * (a * (a - b)) + -(((a + b) * (b * (b - a))) + (b * a^2)) + (a * b^2) : by simp [add_assoc, add_comm]
    --             ... = (a + b) * (a * (a - b)) + (-((a + b) * (b * (b - a))) + -(b * a^2)) + (a * b^2) : by rw neg_add
    --             ... = (a + b) * (a * (a - b)) + -((a + b) * (b * (b - a))) + -(b * a^2) + (a * b^2) : by simp [add_assoc]
    --             ... = (a + b) * (a * (a - b)) -((a + b) * (b * (b - a))) + -(b * a^2) + (a * b^2) : rfl
    --             ... = (a + b) * ((a * (a - b)) - (b * (b - a))) + -(b * a^2) + (a * b^2) : by rw ←mul_sub
    --             ... = (a + b) * ((a * a - a * b) - (b * (b - a))) + -(b * a^2) + (a * b^2) : by rw <-mul_sub
    --             ... = (a + b) * ((a * a - a * b) - (b * b - b * a)) + -(b * a^2) + (a * b^2) : by rw <-mul_sub b
    --             ... = (a + b) * ((a^2 - a * b) - (b^2 - b * a)) + -(b * a^2) + (a * b^2) : by rw [pow_two a, pow_two b]
    --             ... = (a + b) * (a^2 + -(a * b) + -(b^2 - a * b)) + -(b * a^2) + (a * b^2) : by {rw [mul_comm b], refl }
    --             ... = (a + b) * (a^2 + -(a * b) + (a * b + -(b^2))) + -(b * a^2) + (a * b^2) : by { rw [neg_sub], refl }
    --             ... = (a + b) * (a^2 + (-(a * b) + a * b) + -(b^2)) + -(b * a^2) + (a * b^2) : by simp [add_assoc]
    --             ... = (a + b) * (a^2 - (b^2)) + -(b * a^2) + (a * b^2) : by { rw [opp_add, add_zero], reflexivity }
    --             ... = (a + b) * ((a - b) * (a + b)) + -(b * a^2) + (a * b^2) : by rw [problem_1_ii]
    --             ... = (a + b) * ((a - b) * (a + b)) + -(b * (a * a)) + (a * b^2) : by rw [pow_two]
    --             ... = (a + b) * ((a - b) * (a + b)) + -(b * a * a) + (a * b^2) : by rw [mul_assoc]
    --             ... = (a + b) * ((a - b) * (a + b)) + -(a * b * a) + (a * b^2) : by rw [mul_comm b]
    --             ... = (a + b) * ((a - b) * (a + b)) + -(a * b * a) + (b^2 * a) : by rw [mul_comm a (b^2)]
    --             ... = (a + b) * ((a - b) * (a + b)) + (-(a * b * a) + (b^2 * a)) : by rw [add_assoc]
    --             ... = (a + b) * ((a - b) * (a + b)) + ((b^2 * a) - (a * b * a)) : by { rw [add_comm (-(a * b * a))], refl }
    --             ... = (a + b) * ((a - b) * (a + b)) + ((b^2 - (a * b)) * a) : by rw sub_mul _ _ a
    --             ... = (a - b) * (a^2 + a * b + b^2) : sorry


    -- have l1 : a^3 = a * (a^2 + a*b + b^2), from (
    --     calc
    --         a^3 = a * (a^2) : by rw pow_succ
    --         ... = a * (a^2) + 0 : by rw [add_zero (a * a^2)]
    --         ... = a * (a^2) + a * 0 : by rw [mul_zero]
    --         ... = a * (a^2) + a * (b^2 + -(b^2)) : by rw [add_opp]
    --         ... = a * (a^2 + -(b^2) + b^2) : by rw [←mul_add, add_comm (b^2), add_assoc (a^2)]
    --         ... = a * (a^2 - (b^2) + b^2) : sorry
    --         ... = a * ((a - b) * (a + b) + b^2) : by rw problem_1_ii
    --         ... = a * (a ^ 2 + a*b + b^2) : sorry
    -- ),
    -- have l2 : b^3 = b * (a^2 + a*b + b^2), from sorry,
    -- calc
    --     a^3 - b^3   = a * (a^2 + a * b + b^2) - b * (a^2 + a * b + b^2) : by rw [l1, l2]
    --             ... = (a - b) * (a^2 + a * b + b^2) : by rw [mul_comm a, mul_comm b, ←mul_sub, mul_comm]

    -- calc
    --    a^3 - b^3    = a^3 + -(b^3) : rfl
    --             ... = a^3 + -(b * b^2) : by rw [pow_succ b]
    --             ... = a^3 + -b * b^2 : by rw [neg_mul_distrib]
    --             -- Introduce a middle term to factor in `b`s in the left term.
    --             ... = a^3 + 0 + -b * b^2 : by rw [add_zero]
    --             ... = a^3 + (a * 0) + -b * b^2 : by rw [mul_zero]
    --             ... = a^3 + (a * (b^2 + -(b^2))) + -b * b^2 : by rw [add_opp]
    --             ... = (a * a^2 + (a * (b^2 +-(b^2)))) + -b * b^2 : by rw [pow_succ]
    --             ... = (a * (a^2 + b^2 + -(b^2))) + -b * b^2 : by rw [←mul_add, add_assoc]
    --             -- We merged our middle term to the left, now time to do the same to the right.
    --             ... = (a * (a^2 + a * b + b^2)) + 0 + -b * b^2 : by rw [add_zero]
    --             ... = (a * (a^2 + a * b + b^2)) + ((-b) * 0) + -b * b^2 : by rw [mul_zero]
    --             ... = (a * (a^2 + a * b + b^2)) + ((-b) * (a + -a)) + -b * b^2 : by rw [←add_opp]
    --             ... = (a * (a^2 + a * b + b^2)) + (((-b) * (a + -a)) + -b * b^2) : by rw [add_assoc]
    --             ... = (a * (a^2 + a * b + b^2)) + ((-b) * (a + -a + b^2)) : by rw [←mul_add]

    --             ... = (a - b) * (a^2 + a * b + b^2) : sorry

    def gizmo (a b : α) : Π (n : ℕ), α
    | 0 := 0
    | 1 := (a * b)
    | (nat.succ n) := (a^n * b + gizmo n + a * b^n)

    def problem_1_v (a b : α) :
    ∀ n : ℕ, 3 < n →
        a^n - b^n = (a - b) * (a^(n-1) + a^(n-2) * b + (gizmo α a b n) + a * b^(n-2) +b^(n-1))
    | 0 threeltn := sorry
    | 1 threeltn := sorry
    | 2 threeltn := sorry
    | 3 threeltn := sorry
    | (nat.succ (nat.succ n)) twoltn := (
        have aux : ∀ x y : α, x^(n+2) = x * (x^(n+1) + -(y^(n+1)) + y^(n+1)), from (
            λ x y,
            calc
            x^(n+2) = x * x^(n+1) : by rw pow_succ
                ... = x * x^(n+1) + 0 : by rw [add_zero (x * x^(n+1))]
                ... = x * x^(n+1) + x * 0 : by rw mul_zero
                ... = x * x^(n+1) + x * (-(y^(n+1)) + y^(n+1)) : by rw opp_add
                ... = x * (x^(n+1) + (-(y^(n+1)) + y^(n+1))) : by rw ←mul_add
                ... = x * (x^(n+1) + -(y^(n+1)) + y^(n+1)) : by rw ←add_assoc
        ),
        have l1 : a^(n+2) = a * (a^(n+1) + -(b^(n+1)) + b^(n+1)), from aux a b,
        have l2 : b^(n+2) = b * (b^(n+1) + -(a^(n+1)) + a^(n+1)), from aux b a,
        sorry
        -- calc
        --     a^(n+2) - b^(n+2)   = a^(n+2) + -(b^(n+2)) : rfl
        --                     ... = (a - b) * (a^(n-1) + a^(n-2) * b + (gizmo α a b n) + a * b^(n-2) +b^(n-1)) : sorry
    )

end properties
