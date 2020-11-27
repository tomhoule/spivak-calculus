import algebra.ordered_field
import algebra.big_operators

variables {α : Type} [linear_ordered_field α]
variables {a b : α}

-- (i)
def mul_eq_self : a ≠ 0 → a * b = a → b = 1 :=
assume anotzero h,
calc
    b   = a⁻¹ * a * b : by simp only [one_mul, inv_mul_cancel anotzero]
    ... = a⁻¹ * (a * b) : by rw [mul_assoc]
    ... = a⁻¹ * a : by rw h
    ... = 1 : by rw inv_mul_cancel anotzero

-- (ii)
def sq_sq_sub : a^2 - b^2 = (a - b) * (a + b) :=
calc
    a^2 - b^2   = a * (a + b - b) - (b * (b + a - a)) : by simp only [pow_two, add_sub_cancel]
            ... = a * (a + b) + a * -b - (b * (b + a) + b * -a) : by simp only [mul_add, add_neg_cancel_right, mul_neg_eq_neg_mul_symm, add_sub_cancel]
            ... = a * (a + b) + a * -b + -(b * (b + a) + b * -a) : rfl
            ... = a * (a + b) + a * -b + -(b * (b + a)) + -(b * -a) : by simp only [neg_add, add_assoc]
            ... = (a + b) * a + a * -b + (a + b) * -b + b * a : by simp only [add_comm, mul_comm, mul_neg_eq_neg_mul_symm, neg_neg]
            ... = (a + b) * a + (a + b) * -b + (a * -b + a * b) : by rw [add_assoc, add_add_add_comm, mul_comm b a]
            ... = (a + b) * a + (a + b) * -b : by simp only [add_zero, mul_neg_eq_neg_mul_symm, add_left_neg]
            ... = (a + -b) * (a + b) : by rw [←mul_add (a + b), mul_comm (a + b)]
            ... = (a - b) * (a + b) : rfl

-- (iii)
def sq_eq_sq : a^2 = b^2 → a = b ∨ a = -b :=
assume h,
have (a - b) * (a + b) = 0, from (
    eq.symm $ calc
    0   = (a^2) - (a^2) : by rw sub_self
    ... = (a^2) - (b^2) : by rw h
    ... = (a - b) * (a + b) : by rw sq_sq_sub
),
or.elim (zero_eq_mul.elim_left (eq.symm $ this))
    (λ h, or.inl $ sub_eq_zero.elim_left h)
    (λ h, or.inr $ add_eq_zero_iff_eq_neg.elim_left h)

-- (iv)
def cube_cube_sub : a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) :=
calc
    a^3 - b^3   = a * a^2 - b * b^2 : by simp only [pow_succ]
            ... = a * ((a^2 - b^2) + b^2) - b * b^2 : by simp only [sub_add_cancel]
            ... = a * (a^2 - b^2) + a * b^2 - b * b^2 : by rw mul_add
            ... = a * (a^2 - b^2) + (a - b) * b^2 : by rw [add_sub_assoc, sub_mul]
            ... = a * (a - b) * (a + b) + (a - b) * b^2 : by rw [sq_sq_sub, mul_assoc]
            ... = (a - b) * (a * (a + b)) + (a - b) * b^2 : by rw [mul_comm a, mul_assoc]
            ... = (a - b) * (a * (a + b) + b^2) : by rw [←mul_add]
            ... = (a - b) * (a^2 + a * b + b^2) : by simp only [mul_add, pow_succ, mul_one, pow_zero]

-- (v)
section v

    open_locale big_operators

    private def gizmo (a b : α) : ℕ → α :=
    λ n, ∑ m in finset.range (n+1), a^(n - m) * b^m

    example : gizmo a b 0 = a^(0-0) * b^0 + 0 := rfl
    example : gizmo a b 0 = 1 * 1 + 0 := rfl

    example : gizmo a b 1 = a^(1-0) * b^0 + (a^(1-1) * b^1 + 0) := rfl
    example : gizmo a b 1 = a^1 * 1 + (1 * b^1 + 0) := rfl

    example : gizmo a b 2 = a^(2-0) * b^0 + (a^(2-1) * b^1 + (a^(2-2) * b^2 + 0)) := rfl
    example : gizmo a b 2 = a^2 * 1 + (a^1 * b^1 + (1 * b^2 + 0)) := rfl

    lemma next_gizmo : ∀ n, gizmo a b (n+1) = a * gizmo a b n + b^(n+1) :=
    assume n,
    let expanded_n := (∑ m in finset.range (n+1), a^(n - m) * b^m),
        middle_f := λ (m : ℕ), a^(n+1 - m) * b^m,
        middle := (∑ m in finset.range (n+1), middle_f m),
        expanded_succn := (∑ m in finset.range (n+2), middle_f m) in
    have l1 : a * expanded_n = middle, from (
        have helper : ∀ (m : ℕ) (mlen : m ≤ n), (a * a^(n - m)) * b^m = a^(n+1 - m) * b^m, from (
            λ m mlen,
            calc
            (a * a^(n - m)) * b^m   = a^((n - m) + 1) * b^m : by rw pow_succ
                                ... = a^((n+1) - m) * b^m : by rw [nat.succ_sub mlen]
        ),
        have ∀ m, m ∈ finset.range (n+1) → m ≤ n, from (
            assume m h,
            have m < (n+1), from finset.mem_range.elim_left h,
            nat.le_of_lt_succ this
        ),
        calc
        a * expanded_n  = ∑ m in finset.range (n+1), a * (a^(n - m) * b^m) : by rw finset.sum_hom (finset.range (n+1)) (λ x, a * x)
                    ... = ∑ m in finset.range (n+1), (a * a^(n - m)) * b^m : by simp only [mul_assoc]
                    ... = middle : by rw [finset.sum_congr rfl (λ m h, helper m (this m h))] -- need to find a way to inject the proof that m ≤ n
    ),
    have l2 : middle + b^(n+1) = expanded_succn, from (
        have h1 : expanded_succn = middle_f (n+1) + middle, from finset.sum_range_succ middle_f (n+1),
        have h2 : middle_f (n+1) = b^(n+1), from (
            calc
            middle_f (n+1)  = a^(n+1 - (n+1)) * b^(n+1) : rfl
                        ... = b^(n+1) : by simp only [one_mul, nat.sub_self, pow_zero]
        ),
        calc
            middle + b^(n+1)    = b^(n+1) + middle : by rw add_comm
                            ... = middle_f (n+1) + middle : by rw h2
                            ... = expanded_succn : by rw h1
    ),
    calc
        gizmo a b (n+1) = expanded_succn : rfl
                    ... = middle + b^(n+1) : by rw l2
                    ... = a * expanded_n + b^(n+1) : by rw l1
                    ... = a * gizmo a b n + b^(n+1) : rfl

    def pow_pow_sub : ∀ (n : ℕ) (npos : 0 < n), a^n - b^n = (a - b) * gizmo a b (n-1)
    | 0 h := false.elim $ lt_irrefl 0 h
    | 1 h := calc
        a^1 - b^1   = (a - b) : by rw [pow_one, pow_one]
                ... = (a - b) * (1 * 1 + 0) : by simp only [mul_one, add_zero]
                ... = (a - b) * gizmo a b (1-1) : rfl
    | (n+2) h :=
        have lt_helper : 0 < n+1, from nat.zero_lt_succ n,
        calc
        a^(n+2) - b^(n+2)   = a * a^(n+1) - (b * b^(n+1)) : by rw [pow_succ a, pow_succ b]
                        ... = a * ((a^(n+1) - b^(n+1)) + (b^(n+1))) - b * b^(n+1) : by simp only [sub_add_cancel]
                        ... = a * (a^(n+1) - b^(n+1)) + (a * b^(n+1) - (b * b^(n+1))) : by rw [mul_add, add_sub_assoc]
                        ... = a * (a^(n+1) - b^(n+1)) + (a - b) * b^(n+1) : by rw [sub_mul]
                        ... = a * ((a - b) * gizmo a b n) + (a - b) * b^(n+1) : by { rw [pow_pow_sub (n+1) lt_helper], refl }
                        ... = (a - b) * (a * gizmo a b n) + (a - b) * b^(n+1) : by simp only [mul_comm a, mul_assoc]
                        ... = (a - b) * (a * gizmo a b n + b^(n+1)) : by rw mul_add

                        ... = (a - b) * gizmo a b (n+1) : by rw next_gizmo n


    def pow_pow_sub_five (x y : α) : x^5 - y^5 = (x-y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) :=
    have h1 : gizmo x y 4 = x^(4-0)*y^0 + (x^(4-1)*y^(0+1) + (x^(4-2)*y^(0+2) + (x^(4-3)*y^(0+3) + (x^(4-4)*y^(0+4) + 0)))), from rfl,
    have h2 : x^(4-0)*y^0 + (x^(4-1)*y^(0+1) + (x^(4-2)*y^(0+2) + (x^(4-3)*y^(0+3) + (x^(4-4)*y^(0+4) + 0)))) =
        x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4, by rw [
            <-add_assoc, <-add_assoc, <-add_assoc, <-add_assoc, add_zero, pow_zero x, pow_zero y, mul_one, one_mul, pow_one x, pow_one y
        ],
    have x^5-y^5 = (x-y) * gizmo x y 4, by rw [pow_pow_sub 5 (by norm_num)],
    by rwa [h1, h2] at this

end v



-- (vi)
def cube_cube_add : a^3 + b^3 = (a + b) * (a^2 - (a * b) + b^2) :=
calc
    a^3 + b^3   = a^3 + - -(b^3) : by rw [neg_neg]
            ... = a^3 - -(b^3) : rfl
            ... = a^3 - (-b)^3 : by simp only [pow_succ, neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg, pow_zero]
            ... = (a - (-b)) * (a^2 + a * -b + (-b)^2) : by rw [@cube_cube_sub]
            ... = (a + b) * (a^2 + a * -b + (-b)^2) : by rw sub_neg_eq_add
            ... = (a + b) * (a^2 + -(a * b) + b^2) : by simp only [mul_neg_eq_neg_mul_symm, neg_square]
            ... = (a + b) * (a^2 - (a*b) + b^2) : rfl
