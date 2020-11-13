import data.rat.basic
import algebra.ordered_field
import chap1.problem_01

variables {α : Type} [linear_ordered_field α] [comm_group α]
variables {a b c d : α}

-- (i)
def my_mul_div : b ≠ 0 → c ≠ 0 → a / b = (a*c) / (b*c) :=
assume hbnotzero cnotzero,
calc
    a / b   = a * b⁻¹ : rfl
        ... = a * b⁻¹ * (c * c⁻¹) : by simp only [mul_inv_cancel cnotzero, mul_one]
        ... = a * c * (b⁻¹ * c⁻¹) : by simp only [mul_assoc, mul_comm c]
        ... = a * c * (b * c)⁻¹ : by rw [mul_inv']
        ... = (a*c) / (b*c) : rfl

-- (ii)
def add_fracs : b ≠ 0 → d ≠ 0 → (a/b) + (c/d) = (a*d + b*c) / (b*d) :=
assume bnotzero dnotzero,
calc
    (a/b) + (c/d)   = a * b⁻¹ + c * d⁻¹ : rfl
                ... = a * b⁻¹ * (d * d⁻¹) + c * d⁻¹ * (b * b⁻¹) : by simp only [mul_inv_cancel dnotzero, mul_inv_cancel bnotzero, mul_one]
                ... = (a * d) * (b⁻¹ * d⁻¹) + c * d⁻¹ * (b * b⁻¹) : by simp only [mul_comm d, mul_assoc]
                ... = (a * d) * (b⁻¹ * d⁻¹) + b * c * (b⁻¹ * d⁻¹) : by simp only [mul_comm, mul_mul_mul_comm]
                ... = (a * d) * (b * d)⁻¹ + (b * c) * (b * d)⁻¹ : by simp only [mul_inv']
                ... = (a * d + b * c) * (b * d)⁻¹ : by rw [add_mul]
                ... = (a*d + b*c) / (b*d) : rfl

-- (iii)
def mul_inv''' : a ≠ 0 → b ≠ 0 → (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
assume anotzero bnotzero,
have abnotzero : (a * b) ≠ 0, from mul_ne_zero anotzero bnotzero,
calc
    (a * b)⁻¹   = a * a ⁻¹ * b * b⁻¹ * (a * b)⁻¹ : by simp only [mul_inv_cancel anotzero, mul_inv_cancel bnotzero, one_mul]
            ... = a * b * b⁻¹ * (a * b)⁻¹ * a⁻¹ : by simp only [mul_comm a⁻¹, mul_assoc]
            ... = (a * b) * (a * b)⁻¹ * a⁻¹ * b⁻¹ : by simp only [mul_comm b⁻¹, mul_assoc]
            ... = 1 * a⁻¹ * b⁻¹ : by rw [mul_inv_cancel abnotzero]
            ... = a⁻¹ * b⁻¹ : by rw [one_mul]

-- (iv)
def div_div_mul : b ≠ 0 → d ≠ 0 → (a/b) * (c/d) = (a*c)/(b*d) :=
assume bnotzero dnotzero,
calc
    (a/b) * (c/d)   = (a*b⁻¹) * (c*d⁻¹) : rfl
                ... = (a*c) * (b⁻¹ * d⁻¹) : by simp only [mul_comm c, mul_assoc]
                ... = (a*c) * (b * d)⁻¹ : by rw [mul_inv''' bnotzero dnotzero]
                ... = (a*c)/(b*d) : rfl

def my_inv_inv : a ≠ 0 → (a⁻¹)⁻¹ = a :=
assume anzero,
calc
    (a⁻¹)⁻¹ = a * a⁻¹ * (a⁻¹)⁻¹ : by simp only [mul_inv_mul_self, inv_inv']
        ... = a * (a⁻¹ * (a⁻¹)⁻¹) : by rw mul_assoc
        ... = a * (a * (a⁻¹))⁻¹ : by rw mul_inv'
        ... = a * 1⁻¹ : by rw mul_inv_cancel anzero
        ... = a : by simp only [inv_one, mul_one]

-- (v)
def my_div_div : b ≠ 0 → c ≠ 0 → d ≠ 0 → (a/b) / (c/d) = (a*d)/(b*c) :=
assume bnzero cnzero dnzero,
calc
    (a/b) / (c/d)   = (a*b⁻¹) / (c*d⁻¹) : rfl
                ... = (a*b⁻¹) * (c*d⁻¹)⁻¹ : rfl
                ... = (a*b⁻¹) * (c⁻¹*(d⁻¹)⁻¹) : by rw [mul_inv']
                ... = (a*b⁻¹) * (c⁻¹*d) : by simp only [inv_inv']
                ... = (a*d) * (b⁻¹ * c⁻¹) : by simp only [mul_assoc, mul_comm d]
                ... = (a*d) * (b*c)⁻¹ : by rw mul_inv'
                ... = (a*d)/(b*c) : rfl

-- (vi)
theorem my_div_eq : b ≠ 0 → d ≠ 0 → ((a*d) = (b*c) ↔ (a/b) = (c/d)) :=
assume bnotzero dnotzero,
iff.intro
    (   assume (h : a * d = b * c),
        calc
            a/b = a * b⁻¹ : rfl
            ... = a * b⁻¹ * (d * d⁻¹) : by simp only [mul_inv_cancel dnotzero, mul_one]
            ... = a * d * b⁻¹ * d⁻¹ : by simp only [mul_comm d, mul_assoc]
            ... = b * c * b⁻¹ * d⁻¹ : by rw h
            ... = b * b⁻¹ * c * d⁻¹ : by simp only [mul_comm b⁻¹, mul_assoc]
            ... = c * d⁻¹ : by rw [mul_inv_cancel bnotzero, one_mul]
            ... = c/d : rfl)
    (   assume (h : a/b = c/d),
        calc
            a*d = a * (b⁻¹ * b) * d : by simp only [mul_inv_cancel bnotzero, mul_comm, mul_one]
            ... = a * b⁻¹ * b * d : by simp only [mul_assoc]
            ... = a/b * b * d : rfl
            ... = c/d * b * d : by rw h
            ... = c * d⁻¹ * b * d : rfl
            ... = c * b : by simp only [mul_assoc, mul_comm d⁻¹, mul_inv_cancel dnotzero, mul_one]
            ... = b * c : by rw mul_comm)

theorem my_div_self : a ≠ 0 → b ≠ 0 → ((a/b) = (b/a) ↔ a = b ∨ a = -b) :=
assume anotzero bnotzero,
iff.intro
    (λ (h : a/b = b/a),
        have a*a = b*b, from (iff.elim_right (my_div_eq bnotzero anotzero)) h,
        have a^2 = b^2, by rwa [←pow_two a, ←pow_two b] at this,
        show a = b ∨ a = -b, from sq_eq_sq this
    )
    (λ (h : a = b ∨ a = -b),
        or.elim h
            (λ h, by rw h)
            (λ (h: a = -b),
                calc
                a/b = -b / b : by rw h
                ... = b / -b : by rw [neg_div, div_neg]
                ... = b / a : by rw h
            ))
