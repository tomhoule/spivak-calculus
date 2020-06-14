import algebra.ordered_field

variables (α : Type) [discrete_linear_ordered_field α] [comm_group α]
variables {a b c d : α}

-- (i)
def mul_div : b ≠ 0 → c ≠ 0 → a / b = (a*c) / (b*c) :=
assume hbnotzero cnotzero,
calc
    a / b   = a * b⁻¹ : rfl
        ... = a * b⁻¹ * (c * c⁻¹) : by simp [mul_inv_cancel cnotzero]
        ... = a * c * (b⁻¹ * c⁻¹) : by simp [mul_assoc, mul_comm c]
        ... = a * c * (b * c)⁻¹ : by rw [mul_inv'']
        ... = (a*c) / (b*c) : rfl

-- (ii)
def add_fracs : b ≠ 0 → d ≠ 0 → (a/b) + (c/d) = (a*d + b*c) / (b*d) :=
assume bnotzero dnotzero,
calc
    (a/b) + (c/d)   = a * b⁻¹ + c * d⁻¹ : rfl
                ... = a * b⁻¹ * (d * d⁻¹) + c * d⁻¹ * (b * b⁻¹) : by simp [mul_inv_cancel dnotzero, mul_inv_cancel bnotzero]
                ... = (a * d) * (b⁻¹ * d⁻¹) + c * d⁻¹ * (b * b⁻¹) : by simp [mul_comm d, mul_assoc]
                ... = (a * d) * (b⁻¹ * d⁻¹) + b * c * (b⁻¹ * d⁻¹) : by simp [mul_comm, mul_assoc, mul_mul_mul_comm]
                ... = (a * d) * (b * d)⁻¹ + (b * c) * (b * d)⁻¹ : by simp [mul_inv'']
                ... = (a * d + b * c) * (b * d)⁻¹ : by rw [add_mul]
                ... = (a*d + b*c) / (b*d) : rfl

-- (iii)
def mul_inv''' : a ≠ 0 → b ≠ 0 → (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
assume anotzero bnotzero,
have abnotzero : (a * b) ≠ 0, from mul_ne_zero anotzero bnotzero,
calc
    (a * b)⁻¹   = a * a ⁻¹ * b * b⁻¹ * (a * b)⁻¹ : by simp [mul_inv_cancel anotzero, mul_inv_cancel bnotzero]
            ... = a * b * b⁻¹ * (a * b)⁻¹ * a⁻¹ : by simp [mul_comm (a⁻¹), mul_assoc]
            ... = (a * b) * (a * b)⁻¹ * a⁻¹ * b⁻¹ : by simp [mul_comm (b⁻¹), mul_assoc]
            ... = 1 * a⁻¹ * b⁻¹ : by rw [mul_inv_cancel abnotzero]
            ... = a⁻¹ * b⁻¹ : by rw [one_mul]
