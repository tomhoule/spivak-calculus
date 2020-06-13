import data.rat.basic
import algebra.field
import algebra.ordered_field
import algebra.ordered_group
import algebra.order
import part_1_chapter_1

variables {α : Type} [discrete_linear_ordered_field α]
variables {a b : α}

-- Helper for the series in the expansion of a^n - b^n
def gizmo (a b : α): ℕ → α
| 0 := 0
| (nat.succ n) := a^(n+1) * b + gizmo n + a * b^(n+1)

example : @gizmo α _ a b (0: ℕ) = (0 : α) := rfl
example : @gizmo α _ a b (1: ℕ) = a^1 * b + gizmo a b 0 + a * b^1 := rfl
example : @gizmo α _ a b (2: ℕ) = a^2 * b + gizmo a b 1 + a * b^2 := rfl

def gizmo' (a b : α): ℕ → α
| 0 := a + b
| (n+1) := sorry

example : @gizmo' α _ a b (0: ℕ) = a + b := rfl
example : @gizmo' α _ a b (1: ℕ) = a^2 * b + a + b + a * b^2 := rfl
-- example : @gizmo' α _ a b (2: ℕ) = a^2 * b + gizmo a b 1 + a * b^2 := rfl

def push_gizmo : ∀ n, b * gizmo a b n = gizmo a b n + (a * b^(n+1)) := sorry

def gizmo_symm (a b : α): ∀ (n : ℕ), gizmo a b n = gizmo b a n
| 0 := rfl
| (nat.succ n) := calc
    gizmo a b (nat.succ n)  = a^(nat.succ n) * b + gizmo a b n + a * b^(nat.succ n) : rfl
                        ... = a^(nat.succ n) * b + gizmo b a n + a * b^(nat.succ n) : by rw gizmo_symm n
                        ... = b^(nat.succ n) * a + gizmo b a n + b * a^(nat.succ n) : by simp [add_comm, add_assoc, mul_comm]
                        ... = gizmo b a (nat.succ n) : rfl

def lt_helper_1 : ∀ n : ℕ, 1 < n + 2 := sorry

def problem_1_v (a b : α) :
∀ n : ℕ, 1 < n → a^n - (b^n) = (a - b) * (a^(n-1) + gizmo a b (n-2) + b^(n-1))
| 0 oneltn :=
    have 0 < 1, from nat.lt_succ_self 0,
    false.elim $ absurd oneltn (not_lt_of_lt this)
| 1 oneltn := false.elim (lt_irrefl 1 oneltn)
| 2 _ :=
    calc
    a^2 - b^2   = (a - b) * (a + b) : by rw properties.problem_1_ii
            ... = (a - b) * (a^1 + b^1) : by rw [pow_one, pow_one]
            ... = (a - b) * (a^1 + 0 + b^1) : by rw add_zero
            ... = (a - b) * (a^1 + gizmo a b 0 + b^1) : by rw gizmo
| (n+3) _ :=
    let ih := (a - b) * (a^(n+1) + gizmo a b n + b^(n+1)) in
    have next_gizmo : a^(n+1) * b + gizmo a b n + a * b^(n+1) = gizmo a b (n+1), from rfl,
    have l1 : a^(n+3) = (a - b) * a^(n+2) + b * a^(n+2), from
        calc
        a^(n+3) = a * a^(n+2) : by rw pow_succ
            ... = (a + -b + b) * a^(n+2) : by simp [add_zero, neg_add_self]
            ... = a^(n+2) * ((a + -b) + b) : by rw [mul_comm, add_assoc]
            ... = a^(n+2) * (a + -b) + a^(n+2) * b : by rw [mul_add]
            ... = (a + -b) * a^(n+2) + b * a^(n+2) : by { rw [mul_comm, mul_comm b] }
            ... = (a - b) * a^(n+2) + b * a^(n+2) : rfl,
    -- Just a helper to finish up resolving the right term.
    have l2 : a^(n+2) + b * (a^(n+1) + gizmo a b n + b^(n+1)) = a^(n+2) + gizmo a b (n+1) + b^(n+2), from
        calc
            a^(n+2) + b * (a^(n+1) + gizmo a b n + b^(n+1)) = a^(n+2) + b * (a * a^n + gizmo a b n + b * b^n) : by rw [<-pow_succ a, pow_succ b]
                                                        ... = a^(n+2) + b * (a * a^n) + b * gizmo a b n + b * (b * b^n) : by simp [mul_add, add_assoc]
                                                        ... = a^(n+2) + b * (a^(n+1)) + b * gizmo a b n + b^(n+2) : by rw [pow_succ b, pow_succ b, <-pow_succ a]
                                                        ... = a^(n+2) + b * (a^(n+1) + gizmo a b n) + b^(n+2) : by simp [add_assoc, mul_add]
                                                        ... = a^(n+2) + a^(n+1) * b + b * gizmo a b n + b^(n+2) : by simp [mul_add, add_assoc, mul_comm]
                                                        ... = a^(n+2) + (a^(n+1) * b + gizmo a b n + a * b^(n+1)) + b^(n+2) : by simp [push_gizmo, add_assoc]
                                                        ... = a^(n+2) + gizmo a b (n+1) + b^(n+2) : rfl,
    calc
    a^(n+3) - (b^(n+3)) = a^(n+3) - (b * b^(n+2)) : by rw [pow_succ b]
                    ... = (a - b) * a^(n+2) + b * a^(n+2) - (b * b^(n+2)) : by rw [l1]
                    ... = (a - b) * a^(n+2) + (b * a^(n+2) - (b * b^(n+2))) : by rw [add_sub_assoc]
                    ... = (a - b) * a^(n+2) + (b * (a^(n+2) - (b^(n+2)))) : by rw [mul_sub]
                    ... = (a - b) * a^(n+2) + b * (ih) : by { rw [problem_1_v (n+2) (lt_helper_1 n)], refl }
                    ... = (a - b) * a^(n+2) + (a - b) * b * (a^(n+1) + gizmo a b n + b^(n+1)) : by simp [mul_mul_mul_comm, mul_assoc, mul_comm]
                    ... = (a - b) * a^(n+2) + (a - b) * (b * (a^(n+1) + gizmo a b n + b^(n+1))) : by rw [mul_assoc]
                    ... = (a - b) * (a^(n+2) + b * (a^(n+1) + gizmo a b n + b^(n+1))) : by rw ←mul_add
                    ... = (a - b) * (a^(n+2) + gizmo a b (n+1) + b^(n+2)) : by rw l2
