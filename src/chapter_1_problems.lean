import data.rat.basic
import algebra.field
import algebra.ordered_field
import algebra.ordered_group
import algebra.order
import part_1_chapter_1

namespace chapter1_problems

    variables {α : Type} [discrete_linear_ordered_field α]
    variables {a b : α}

    def gizmo (a b : α): ℕ → α
    | 0 := 0
    | (nat.succ n) := a^(n+1) * b + gizmo n + a * b^(n+1)

    example : @gizmo α _ a b (0: ℕ) = (0 : α) := rfl
    example : @gizmo α _ a b (1: ℕ) = a^1 * b + gizmo a b 0 + a * b^1 := rfl
    example : @gizmo α _ a b (2: ℕ) = a^2 * b + gizmo a b 1 + a * b^2 := rfl

    def gizmo_symm (a b : α): ∀ (n : ℕ), gizmo a b n = gizmo b a n
    | 0 := rfl
    | (nat.succ n) := calc
        gizmo a b (nat.succ n)  = a^(nat.succ n) * b + gizmo a b n + a * b^(nat.succ n) : rfl
                            ... = a^(nat.succ n) * b + gizmo b a n + a * b^(nat.succ n) : by rw gizmo_symm n
                            ... = b^(nat.succ n) * a + gizmo b a n + b * a^(nat.succ n) : by simp [add_comm, add_assoc, mul_comm]
                            ... = gizmo b a (nat.succ n) : rfl

    def lt_helper_1 : ∀ n : ℕ, 1 < n + 2 := sorry

    def problem_1_v (a b : α) :
    ∀ n : ℕ, 1 < n → a^n - b^n = (a - b) * (a^(n-1) + gizmo a b (n-2) + b^(n-1))
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
        have l1 : a^(n+3) = a * ((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) + a * b^(n+2), from
            calc
            a^(n+3) = a * (a^(n+2)) : by rw pow_succ
                ... = a * (a^(n+2)) + 0 : by rw add_zero (a * (a^(n+2)))
                ... = a * (a^(n+2)) + (a * 0) : by rw mul_zero
                ... = a * (a^(n+2)) + (a * (-(b^(n+2)) + b^(n+2))) : by rw add_left_neg
                ... = a * (a^(n+2) + (-(b^(n+2)) + b^(n+2))) : by rw ←mul_add
                ... = a * ((a^(n+2) - (b^(n+2))) + b^(n+2)) : by { rw [←add_assoc], reflexivity }
                ... = a * (((a - b) * (a^(n+1) + (gizmo a b n) + b^(n+1))) + b^(n+2)) : by { rw [problem_1_v (n+2) (lt_helper_1 n)], refl }
                ... = a * ((a - b) * (a^(n+1) + gizmo a b n + b^(n+1)) + b^(n+2)) : by simp [mul_assoc, add_assoc]
                ... = a * ((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) + a * b^(n+2) : by rw ←mul_add a,
        have l2: b^(n+3) = b * -((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) + b * a^(n+2), from
            calc
            b^(n+3) = b * (b^(n+2)) : by rw pow_succ
                ... = b * (b^(n+2)) + 0 : by rw add_zero (b * b^(n+2))
                ... = b * (b^(n+2)) + b * 0 : by rw mul_zero
                ... = b * (b^(n+2)) + b * (-(a^(n+2)) + a^(n+2)) : by rw add_left_neg
                ... = b * (b^(n+2)) + b * (-(a^(n+2)) + a^(n+2)) : by rw add_left_neg
                ... = b * (b^(n+2) + -(a^(n+2)) + a^(n+2)) : by rw [←mul_add, add_assoc]
                ... = b * (b^(n+2) - (a^(n+2)) + a^(n+2)) : rfl
                ... = b * (-(a^(n+2) - (b^(n+2))) + a^(n+2)) : by rw neg_sub
                ... = b * (-((a - b) * (a^(n+1) + (gizmo a b n) + b^(n+1))) + a^(n+2)) : by { rw [problem_1_v (n+2) (lt_helper_1 n)], refl }
                ... = b * -((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) + b * a^(n+2) : by rw ←mul_add,
        have l3 : a * b^(n+2) + -(b * a^(n+2)) = (a - b) * 3, from calc
            a * b^(n+2) + -(b * a^(n+2))    = a * b^(n+2) + -(a^(n+2) * b) : by rw [mul_comm b]
                                        ... = a * (b^(n+2) + 0) + -((a^(n+2) + 0) * b) : by rw [add_zero (b^(n+2)), add_zero (a^(n+2))]
                                        ... = a * (b^(n+2) + (-(a^(n+2)) + (a^(n+2)))) + -((a^(n+2) + (-(b^(n+2)) + b^(n+2))) * b) : by rw [neg_add_self, neg_add_self]
                                        ... = a * (b^(n+2) + (-(a^(n+2)) + (a^(n+2)))) + (-(a^(n+2) + (-(b^(n+2)) + b^(n+2))) * b) : by rw [properties.neg_mul_distrib]
                                        ... = a * (b^(n+2) + (-(a^(n+2)) + (a^(n+2)))) + ((-(a^(n+2)) + -(-(b^(n+2)) + b^(n+2))) * b) : by rw [neg_add]
                                        ... = a * (b^(n+2) + (-(a^(n+2)) + (a^(n+2)))) + ((-(a^(n+2)) + (b^(n+2) + -(b^(n+2)))) * b) : by rw [neg_add, neg_neg]
                                        ... = a * (b^(n+2) + (-(a^(n+2)) + (a^(n+2)))) + ((b^(n+2) + -(a^(n+2)) + -(b^(n+2))) * b) : by simp [add_comm, add_assoc]
                                        ... = a * (b^(n+2) + (-(a^(n+2)) + (a^(n+2)))) + b * (b^(n+2) + -(a^(n+2)) + -(b^(n+2))) : by rw [mul_comm b]
                                        ... = a * (b^(n+2) + -(a^(n+2))) + a * a^(n+2) + (b * (b^(n+2) + -(a^(n+2))) + b * -(b^(n+2))) : by simp [mul_add]
                                        ... = (b^(n+2) + -(a^(n+2))) * a + a * a^(n+2) + (b * (b^(n+2) + -(a^(n+2))) + b * -(b^(n+2))) : by rw [mul_comm a]
                                        ... = (b^(n+2) + -(a^(n+2))) * a + a * a^(n+2) + b * (b^(n+2) + -(a^(n+2))) + b * -(b^(n+2)) : by rw [<-add_assoc]
                                        ... = (b^(n+2) + -(a^(n+2))) * a + a * a^(n+2) + (b^(n+2) + -(a^(n+2))) * b + b * -(b^(n+2)) : by rw [mul_comm b]
                                        ... = (b^(n+2) + -(a^(n+2))) * a + (a * a^(n+2) + (b^(n+2) + -(a^(n+2))) * b) + b * -(b^(n+2)) : by rw [<-add_assoc]
                                        ... = (b^(n+2) + -(a^(n+2))) * a + ((b^(n+2) + -(a^(n+2))) * b + a * a^(n+2)) + b * -(b^(n+2)) : by rw [add_comm (a * a^(n+2))]
                                        ... = (b^(n+2) + -(a^(n+2))) * a + (b^(n+2) + -(a^(n+2))) * b + a * a^(n+2) + b * -(b^(n+2)) : by rw [<-add_assoc]
                                        ... = (b^(n+2) + -(a^(n+2))) * (a + b) + a * a^(n+2) + b * -(b^(n+2)) : by rw [mul_add]

                                        ... = (a - b) * 3 : sorry,
                                    --  ... = a * b * b^(n+1) + -b * (a * a^(n+1)) : by rw [properties.neg_mul_distrib]
                                    --  ... = a * (b * b^(n+1)) + -b * (a * a^(n+1)) : by simp [mul_assoc]
                                    --  ... = (b * b^(n+1)) * a + -b * (a * a^(n+1)) : by simp [mul_assoc]
                                    --  ... = a * (b * b^(n+1)) + (-b * a) * a^(n+1) : by simp [mul_assoc]
                                    --  ... = a * (b * b^(n+1)) + (a * -b) * a^(n+1) : by rw [mul_comm (-b) a]
                                    --  ... = a * (b * b^(n+1)) + a * (-b * a^(n+1)) : by simp [mul_assoc]
                                    --  ... = a * ((b * b^(n+1)) + (-b * a^(n+1))) : by rw mul_add
                                    --  ... = a * ((b * (b^(n+1))) + -(b * (a^(n+1)))) : by rw [properties.neg_mul_distrib]
                                    --  ... = a * ((b * (b^(n+1))) - (b * (a^(n+1)))) : rfl
                                    --  ... = a * (b * ((b^(n+1)) - (a^(n+1)))) : by rw ←mul_sub
                                    --  ... = a * b * ((b^(n+1)) - (a^(n+1))) : by rw mul_assoc,
        have next_gizmo : a^(n+1) * b + gizmo a b n + a * b^(n+1) = gizmo a b (n+1), from rfl,
        calc
        a^(n+3) - b^(n+3)   = a * ((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) + a * b^(n+2) - (b * -((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) + b * a^(n+2)) : by rw [l1, l2]
                        ... = a * ((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) + a * b^(n+2) + -(b * -((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) + b * a^(n+2)) : rfl
                        ... = a * ((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) + a * b^(n+2) + -(b * -((a - b) * (a^(n+1) + gizmo a b n + b^(n+1)))) + -(b * a^(n+2)) : by simp [neg_add, add_assoc]
                        ... = a * ((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) + (a * b^(n+2) + -(b * -((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))))) + -(b * a^(n+2)) : by simp [add_assoc]
                        ... = a * ((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) + (-(b * -((a - b) * (a^(n+1) + gizmo a b n + b^(n+1)))) + a * b^(n+2)) + -(b * a^(n+2)) : by simp [add_comm]
                        ... = a * ((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) + -(b * -((a - b) * (a^(n+1) + gizmo a b n + b^(n+1)))) + (a * b^(n+2) + -(b * a^(n+2))) : by simp [add_assoc]
                        ... = a * ((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) + (-b * -((a - b) * (a^(n+1) + gizmo a b n + b^(n+1)))) + (a * b^(n+2) + -(b * a^(n+2))) : by rw properties.neg_mul_distrib
                        ... = a * ((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) + (b * ((a - b) * (a^(n+1) + gizmo a b n + b^(n+1)))) + (a * b^(n+2) + -(b * a^(n+2))) : by rw properties.neg_mul_neg_eq_pos_mul_pos
                        ... = ((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) * a + (((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) * b) + (a * b^(n+2) + -(b * a^(n+2))) : by simp [mul_comm]
                        ... = ((a - b) * (a^(n+1) + gizmo a b n + b^(n+1))) * (a + b) + (a * b^(n+2) + -(b * a^(n+2))) : by rw <-mul_add

                        ... = (a - b) * (a^(n+2) + gizmo a b (n+1) + b^(n+2)) : sorry

              -- sorry -- use square as the base case: a^1 + gizmo 0 + b^1
                       -- we can get a and b factors from both ends, and use them
                       -- to reduce to (a - b) (a + b), out of which we get our gizmo 0. Or
                       -- recursively? Maybe that's easier, let's see.


    -- | 2 twoltn := false.elim (lt_irrefl 2 twoltn)
    -- | (n+3) twoltn := (
    --     have aux : ∀ x y : α, x^(n+3) = x * (x^(n+2) + -(y^(n+2)) + y^(n+2)), from (
    --         λ x y,
    --         calc
    --         x^(n+3) = x * x^(n+2) : by rw pow_succ
    --             ... = x * x^(n+2) + 0 : by rw [add_zero (x * x^(n+2))]
    --             ... = x * x^(n+2) + x * 0 : by rw mul_zero
    --             ... = x * x^(n+2) + x * (-(y^(n+2)) + y^(n+2)) : by rw add_left_neg
    --             ... = x * (x^(n+2) + (-(y^(n+2)) + y^(n+2))) : by rw ←mul_add
    --             ... = x * (x^(n+2) + -(y^(n+2)) + y^(n+2)) : by rw ←add_assoc
    --     ),
    --     have l1 : a^(n+3) = a * (a^(n+2) + -(b^(n+2)) + b^(n+2)), from aux a b,
    --     have l2 : b^(n+3) = b * (b^(n+2) + -(a^(n+2)) + a^(n+2)), from aux b a,
    --     have l3 : gizmo (n + 1) = a^(n+1+1) * b + (gizmo n) + a * b^(n+1+1), by {
    --         cases n,
    --         {   show gizmo (0 + 1) = a^(0+1+1) * b + gizmo 0 + a * b^(0+1+1), from sorry },
    --         sorry
    --     },
    --     calc
    --         a^(n+3) - b^(n+3)   = a^(n+3) + -(b^(n+3)) : rfl
    --                         ... = (a - b) * (a^(n+2) + (gizmo (n+1)) + b^(n+2)) : sorry
    -- )


end chapter1_problems
