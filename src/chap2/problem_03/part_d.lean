import algebra.big_operators.basic
import chap2.problem_03.parts_abc

section part_d

    open_locale big_operators
    open finset (range)
    open problem_03 (choose choose_n_zero choose_self part_a)

    variables { a b : ℚ }

    def helper1 : ∀ n j (hJ : j < n), (choose n (j+1) * a^((n+1)-(j+1)) * b^(j+1) + choose n j * a^((n+1)-(j+1)) * b^(j+1) = choose (n+1) (j+1) * a^((n+1)-(j+1)) * b^(j+1)) := λ n j hJ, by rw [mul_assoc (choose n _), mul_assoc, <-add_mul (choose n (j+1)), add_comm, part_a n j hJ, <-mul_assoc]
    def helper3 : ∀ n, b^(n+1) = choose (n+1) (n+1) * a^(n+1-(n+1)) * b^(n+1) := λ n, by { symmetry, rw [choose_self, one_mul, nat.sub_self (n+1), pow_zero a, one_mul] }
    def helper4 : ∀ n, ∑ j in range n, (choose n (j+1) * a^((n+1)-(j+1)) * b^(j+1) + choose n j * a^((n+1)-(j+1)) * b^(j+1)) = (∑ j in range n, (choose (n+1) (j+1) * a^((n+1)-(j+1)) * b^(j+1))) := λ n, finset.sum_congr (show range n = range n, from rfl) (λ j hJ, helper1 n j (finset.mem_range.mp hJ))

    def binomial_theorem : ∀ (n : ℕ), (a + b)^n = ∑ j in range (n+1), choose n j * a^(n-j) * b^j
    | 0 := (
        let n := 0 in
        have left : (a + b)^n = 1, from pow_zero (a + b),
        have right : ∑ j in range (n+1), choose n j * a^(n-j) * b^j = 1, from rfl,
        eq.trans left right
    )
    | (n+1) := by {
        have ih : (a + b)^n = ∑ j in range (n+1), choose n j * a^(n-j) * b^j, from binomial_theorem n,
        have left : (a + b)^(n+1) = (a+b) * (a + b)^n, from pow_succ (a + b) n,
        have right : ∑ j in range (n+1+1), choose (n+1) j * a^((n+1)-j) * b^j = (a+b) * ∑ j in range (n+1), choose n j * a^(n-j) * b^j, from eq.symm (
            have hAs : a * ∑ j in range (n+1), choose n j * a^(n-j) * b^j = ∑ j in range n, choose n (j+1) * a^((n+1)-(j+1)) * b^(j+1) + a^(n+1), from (
                have helper : ∀ j, j ≤ n → a * (choose n j * a^(n-j) * b^j) = choose n j * a^(n+1-j) * b^j, from (
                    λ j jLeN,
                    have n-j + 1 = (n+1)-j, from nat.sub_add_eq_add_sub jLeN,
                    calc
                    a * (choose n j * a^(n-j) * b^j) = choose n j * (a * a^(n-j)) * b^j : by simp only [mul_assoc, mul_comm a]
                    ... = choose n j * a^(n+1-j) * b^j : by rw [<-pow_succ a, this]
                ),
                calc
                a * ∑ j in range (n+1), choose n j * a^(n-j) * b^j = ∑ j in range (n+1), a * (choose n j * a^(n-j) * b^j) : (eq.symm $ finset.sum_hom _ (λ x, a * x))
                ... = ∑ j in range (n+1), choose n j * a^((n+1)-j) * b^j : finset.sum_congr (show range (n+1) = range (n+1), from rfl) (λ (i : nat) hIN, helper i (nat.le_of_lt_succ $ finset.mem_range.mp hIN))
                ... = ∑ j in range n, choose n (j+1) * a^((n+1)-(j+1)) * b^(j+1) + (choose n 0 * a^(n+1-0) * b^0) : finset.sum_range_succ' (λ j, choose n j * a^((n+1)-j) * b^j) n
                ... = (∑ j in range n, choose n (j+1) * a^((n+1)-(j+1)) * b^(j+1)) + a^(n+1) : by rw [pow_zero b, mul_one, choose_n_zero, one_mul, nat.sub_zero]
            ),
            have hBs : b * ∑ j in range (n+1), choose n j * a^(n-j) * b^j = b^(n+1) + ∑ j in range n, choose n j * a^((n+1)-(j+1)) * b^(j+1), from (
                have helper : ∀ j, b * (choose n j * a^(n-j) * b^j) = choose n j * a^(n-j) * b^(j+1), from (
                    λ (j:ℕ),
                    calc
                    b * (choose n j * a^(n-j) * b^j) = choose n j * a^(n-j) * (b * b^j) : by simp only [mul_assoc, mul_comm b]
                    ... = choose n j * a^(n-j) * b^(j+1) : by rw [pow_succ b]
                ),
                have helper2 : ∀ j, choose n j * a^(n-j) * b^(j+1) = choose n j * a^((n+1)-(j+1)) * b^(j+1), from λ j, by rw [nat.succ_sub_succ n j],
                have helper3 : ∑ j in range n, choose n j * a^(n-j) * b^(j+1) = ∑ j in range n, choose n j * a^((n+1)-(j+1)) * b^(j+1), from finset.sum_congr (show range n = range n, from rfl) (λ j _, helper2 j),
                calc
                b * ∑ j in range (n+1), choose n j * a^(n-j) * b^j = ∑ j in range (n+1), b * (choose n j * a^(n-j) * b^j) : eq.symm $ finset.sum_hom _ (λ x, b * x)
                ... = ∑ j in range (n+1), choose n j * a^(n-j) * b^(j+1) : finset.sum_congr (show range (n+1) = range (n+1), from rfl) (λ j _, helper j)
                ... = (choose n n * a^(n - n) * b^(n+1)) + ∑ j in range n, choose n j * a^(n-j) * b^(j+1) : finset.sum_range_succ (λ j, choose n j * a^(n-j) * b^(j+1)) n
                ... = b^(n+1) + ∑ j in range n, choose n j * a^(n-j) * b^(j+1) : by rw [choose_self n, one_mul (a^_), nat.sub_self n, pow_zero a, one_mul (b^_)]
                ... = _ : by rw [helper3]
            ),
            have helper2 : a^(n+1) = choose (n+1) 0 * a^(n+1-0) * b^0, by { symmetry, rw [choose_n_zero (n+1), one_mul, pow_zero b, mul_one, nat.sub_zero] },
            calc
            (a+b) * ∑ j in range (n+1), choose n j * a^(n-j) * b^j = a * ∑ j in range (n+1), choose n j * a^(n-j) * b^j + b * ∑ j in range (n+1), choose n j * a^(n-j) * b^j : right_distrib a b _
            -- Telescope the two sums by distributing the multiplication, then:
            -- - Noticing that f 0 in the final sequence is a^(n+1)-j (the
            --   choose factor may be a problen)
            -- - Doing the multiplication and extracting the last term at the
            --   other end, so we have two terms and two sums.
            ... = (∑ j in range n, choose n (j+1) * a^((n+1)-(j+1)) * b^(j+1) + a^(n+1)) + (b^(n+1) + ∑ j in range n, choose n j * a^((n+1)-(j+1)) * b^(j+1)) : by rw [hAs, hBs]
            ... = (∑ j in range n, choose n (j+1) * a^((n+1)-(j+1)) * b^(j+1)) + (∑ j in range n, choose n j * a^((n+1)-(j+1)) * b^(j+1)) + a^(n+1) + b^(n+1) : by abel
            ... = ∑ j in range n, (choose n (j+1) * a^((n+1)-(j+1)) * b^(j+1) + choose n j * a^((n+1)-(j+1)) * b^(j+1)) + a^(n+1) + b^(n+1) : by rw [<-finset.sum_add_distrib]
            ... = (∑ j in range n, (choose (n+1) (j+1) * a^((n+1)-(j+1)) * b^(j+1))) + a^(n+1) + b^(n+1) : congr_arg2 has_add.add (congr_fun (congr_arg has_add.add (helper4 n)) (a ^ (n + 1))) rfl
            ... = (∑ j in range (n+1), (choose (n+1) j * a^((n+1)-j) * b^j)) + b^(n+1) : by rw [helper2, finset.sum_range_succ' (λ j, choose (n+1) j * a^((n+1)-j) * b^j) n]
            ... = ∑ j in range (n+1+1), choose (n+1) j * a^((n+1)-j) * b^j : by rw [helper3 n, add_comm, finset.sum_range_succ _ (n+1)]
        ),
        rw [left, ih, <-right]
    }

end part_d
