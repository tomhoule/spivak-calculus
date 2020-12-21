import algebra.big_operators.basic
import data.nat.choose.basic
import data.nat.parity
import tactic.linarith

open_locale big_operators
open finset (range)
open nat (choose)


-- (i)
theorem part_i : ∀ n, ∑ j in range (n+1), choose n j = 2^n
| 0 := rfl
| (n+1) := (
    have ih : ∑ j in range (n+1), choose n j = 2^n, from part_i n,
    have h1 : (∑ j in range (n+1), choose n j) = choose n n + (∑ j in range n, choose n j), from finset.sum_range_succ (λ j, choose n j) n,
    have h2 : (∑ j in range (n+1), choose n j) = (∑ j in range n, choose n (j+1)) + 1, from (
        calc
        _   = (∑ j in range n, choose n (j+1)) + choose n 0 : finset.sum_range_succ' _ n
        ... = _ : by rw [nat.choose_zero_right n]
    ),
    have h3 : choose (n+1) 0 = 1, from (n + 1).choose_zero_right,
    eq.symm $ calc
    2^(n+1) = 2 * 2^n : pow_succ 2 n
    ... = 2^n + 2^n : by exact two_mul (2 ^ n)
    ... = (∑ j in range (n+1), choose n j) + (∑ j in range (n+1), choose n j) : by rw [ih]
    ... = choose n n + (∑ j in range n, choose n j) + ((∑ j in range n, choose n (j+1)) + 1) : by { nth_rewrite 0 [h1], nth_rewrite 0 h2 }
    ... = (∑ j in range n, choose n j) + (∑ j in range n, choose n (j+1)) + 1 + choose n n : by abel
    ... = ∑ j in range n, choose (n+1) (j+1) + 1 + choose n n : by rw [<-finset.sum_add_distrib, finset.sum_congr rfl (λ j _, show choose n j + choose n (j+1) = choose (n+1) (j+1), from (nat.choose_succ_succ n j).symm)]
    ... = ∑ j in range n, choose (n+1) (j+1) + choose (n+1) 0 + choose n n : by rw [nat.choose_zero_right (n+1)]
    ... = ∑ j in range (n+1), choose (n+1) j + choose n n : by rw [<-finset.sum_range_succ' _ n]
    ... = ∑ j in range (n+1), choose (n+1) j + choose (n+1) (n+1) : by rw [nat.choose_self n, nat.choose_self (n+1)]
    ... = ∑ j in range (n+1+1), choose (n+1) j : by rw [add_comm _ (choose _ _), <-finset.sum_range_succ]
)

-- (ii)
theorem part_ii : ∀ n, 0 < n → ∑ j in range (n+1), (-1 : ℚ)^j * choose n j = 0
| 0 nPos := absurd rfl (ne_of_lt nPos)
| 1 nPos := rfl
| (n+2) (nPos : 0 < (n+2)) := by {
    have ih : ∑ j in range (n+2), (-1 : ℚ)^j * choose (n+1) j = 0 := part_ii (n+1) (nat.succ_pos n),
    -- First use the induction on choose to get two sums.
    rw [finset.sum_range_succ'],
    conv { to_lhs, congr, congr, skip, funext, rw [nat.choose_succ_succ], norm_num, rw [mul_add] },
    rw [finset.sum_add_distrib, add_assoc, nat.choose],
    -- Now reduce the two sums to the predecessor (the left side of the
    -- inductive hypothesis).
    conv { to_lhs, congr, skip, congr, skip, rw [(show 1 = choose (n+1) 0, by simp)] },
    rw [<-finset.sum_range_succ' (λ j, (-1 : ℚ)^j * choose (n+1) j) (n+2)],
    conv { to_lhs, congr, { congr, skip, funext, rw [pow_succ, mul_assoc] } },
    -- . Eliminate the left term
    rw [finset.sum_hom, ih, mul_zero, zero_add],
    -- . Eliminate the right term
    rw [finset.sum_range_succ, ih], simp only [add_zero, nat.cast_zero, nat.choose_succ_self, mul_zero]
}

-- (iii)
theorem part_iii : ∀ n, 0 < n → ∑ l in (range (n+1)).filter odd, choose n l = 2^(n-1)
| 0 nPos := false.elim $ absurd (show 0 = 0, from rfl) (ne_of_lt nPos)
| 1 nPos := rfl
| (n+2) (nPos : 0 < n+2) := by {
    norm_num,
    have ih : ∑ l in (range (n+2)).filter odd, choose (n+1) l = 2^n, by { apply part_iii (n+1) (nat.succ_pos n) },

    sorry
}

--- (iv)
theorem part_iv : ∀ n, ∑ l in (range (n+1)).filter even, choose n l = 2^(n-1) := sorry
