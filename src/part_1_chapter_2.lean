import algebra.big_operators.basic
import tactic.interactive

open_locale big_operators
open finset (range)

def nat_seq_sum_aux : ∀ (n : ℕ), (↑(n+1):ℚ) + ↑(n*(n+1))/2 = ↑((n+1)*(n+1+1))/2 :=
λ n,
let n' := (↑n:ℚ) in
have n+1 + (n+1) + n*(n+1) = (n+1)*(n+1+1), by rw [add_assoc, add_comm (n+1) (n*(n+1)), mul_comm, <-nat.mul_succ (n+1), add_comm (n+1), <- nat.mul_succ (n+1)],
have (↑(n+1):ℚ) + ↑(n*(n+1))/2 = ↑((n+1)*(n+1+1))/2, from (
    calc
    ↑(n+1) + ↑(n*(n+1))/2 = n'+1 + (n*(n+1))/2 : by push_cast
    ... = (n'+1 + (n+1))/2 + n*(n+1)/2 : by rw [add_self_div_two]
    ... = (n'+1 + (n'+1) + n*(n+1))/2 : by rw [div_add_div_same]
    ... = ((n'+1)*(n'+1+1))/2 : by rw_mod_cast this
    ... = ↑(((n:ℕ)+1)*(n+1+1))/2 : by norm_cast
),
by cc

def nat_seq_sum : ∀ (n : ℕ), (↑(∑ i in range (n+1), i):ℚ) = ↑(n * (n+1))/2
| 0 := by {
    have : ∑ i in range (0+1), i = 0, from rfl,
    have : ↑(∑ i in range (0+1), i) = (0 : ℚ), by exact_mod_cast this,
    by norm_num
}
| (n+1) := by {
    let n' := (↑n:ℚ),
    have ih : (↑(∑ i in range (n+1), i):ℚ) = ↑(n*(n+1))/2, from nat_seq_sum n,
    have : (∑ i in range (n+1+1), i) = (n+1) + (∑ i in range (n+1), i), by refine finset.sum_range_succ _ _,
    have left : (↑(∑ i in range (n+1+1), i):ℚ) = (n'+1) + ↑(∑ i in range (n+1), i), by exact_mod_cast this,
    have : (↑(n+1):ℚ) + ↑(n*(n+1))/2 = ↑((n+1)*(n+1+1))/2, from nat_seq_sum_aux n,
    rw <-ih at this,
    exact eq.trans left this
}
