import algebra.big_operators
import data.real.basic

open finset (range)

open_locale big_operators

-- (i)
def part_i_aux : ∀ (n : ℕ), 6*((n+1)^2) + (n*(n+1)*(2*n+1)) = (n+1)*(n+2)*(2*(n+1)+1) := λ n, by ring

def part_i : ∀ (n : ℕ), ↑(∑ i in range (n+1), i^2) = ((↑n:ℚ)*(n+1)*(2*n + 1))/6
| 0 := (
    let n := 0 in
    have (↑(∑ i in range (n+1), i^2): ℚ) = 0, from rfl,
    have ((↑n:ℚ)*(n+1)*(2*n+1))/6 = 0, by norm_num,
    by linarith
)
| 1 := (
    let n := 1 in
    have ↑(∑ i in range (n+1), i^2) = (1:ℚ), from rfl,
    have ((↑n:ℚ)*(n+1)*(2*n+1))/6 = 1, by norm_num,
    by linarith
)
| (n+1) := by {
    let n' := (↑n:ℚ),
    have ih : ↑(∑ i in range (n+1), i^2) = (n'*(n+1)*(2*n+1))/6, from part_i n,
    have sum : (↑(∑ i in range (n+1+1), i^2):ℚ) = (n'+1)^2 + ∑ i in range (n+1), i^2, by apply_mod_cast finset.sum_range_succ _ _,
    calc
    (↑(∑ (i:ℕ) in range (n+1+1), i^2):ℚ) = (n'+1)^2 + (∑ (i:ℕ) in range (n+1), i^2) : by rw [sum]
    ... = (n'+1)^2 + ↑(∑ i in range (n+1), i^2) : by push_cast
    ... = (n'+1)^2 + (n'*(n+1)*(2*n+1))/6 : by rw [ih]
    ... = (6*(n+1)^2 + n*(n+1)*(2*n+1))/6 : by ring
    ... = ((n+1)*(n+1+1)*(2*(n+1)+1))/6 : by rw_mod_cast part_i_aux
}

-- (ii)
def part_ii : ∀ (n : ℕ), ∑ i in range (n+1), i^3 = (∑ i in range (n+1), i)^2
| 0 := (
    let n := 0 in
    have ∑ i in range (n+1), i^3 = 0, from rfl,
    have (∑ i in range (n+1), i)^2 = 0, from zero_pow zero_lt_two,
    by cc
)
| (n+1) := by {
    have ih : ∑ i in range (n+1), i^3 = (∑ i in range (n+1), i)^2, from part_ii n,
    have succ :  ∑ (i : ℕ) in range (n + 1 + 1), i ^ 3 = (n+1)^3 + (∑ (i : ℕ) in range (n + 1), i ^ 3), by refine finset.sum_range_succ _ _,
    calc
    ∑ (i : ℕ) in range (n + 1 + 1), i ^ 3 = (n+1)^3 + (∑ (i : ℕ) in range (n + 1), i ^ 3) : by refine finset.sum_range_succ _ _
    ... = (n+1)^3 + (∑ i in range (n+1), i)^2 : by rw [ih]
    ... = (n+1)^3 + (∑ i in range (n+1), i)^2 : by ring
    ... = (∑ i in range (n+1+1), i)^2 : sorry
}
