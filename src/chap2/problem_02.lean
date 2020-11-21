import algebra.big_operators.basic
import data.rat.basic
import tactic.ring

open finset (range)

open_locale big_operators

-- (i)
namespace chap_02_problem_02_i

    private def f : ℕ → ℤ := λ n, 2*n - 1

    private def f_zero : f 0 = -1 := rfl
    private def f_one : f 1 = 1 := rfl

    private def next : ∀ n : ℕ, f (n+1) + (↑n^2 - 1) = (n+1)^2 - 1 :=
    begin
        intro n,
        have h1 : n + (n+1) + n^2 = (n+1)^2, by ring,
        have : f (n+1) = ↑(n+1) + ↑(n+1) - ↑1, by ring,
        have h2 : f (n+1) = (n+1) + (n+1) - 1, by simpa only,
        have : ((↑n:ℤ)+1) + (n+1) - 1 = n + (n+1), by ring,
        calc
        f (n+1) + (↑n^2 - 1) = n + (n+1) + (n^2 - 1) : by rw [h2, this]
        ... = n + (n+1) + n^2 - 1 : by ring
        ... = (n+1)^2 - 1 : by rw_mod_cast [h1]
    end

    def part_i : ∀ (n : ℕ), ∑ i in range (n+1), f i = ↑n^2 - 1
    | 0 := rfl
    | 1 := (
        let n := 1 in
        have left : ∑ i in range (n+1), f i = 0, from rfl,
        have (↑1:ℤ)^2 - 1 = 0, by norm_num,
        by rw [left, <-this]
    )
    | (n+1) := by {
        have ih : ∑ i in range (n+1), f i = ↑n^2 - 1, from part_i n,
        have h1 : ∑ i in range (n+1+1), f i = f (n+1) + ∑ i in range (n+1), f i, from finset.sum_range_succ f (n+1),
        have h2 : f (n+1) + (↑n^2 - 1) = ↑((n+1)^2) - 1, from next n,
        rw [h1, ih, h2],
        push_cast
    }

end chap_02_problem_02_i

-- (ii)
namespace chap_02_problem_02_ii

    private def f : ℕ → ℤ :=
    λ n,
    let n' := int.of_nat n in
    (2*n' - 1)^2

    private def next_f : ∀ n, f (n+1) = 4*n*(n + 1) + 1 :=
    λ n,
    have h1 : ∀ (n:ℤ), (2*(n+1)-1)^2 = 4*n*(n + 1) + 1, from λ n, by ring,
    have f (n+1) = (2*(↑n+1)-1)^2, by refl,
    have f (n+1) = 4*n*(n + 1) + 1, by rwa [h1] at this,
    by exact this

    private def f' : ℕ → ℤ := λ n, n^2 + 1

    private def next_f' : ∀ n : ℕ, f (n+1) + f' n = f' (n+1) :=
    λ n,
    calc
    f (n+1) + f' n = 4*n*(n + 1) + 1 + f' n : by rw [next_f]
    ... = f' (n+1) : sorry

    def part_ii : ∀ (n : ℕ), ∑ i in range (n+1), f i = f' n
    | 0 := (
        let n := 0 in
        have ∑ i in range (n+1), f i = 1, from rfl,
        have f' n = 1, from rfl,
        by refl
    )
    | 1 := (
        let n := 1 in
        have ∑ i in range (n+1), f i = 2, from rfl,
        have f' n = 2, from rfl,
        by cc
    )
    | (n+1) := (
        have ih : ∑ i in range (n+1), f i = f' n, from part_ii n,
        have left : ∑ i in range (n+1+1), f i = f (n+1) + ∑ i in range (n+1), f i, from finset.sum_range_succ f (n+1),
        by rw [left, ih, next_f']
    )

end chap_02_problem_02_ii
