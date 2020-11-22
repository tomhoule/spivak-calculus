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
        have h2 : f (n+1) + (↑n^2 - 1) = ↑((n+1)^2) - 1, by exact next n,
        rw [h1, ih, h2],
        push_cast
    }

end chap_02_problem_02_i

-- (ii)
namespace chap_02_problem_02_ii

    private def f : ℕ → ℚ :=
    λ n,
    let n' := int.of_nat n in
    (2*n' - 1)^2

    example : f 0 = 1 := rfl
    example : f 1 = 1 := rfl
    example : f 2 = 9 := rfl
    example : f 3 = 25 := rfl

    -- Note that (2n)² = 4n². So the sums of the (2n - 1)² is going to be the
    -- sum of the (2n)² plus the sum of the (-4n + 1) terms.
    example : ∀ n : ℕ, f n = 4*n^2 - 4*n + 1 :=
    λ n,
    calc
    f n = (2*n - 1)^2 : by refl
    ... = 4*n^2 - 4*n + 1 : by ring

    def right_f : ℕ → ℚ := λ n, ((-4):rat) * n + 1

    def right : ∀ n : ℕ, ∑ i in range (n+1), right_f i = -4 * (n * (n+1))/2 + (n+1)
    | 0 := (
        have -(4:rat) * 0 + 1 = 1, from rfl,
        have -(4:rat) * (0*(0+1))/2 + (0+1) = 1, from rfl,
        rfl
    )
    | (n+1) := by {
        have ih : ∑ i in range (n+1), right_f i = -4 * (n * (n+1))/2 + (n+1), from right n,
        have left : ∑ i in range (n+1+1), right_f i = (-(4:rat) * (n+1) + 1) + ∑ i in range (n+1), right_f i, from finset.sum_range_succ right_f (n+1),
        rw [left, ih],
        push_cast,
        ring
    }

    -- Tried to figure out the formula from this, without success.
    private def next_f : ∀ n, f (n+1) = 4*n*(n + 1) + 1 :=
    λ n,
    have h1 : ∀ (n:ℚ), (2*(n+1)-1)^2 = 4*n*(n + 1) + 1, from λ n, by ring,
    have f (n+1) = (2*(↑n+1)-1)^2, by refl,
    have f (n+1) = 4*n*(n + 1) + 1, by rwa [h1] at this,
    by exact this

    private def next_f_alt : ∀ n, f (n+1) = 4*n^2 + 4*n + 1 := λ n, by {
        rw next_f n,
        ring
    }

    -- Since for each i we add (4n^2) + (-4n + 1), this is defined as the sum of
    -- the left sides, so 4* what we found in problem 1, and the sum of the
    -- right side (see `right`) above. This can be simplified further.
    private def f' : ℕ → ℚ := λ n, 4*(((↑n:ℚ)*(n+1)*(2*n + 1))/6) + -4 * (n * (n+1))/2 + (n+1)

    private def f'_succ : ∀ n : ℕ, f (n+1) + f' n = f' (n+1) :=
    λ n,
    calc
    f (n+1) + f' n = 4*n^2 + 4*n + 1 + f' n : by rw [next_f_alt]
    ... = 4*n^2 + 4*n + 1 + (4*(((↑n:ℚ)*(n+1)*(2*n + 1))/6) + -4 * (n * (n+1))/2 + (n+1)) : rfl
    ... = (4:rat)*(((n+1)*((n+1)+1)*(2*(n+1) + 1))/6) + -4 * ((n+1) * ((n+1)+1))/2 + ((n+1)+1) : by ring
    ... = f' (n+1) : rfl

    def part_ii : ∀ (n : ℕ), ∑ i in range (n+1), f i = f' n
    | 0 := (
        have h1 : ∑ i in range 1, f i = 1, from rfl,
        have f' 0 = 1, from rfl,
        eq.trans h1 (eq.symm this)
    )
    -- | 1 := (
    --     let n := 1 in
    --     have h1 : ∑ i in range (n+1), f i = 2, from rfl,
    --     have f' n = 2, from rfl,
    --     eq.trans h1 (eq.symm this)
    -- )
    | (n+1) := (
        have ih : ∑ i in range (n+1), f i = f' n, from part_ii n,
        have left : ∑ i in range (n+1+1), f i = f (n+1) + ∑ i in range (n+1), f i, from finset.sum_range_succ f (n+1),
        by rw [left, ih, f'_succ]
    )

end chap_02_problem_02_ii
