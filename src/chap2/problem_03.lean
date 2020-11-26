import data.nat.choose.basic
import data.rat.basic
import tactic.norm_num
import tactic.linarith

namespace problem_03

variables ( n k : ℕ )

def factorial : ℕ → ℕ
| 0 := 1
| (n+1) := (n+1) * factorial n

example : factorial 0 = 1 := rfl
example : factorial 1 = 1 := rfl
example : factorial 2 = 2 := rfl
example : factorial 3 = 6 := rfl
example : factorial 4 = 24 := rfl

def factorial_pos : ∀ n, 0 < factorial n
| 0 := (
    calc
    factorial 0 = 1 : rfl
    ... > 0 : by norm_num
)
| (n+1) := (
    have ih : factorial n > 0, from factorial_pos n,
    have 0 < n+1, from nat.succ_pos n,
    have 0 < (n+1) * factorial n, from mul_pos this ih,
    this
)

def choose : ℕ → ℕ → ℚ :=
λ n k, factorial n / (factorial k * factorial (n-k))

example : choose 0 0 = 1 := rfl
example : ∀ n, choose n 0 = 1 := (
    λ n,
    have factorial n ≠ 0, from ne_of_gt (factorial_pos n),
    calc
    choose n 0 = factorial n / (factorial 0 * factorial (n-0)) : rfl
    ... = factorial n / (1 * factorial n) : rfl
    ... = factorial n / factorial n : by rw [one_mul]
    ... = 1 : div_self (by exact_mod_cast this)
)

def choose_self : ∀ n, choose n n = 1 := λ n,
have factorial n ≠ 0, from ne_of_gt (factorial_pos n),
calc
    choose n n = factorial n / (factorial n * factorial (n-n)) : rfl
    ... = factorial n / (factorial n * factorial 0) : by norm_num
    ... = factorial n / (factorial n * 1) : rfl
    ... = factorial n / factorial n : by rw [mul_one]
    ... = 1 : div_self (by exact_mod_cast this)

example : ∀ (a b c : ℚ), 0 ≠ a → 0 ≠ b → 0 ≠ c → (a * b) / (a * c) = b/c := by {
    intros a b c aNonzero bNonzero cNonzero,
    exact mul_div_mul_left b c (ne.symm aNonzero)
}

def part_a : ∀ n k, k < n → choose (n+1) (k+1) = choose n k + choose n (k+1) :=
begin
    intros n k kLtN,
    have kLtNRat : (k:rat) < n, by exact_mod_cast kLtN,
    have kSuccNonzero : (k+1) ≠ 0,from  nat.succ_ne_zero k,
    have kSuccNonzeroRat : ((k:rat)+1) ≠ 0, from nat.cast_add_one_ne_zero k,
    have kSuccLeNSucc : (k+1) ≤ (n+1), from add_le_add_right (le_of_lt kLtN) 1,
    have : n+1 = (n+1)-(k+1) + (k+1), from (eq.symm $ nat.sub_add_cancel kSuccLeNSucc),
    have h2 : (n+1) * factorial n = ((n+1)-(k+1) + (k+1)) * factorial n, by rw [<-this],
    have h3 : (((↑k:rat)+1) * factorial n) / (factorial (k+1) * factorial ((n+1)-(k+1))) = choose n k, from (
        calc
        (((k:rat)+1) * factorial n) / (factorial (k+1) * factorial ((n+1)-(k+1))) = ((k+1) * factorial n) / (↑((k+1) * factorial k) * factorial ((n+1)-(k+1))) : rfl
        ... = ((k+1) * factorial n) / ((k+1) * factorial k * factorial ((n+1)-(k+1))) : by norm_cast
        ... = factorial n / (factorial k * factorial ((n+1)-(k+1))) : by rw [mul_assoc, mul_div_mul_left _ _ kSuccNonzeroRat]
        ... = factorial n / (factorial k * factorial (n-k)) : by rw [nat.succ_sub_succ n k]
        ... = choose n k : rfl
    ),
    have h4 : ((((n:rat)+1)-(k+1)) * factorial n) / (factorial (k+1) * factorial ((n+1)-(k+1))) = choose n (k+1), from (
        have nat.succ (n - (k+1)) = (n+1) - (k+1), from (eq.symm $ nat.succ_sub (show n >= (k+1), from nat.succ_le_iff.mpr kLtN)),
        have factorial ((n+1) - (k+1)) = ((n+1) - (k+1)) * factorial (n-(k+1)), from eq.symm (
            calc
            ((n+1) - (k+1)) * factorial (n-(k+1)) = nat.succ (n-(k+1)) * factorial (n-(k+1)) : by rw [<-this]
            ... = factorial (nat.succ (n-(k+1))) : rfl
            ... = factorial ((n+1) - (k+1)) : by rw this
        ),
        calc
        ((((↑n:rat)+1)-(k+1)) * factorial n) / (factorial (k+1) * factorial ((n+1)-(k+1))) = ((((↑n:rat)+1)-(k+1)) * factorial n) / (factorial (k+1) * ↑(((n+1) - (k+1)) * factorial (n-(k+1)))) : by rw this
        ... = (((n+1)-(k+1)) * factorial n) / (factorial (k+1) * (((n+1) - (k+1)) * factorial (n-(k+1)))) : by norm_cast
        ... = (((n+1)-(k+1)) * factorial n) / (((n+1) - (k+1)) * factorial (k+1) * factorial (n-(k+1))) : by rw [<-mul_assoc, mul_comm _ ((((n:rat)+1) - (k+1)))]
        ... = ((n-k) * factorial n) / ((n-k) * factorial (k+1) * factorial (n-(k+1))) : by norm_num
        ... = factorial n / (factorial (k+1) * factorial (n-(k+1))) : by rw [mul_assoc, mul_div_mul_left _ _ (ne_of_gt $ sub_pos_of_lt kLtNRat)]
        ... = choose n (k+1) : rfl
    ),
    calc
    choose (n+1) (k+1) = ↑((n+1) * factorial n) / (factorial (k+1) * factorial ((n+1)-(k+1))) : rfl
    ... = ↑(((n+1)-(k+1) + (k+1)) * factorial n) / (factorial (k+1) * factorial ((n+1)-(k+1))) : by rw [h2]
    ... = (((n+1)-(k+1) + (k+1)) * factorial n) / (factorial (k+1) * factorial ((n+1)-(k+1))) : by norm_cast
    ... = (((n+1)-(k+1)) * factorial n) / _ + ((k+1) * factorial n) / (factorial (k+1) * factorial ((n+1)-(k+1))) : by rw [right_distrib, div_add_div_same]
    ... = choose n (k+1) + choose n k : by rw [h3, h4]
    ... = choose n k + choose n (k+1) : by rw add_comm
end

def choose_n_zero : ∀ n, choose n 0 = 1 :=
λ n,
have factorial n ≠ 0, from ne_of_gt (factorial_pos n),
have (↑(factorial n):rat) ≠ 0, by exact_mod_cast this,
calc
    choose n 0 = factorial n / (factorial 0 * factorial (n-0)) : rfl
    ... = factorial n / (1 * factorial n) : rfl
    ... = 1 : by rw [one_mul, div_self this]


def part_b : ∀ (n k : ℕ), k ≤ n → ∃ (c : ℕ), choose n k = ↑c
| 0 0 kLeN := ⟨1, rfl⟩
| n 0 kLeN := (
    have (1:rat) = ↑1, from rfl,
    have choose n 0 = 1, from choose_n_zero n,
    ⟨1, by cc⟩
)
| 0 k kLeN := (
    have (1:rat) = ↑1, from rfl,
    have t1 : k = 0, from le_zero_iff_eq.mp kLeN,
    have choose 0 0 = 1, by refl,
    have choose 0 k = choose 0 0, by rw [t1],
    ⟨1, by cc⟩
)
| (n+1) (k+1) kLeN := by {
    have kLeNPred : k ≤ n, from nat.succ_le_succ_iff.mp kLeN,
    have ih : ∃ (c : ℕ), choose n k = ↑c, from part_b n k kLeNPred,
    rcases (eq_or_lt_of_le kLeN) with kEqN | kLtN,
    {
        have : (1:rat) = ↑1, from rfl,
        have : choose (n+1) (n+1) = 1, from choose_self (n+1),
        exact ⟨1, by cc⟩
    },
    have kLeN : (k+1) ≤ n, from nat.lt_succ_iff.mp kLtN,
    have ih2 : ∃ (c : ℕ), choose n (k+1) = ↑c, from part_b n (k+1) kLeN,
    rcases ⟨ih, ih2⟩ with ⟨⟨ihC, _⟩, ⟨ih2C, _⟩⟩,
    existsi (ihC + ih2C),
    have : choose (n+1) (k+1) = choose n k + choose n (k+1), from part_a n k (show k < n, from nat.succ_le_iff.mp kLeN),
    have : (↑ihC:rat) + ih2C =  ↑(ihC + ih2C), by norm_cast,
    cc
}

end problem_03
