import algebra.big_operators.basic
import data.finset.basic
import data.nat.choose.basic
import data.rat.basic
import tactic.linarith
import tactic.norm_num

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
    obtain ⟨ihC, _⟩ : ∃ (c : ℕ), choose n k = ↑c, from part_b n k kLeNPred,
    rcases (eq_or_lt_of_le kLeN) with kEqN | kLtN,
    {
        have : (1:rat) = ↑1, from rfl,
        have : choose (n+1) (n+1) = 1, from choose_self (n+1),
        exact ⟨1, by cc⟩
    },
    have kLeN : (k+1) ≤ n, from nat.lt_succ_iff.mp kLtN,
    obtain ⟨ih2C, _⟩ : ∃ (c : ℕ), choose n (k+1) = ↑c, from part_b n (k+1) kLeN,
    existsi (ihC + ih2C),
    have : choose (n+1) (k+1) = choose n k + choose n (k+1), from part_a n k (show k < n, from nat.succ_le_iff.mp kLeN),
    have : (↑ihC:rat) + ih2C =  ↑(ihC + ih2C), by norm_cast,
    cc
}

namespace part_c

-- The number of sublits of length k in a list of natural numbers.
def len_sublists_count : list ℕ → ℕ → ℕ
| _ 0 := 1 -- the empty list
| [] n := 0
| (hd::tl) (n+1) := (
    -- the sum of the lists including hd
    len_sublists_count tl n +
    -- plus the sum of the lists in tl not including hd
    len_sublists_count tl (n+1)
)


example : len_sublists_count [] 0 = 1 := rfl
example : len_sublists_count [] 1 = 0 := rfl
example : len_sublists_count [1] 0 = 1 := rfl
example : len_sublists_count [1] 1 = 1 := rfl
example : len_sublists_count [1] 2 = 0 := rfl
example : len_sublists_count [1, 2] 1 = 2 := rfl
example : len_sublists_count [1, 2] 2 = 1 := rfl
example : len_sublists_count [1, 2, 3] 2 = 3 := rfl
example : len_sublists_count [3, 2, 1] 3 = 1 := rfl
example : len_sublists_count [1, 2, 3, 4] 3 = 4 := rfl

def len_sublists_count_gt_length : ∀ (l : list ℕ) k, k > l.length → len_sublists_count l k = 0
| [] (k+1) kGt := rfl
| (hd::tl) (k+1) kGt := (
    have (hd::tl).length = tl.length + 1, from list.length_cons hd tl,
    have h1 : k > tl.length, by linarith,
    have ih : len_sublists_count tl k = 0, from len_sublists_count_gt_length tl k h1,
    have ih2 : len_sublists_count tl (k+1) = 0, from len_sublists_count_gt_length tl (k+1) (nat.lt.step h1),
    calc
    len_sublists_count (hd :: tl) (k + 1) = len_sublists_count tl k + len_sublists_count tl (k+1) : rfl
    ... = 0 : by rw [ih, ih2, add_zero]
)

def len_sublists_count_self : ∀ l, len_sublists_count l l.length = 1
| [] := rfl
| (hd::tl) := (
    have ih : len_sublists_count tl tl.length = 1, from len_sublists_count_self tl,
    have h2 : (hd::tl).length = tl.length + 1, from list.length_cons hd tl,
    have h4 : (hd::tl).length > tl.length, by linarith,
    calc
    len_sublists_count (hd :: tl) (hd :: tl).length = len_sublists_count (hd :: tl) (tl.length + 1) : by rw [h2]
    ... = len_sublists_count tl tl.length + len_sublists_count tl (hd::tl).length : rfl
    ... = 1 + len_sublists_count tl (hd::tl).length : by rw [ih]
    ... = 1 : by rw [len_sublists_count_gt_length tl (hd::tl).length h4]
)

def part_c : ∀ (lst : list ℕ) (k : ℕ), k < lst.length → ↑(len_sublists_count lst k) = choose lst.length k
| [] 0 hLen := (
    have left : len_sublists_count [] 0 = 1, from rfl,
    have right : choose list.nil.length 0 = 1, from rfl,
    by rw_mod_cast [left, right]
)
| (hd::tl) 0 HLen := (
    have left : len_sublists_count (hd::tl) 0 = 1, from rfl,
    have right : choose (hd::tl).length 0 = 1, from choose_n_zero (hd :: tl).length,
    by rw_mod_cast [left, right]
)
| (hd::tl) (k+1) hLen := by {
    have : k+1 < (hd::tl).length, by exact hLen,
    have hLen' : k < (hd::tl).length, from buffer.lt_aux_1 hLen,
    have hConsLen : (hd::tl).length = tl.length + 1, from list.length_cons hd tl,
    have hLen'' : k < tl.length, by { rw [hConsLen] at hLen, exact (add_lt_add_iff_right 1).mp hLen},
    have ih : ↑(len_sublists_count (hd::tl) k) = choose (hd::tl).length k, from part_c (hd::tl) k hLen',
    have ih2 : ↑(len_sublists_count tl k) = choose tl.length k, by refine part_c tl k hLen'',
    have : (k+1) ≤ tl.length, from nat.succ_le_iff.mpr hLen'',
    have ih3 : ↑(len_sublists_count tl (k+1)) = choose tl.length (k+1), by {
        rcases (eq_or_lt_of_le this) with kEq | kLt,
        {
            calc
            ↑(len_sublists_count tl (k+1)) = ↑1 : by rw [kEq, len_sublists_count_self]
            ... = choose tl.length (k+1) : by rw_mod_cast [<-choose_self (k+1), kEq]
        },
        exact part_c tl (k+1) kLt
    },
    calc
    (↑(len_sublists_count (hd :: tl) (k + 1)):rat) = ↑(len_sublists_count tl k + len_sublists_count tl (k+1)) : rfl
    ... = ↑(len_sublists_count tl k) + ↑(len_sublists_count tl (k+1)) : by push_cast
    ... = choose tl.length k + ↑(len_sublists_count tl (k+1)) : by rw [ih2]
    ... = choose tl.length k + choose tl.length (k+1) : by rw [ih3]
    ... = choose (tl.length + 1) (k+1) : by rw [part_a (tl.length) k hLen'']
    ... = choose (hd::tl).length (k+1) : by rw [hConsLen]
}

end part_c


section part_d

    open_locale big_operators
    open finset (range)

    def part_d : ∀ (a b : ℚ) (n : ℕ), (a + b)^n = ∑ j in range (n+1), choose n j * a^(n-j) * b^j
    | a b 0 := (
        let n := 0 in
        have left : (a + b)^n = 1, from pow_zero (a + b),
        have right : ∑ j in range (n+1), choose n j * a^(n-j) * b^j = 1, from rfl,
        eq.trans left right
    )
    | a b (n+1) := by {
        have ih : (a + b)^n = ∑ j in range (n+1), choose n j * a^(n-j) * b^j, from part_d a b n,
        have left : (a + b)^(n+1) = (a+b) * (a + b)^n, from pow_succ (a + b) n,
        have right : ∑ j in range (n+1+1), choose (n+1) j * a^((n+1)-j) * b^j = (a+b) * ∑ j in range (n+1), choose n j * a^(n-j) * b^j, from eq.symm (
            have h1 : a * ∑ j in range (n+1), (choose n j * a^(n-j) * b^j) = ∑ j in range (n+1), a * (choose n j * a^(n-j) * b^j), by refine (eq.symm $ finset.sum_hom _ _),
            have h2 : ∀ j, a * (choose n j * a^(n-j) * b^j) = choose n j * a^(n+1-j) * b^j, from (
                λ j,
                have j ≤ n, from sorry,
                have n-j + 1 = (n+1)-j, from nat.sub_add_eq_add_sub this,
                calc
                a * (choose n j * a^(n-j) * b^j) = choose n j * (a * a^(n-j)) * b^j : by simp [mul_assoc, mul_comm a]
                ... = choose n j * a^(n-j + 1) * b^j : by rw [pow_succ]
                ... = choose n j * a^(n+1-j) * b^j : by rw this
            ),
            have choose (n+1) (n+1) * a^0 * b^(n+1) = b^(n+1), by rw [choose_self, pow_zero, one_mul, one_mul],
            calc
            (a+b) * ∑ j in range (n+1), choose n j * a^(n-j) * b^j = a * ∑ j in range (n+1), choose n j * a^(n-j) * b^j + b * ∑ j in range (n+1), choose n j * a^(n-j) * b^j : by rw right_distrib
            ... = ∑ j in range (n+1), a * (choose n j * a^(n-j) * b^j) + b * ∑ j in range (n+1), choose n j * a^(n-j) * b^j: by rw h1
            ... = b^(n+1) + ∑ j in range (n+1), choose (n+1) j * a^((n+1)-j) * b^j : sorry
            ... = (1 * b^(n+1)) + ∑ j in range (n+1), choose (n+1) j * a^((n+1)-j) * b^j : by rw one_mul
            ... = (a^((n+1)-(n+1)) * b^(n+1)) + ∑ j in range (n+1), choose (n+1) j * a^((n+1)-j) * b^j : by rw [<-pow_zero a, nat.sub_self (n+1)]
            ... = (1 * a^((n+1)-(n+1)) * b^(n+1)) + ∑ j in range (n+1), choose (n+1) j * a^((n+1)-j) * b^j : by rw [one_mul (a^((n+1)-(n+1)))]
            ... = (choose (n+1) (n+1) * a^((n+1)-(n+1)) * b^(n+1)) + ∑ j in range (n+1), choose (n+1) j * a^((n+1)-j) * b^j : by rw [choose_self (n+1)]
            ... = ∑ j in range (n+1+1), choose (n+1) j * a^((n+1)-j) * b^j : by refine (eq.symm $ finset.sum_range_succ _ _)
        ),
        rw [left, ih, <-right]
    }

end part_d

end problem_03
