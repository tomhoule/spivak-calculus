import algebra.big_operators.basic
import data.nat.choose.basic
import data.nat.parity

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
    conv_lhs { congr, congr, skip, funext, rw [nat.choose_succ_succ], norm_num, rw [mul_add] },
    rw [finset.sum_add_distrib, add_assoc, nat.choose],

    -- Now reduce the two sums to the predecessor (the left side of the
    -- inductive hypothesis).
    conv { to_lhs, congr, skip, congr, skip, rw [(show 1 = choose (n+1) 0, by refl)] },
    rw [<-finset.sum_range_succ' (λ j, (-1 : ℚ)^j * choose (n+1) j) (n+2)],
    conv_lhs { congr, { congr, skip, funext, rw [pow_succ, mul_assoc] } },
    -- . Eliminate the left term
    rw [finset.sum_hom, ih, mul_zero, zero_add],
    -- . Eliminate the right term
    rw [finset.sum_range_succ, ih], simp only [add_zero, nat.cast_zero, nat.choose_succ_self, mul_zero]
}

-- (iii)

lemma sum_choose_succ_succ { n : ℕ } { s : finset ℕ } : ∑ i in s, choose (n+1) (i+1) = ∑ i in s, choose n i + ∑ i in s, choose n i.succ := by
{ conv_lhs { congr, skip, funext, rw nat.choose_succ_succ }, rw <-finset.sum_add_distrib }

def oddRange : ℕ → finset ℕ := λ n, (range n).filter odd
def evenRange : ℕ → finset ℕ := λ n, (range n).filter even

@[simp] def sumEvenRangeSucc' : ∀ n (f : ℕ → ℕ), ∑ i in evenRange (n+1), f i = (∑ i in oddRange n, f (i+1)) + f 0 := by {
    intros n f,
    unfold evenRange oddRange,
    rw [finset.sum_filter, finset.sum_range_succ', <-finset.sum_filter],
    simp only [nat.even_zero, if_true, add_left_inj],
    have : odd = (λ x, even (x+1)) := funext (λ x, by simp only [nat.even_succ, nat.odd_iff_not_even]),
    conv_rhs { congr, congr, rw this },
    simp only [finset.filter_congr_decidable]
}

@[simp] def sumOddRangeSucc' : ∀ n (f : ℕ → ℕ), ∑ i in oddRange (n+1), f i = (∑ i in evenRange n, f (i+1)) := by {
    intros n f,
    unfold evenRange oddRange,
    rw [finset.sum_filter, finset.sum_range_succ', <-finset.sum_filter],
    simp only [nat.odd_iff_not_even, not_true, nat.even_zero, if_false, add_left_inj, add_zero],
    have : even = (λ x, ¬even (x+1)) := funext (λ x, by simp only [nat.even_succ, not_not]),
    conv_rhs { congr, congr, rw this },
    simp only [finset.filter_congr_decidable]
}

@[simp] def sumOddRangeSuccOFOdd : ∀ n (f : ℕ → ℕ), odd n → ∑ i in oddRange (n+1), f i = f n + (∑ i in oddRange n, f i) := by {
    intros n f nOdd,
    unfold evenRange oddRange,
    rw [finset.sum_filter, finset.sum_range_succ, <-finset.sum_filter],
    simp only [if_true, nat.odd_iff_not_even, add_right_inj, finset.filter_congr_decidable, nOdd],
    have : odd = (λ x, ¬even x) := funext (λ x, by rw nat.odd_iff_not_even),
    conv_lhs { congr, congr, rw <-this },
    simp only [finset.filter_congr_decidable]
}

@[simp] def sumOddRangeSucc : ∀ n (f : ℕ → ℕ), ∑ i in oddRange (n+1), f i = ite (odd n) (f n) 0 + (∑ i in oddRange n, f i) := by {
    intros n f,
    unfold evenRange oddRange,
    rw [finset.sum_filter, finset.sum_range_succ, <-finset.sum_filter],
}

@[simp] def sumEvenRangeSucc : ∀ n (f : ℕ → ℕ), ∑ i in evenRange (n+1), f i = ite (even n) (f n) 0 + (∑ i in evenRange n, f i) := by {
    intros n f,
    unfold evenRange oddRange,
    rw [finset.sum_filter, finset.sum_range_succ, <-finset.sum_filter],
}



def ef : ℕ → ℕ := λ n, ∑ (x : ℕ) in oddRange (n+2), choose (n+1) x
def ef' : ℕ → ℕ := λ n, ∑ (x : ℕ) in evenRange (n+2), choose (n+1) x

example : ef 0 = ef' 0 := rfl
example : ef 1 = ef' 1 := rfl
example : ef 2 = ef' 2 := rfl
example : ef 3 = ef' 3 := rfl
example : ef 4 = ef' 4 := rfl
example : ef 5 = ef' 5 := rfl
example : ef 6 = ef' 6 := rfl

lemma part_iii_helper : ∀ n, ef n = ef' n
| 0 := rfl
| (n+1) := by {
    have ih : ef n = ef' n := part_iii_helper n,
    delta ef ef',
    delta ef ef' at ih,
    rw [sumEvenRangeSucc', sum_choose_succ_succ, sumOddRangeSucc', sum_choose_succ_succ],
    nth_rewrite_rhs 0 ih,
    nth_rewrite_rhs 0 add_assoc,
    rw [add_right_inj, <-sumOddRangeSucc'],
    nth_rewrite_rhs 0 <-sumEvenRangeSucc',

    rw [sumEvenRangeSucc, sumOddRangeSucc, ih, add_left_inj],
    rw [nat.choose_succ_self],
    simp only [if_t_t]
}

theorem part_iii : ∀ (n : ℕ), 0 < n → ∑ l in oddRange (n+1), choose n l = 2^(n-1)
| 0 nPos := false.elim $ absurd (show 0 = 0, from rfl) (ne_of_lt nPos)
| 1 nPos := rfl
| (n+2) (nPos : 0 < n+2) := by {
    have zeroNotOdd : ¬odd 0, by simp only [not_true, nat.odd_iff_not_even, not_false_iff, nat.even_zero],
    have ih : (∑ l in oddRange (n+2), choose (n+1) l) = 2^n := by { apply part_iii (n+1) (nat.succ_pos n) },
    have parityIrrelevance : ∑ i in oddRange (n+2), choose (n+1) i = ∑ i in evenRange (n+2), choose (n+1) i := part_iii_helper n,

    conv_lhs { rw [sumOddRangeSucc', sum_choose_succ_succ] },

    conv_rhs { norm_num, rw [pow_succ, <-ih, two_mul] },

    -- Eliminate the left terms
    rw [parityIrrelevance, add_right_inj],

    -- Eliminate the rest
    conv_lhs { rw [sumEvenRangeSucc, nat.choose_succ_self], congr, simp },
    rw [<-parityIrrelevance, sumOddRangeSucc', zero_add]
 }

--- (iv)
theorem part_iv : ∀ n, ∑ l in evenRange (n+1), choose n l = 2^(n-1)
| 0 := rfl
| 1 := rfl
| (n+2) := by {
    have ih : ∑ l in evenRange (n+2), choose (n+1) l = 2^n := by { apply part_iv (n+1) },
    have parityIrrelevance : ∑ i in oddRange (n+2), choose (n+1) i = ∑ i in evenRange (n+2), choose (n+1) i := part_iii_helper n,

    conv_rhs { norm_num, rw [pow_succ, <-ih, two_mul] },

    rw [sumEvenRangeSucc', sum_choose_succ_succ],

    conv_lhs { congr, congr, skip, rw [sumOddRangeSucc, nat.choose_succ_self], congr, simp },
    nth_rewrite_rhs 0 sumEvenRangeSucc',

    conv_lhs { rw [add_comm, nat.choose_zero_right, zero_add] },
    conv_rhs { rw [add_assoc, add_comm, nat.choose_zero_right, add_assoc] },
    rw [add_right_inj, add_left_inj],

    exact parityIrrelevance
}
