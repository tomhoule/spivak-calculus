import algebra.big_operators.basic
import data.nat.choose.basic
import chap2.problem_03.binomial_theorem_golf

open_locale big_operators
open finset (range)
open nat (choose)

namespace partA

def f : ℕ → ℕ → ℕ → ℕ → ℕ :=
λ l m n k, choose n k * choose m (l - k)

lemma fZero : ∀ m n, f 0 m n 0 = 1 := by { intros, unfold f, norm_num }

lemma hint ( x n : ℕ ) : (1 + x)^n = ∑ k in range (n+1), n.choose k * x^k := by {
  rw [binomial_theorem],
  conv_lhs { congr, congr, skip, funext, rw [one_pow, mul_one] }
}

lemma hint' ( x m n : ℕ ) : (1 + x)^n * (1 + x)^m = ∑ k in range (n+m+1), (choose (n+m) k * x^k) := by {
  rw [<-pow_add, binomial_theorem],
  conv_lhs { congr, skip, funext, rw [one_pow, mul_one] },
}

lemma hint'' ( x m n : ℕ ) :
  (∑ k in range (n+1), (n.choose k * x^k)) * (∑ k in range (m+1), (m.choose k * x^k)) =
  ∑ k in range (n+m+1), choose (n+m) k * x^k
:= by { intros, rw [<-hint x m, <-hint x n], exact hint' x m n }

lemma sum_hom_mul ( a n : ℕ ) ( f : ℕ → ℕ ) :
  a * ∑ i in range n, f i = ∑ i in range n, a * f i := by
{ intros, rw [finset.sum_hom (range n) (λ x, a * x)] }

lemma formal_power_series_mul ( m n x : ℕ ) ( a b : ℕ → ℕ ):
  (∑ i in range (m+1), (a i * x^i)) * (∑ j in range (n+1), (b j * x^j)) =
  ∑ l in range (m+n+1), (∑ k in range (l+1), (f l m n k)) * x^l
:= by {
  intros,
  rw sum_hom_mul (∑ i in range (m+1), _),
  conv_lhs { congr, skip, funext, rw [mul_comm, sum_hom_mul] },
  conv in (_ * _) { rw [mul_assoc, mul_comm (_^_), mul_assoc, <-mul_assoc (b _), <-pow_add], },
  sorry
 }

theorem part_a : ∀ (l m n : ℕ), (∑ k in range (l+1), f l m n k) = choose (n+m) l := by {
  intros,
  let h := hint' l m n,
  rw [hint l, hint l, formal_power_series_mul] at h,
  -- rw [
  --   finset.sum_congr
  --     (show range (m+n+1) = range (m+n+1), from rfl)
  --     (λ x xInRange, _)
  -- ],
  -- finset.sum_congr
  -- mul_left_inj
  sorry
}
-- | 0 m n := by { rw [finset.sum_range_one, fZero, nat.choose_zero_right] }
-- | (l+1) m n := by {
--   let ih := part_a l m n,

--   -- proove that left * x^k = right * x^k (and x^k ≠ 0)
--   sorry
-- }

end partA
