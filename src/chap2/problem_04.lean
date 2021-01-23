import algebra.big_operators.basic
import chap2.problem_03.binomial_theorem_golf
import data.mv_polynomial.basic
import data.polynomial.basic
import data.polynomial.eval
import data.finsupp.pointwise
import data.finset.nat_antidiagonal

open_locale big_operators
open finset (range)
open nat (choose)
open polynomial (eval coeff monomial)

namespace partA


private lemma vandermonde_identity_aux (m n : ℕ) : choose_polynomial n * choose_polynomial m = choose_polynomial (n+m) := by {
  rw [<-binomial_theorem' n, <-binomial_theorem' m],
  rw [<-pow_add, binomial_theorem']
}

private lemma antidiagonal_sum_rewrite (n : ℕ) (f : ℕ → ℕ → ℕ) : ∑ k in finset.nat.antidiagonal n, f k.fst k.snd = ∑ k in range (n+1), f k (n-k) := by {
  apply @finset.sum_bij _ _ _ _ _ _ (λ (x:ℕ × ℕ), f x.fst x.snd) (λ x, f x (n-x)) (λ (a:ℕ ×ℕ) ha, a.fst),
  { intros,
    simp only [finset.mem_range],
    rw [finset.nat.mem_antidiagonal] at ha,
    replace ha := (nat.lt_succ_of_le $ le_of_eq ha),
    exact buffer.lt_aux_1 ha
  },
  { intros,
    simp only,
    rw [finset.nat.mem_antidiagonal] at ha,
    have : n - a.fst = a.snd := norm_num.sub_nat_pos n a.fst a.snd ha,
    rw this
  },
  { intros _ _ _ _ h₁,
    simp only at h₁,
    rw [prod.ext_iff],
    split, exact h₁,
    rw [finset.nat.mem_antidiagonal] at ha₁ ha₂,
    replace ha₁ := nat.sub_eq_of_eq_add (eq.symm ha₁),
    replace ha₂ := nat.sub_eq_of_eq_add (eq.symm ha₂),
    rw h₁ at ha₁,
    rw [<-ha₁, <-ha₂]
  },
  intros,
  existsi (b, n - b),
  rw finset.mem_range at H,
  have : (b, n - b) ∈ finset.nat.antidiagonal n, by {
    rw finset.nat.mem_antidiagonal,
    have h2 : b ≤ n := nat.lt_succ_iff.mp H,
    simp only, exact nat.add_sub_of_le h2
  },
  existsi this,
  simp only
}


theorem vandermonde_identity (m n l : ℕ) : ∑ k in range (l+1), (choose n k * choose m (l-k)) = choose (n+m) l := by {
  rw <-antidiagonal_sum_rewrite l (λ a b, choose n a * choose m b),
  let h := (polynomial.ext_iff.mp $ vandermonde_identity_aux m n) l,
  rw [polynomial.coeff_mul _ _ l] at h,
  simp only [choose_polynomial.coeff_eq] at h,
  exact h
}

end partA

namespace partB

theorem b : ∀ n, (∑ k in range (n+1), (choose n k)^2) = choose (2*n) n := by {
  intro n,
  let h := partA.vandermonde_identity n n n,
  rw <-two_mul at h,
  rw <-h,
  conv_rhs {
    apply_congr, skip,
    rw nat.choose_symm (nat.le_of_lt_succ $ finset.mem_range.mp H),
    rw <-pow_two,
  },
}

end partB
