import data.real.sqrt

namespace chap2problem15

open real (sqrt)

variables (p q : ℚ)

example (a b c : ℝ) : -(a * b) = -a * b := neg_mul_eq_neg_mul a b
example (a b c : ℝ) : -a - b = -(a+b) := (neg_add' a b).symm

theorem a (x : ℝ) (qNonneg : 0 ≤ (q:real)) : x = p + sqrt q → ∀ (m : ℕ), ∃ (a b : ℚ), x^m = a + b * sqrt q := by {
  intros h m,
  induction m with m ih,
  { rw pow_zero,
    existsi (1:rat), existsi (0:rat),
    norm_cast, rw [zero_mul, add_zero]
  },
  obtain ⟨aM, ⟨bM, ih⟩⟩ := ih,
  rw [pow_succ, ih, h],
  rw [add_mul, mul_add, mul_comm _ (_*_), add_assoc, mul_comm _ (sqrt _), mul_assoc],
  rw [mul_add, <-mul_assoc (sqrt _) (sqrt _) _, <-pow_two, real.sqr_sqrt qNonneg, <-add_assoc ((sqrt _) * _)],
  rw [<-mul_add, add_comm (sqrt _ * _), mul_comm (sqrt _), <-add_assoc],
  norm_cast,
  existsi (p * aM + q * bM),
  existsi (bM * p + aM),
  refl
}

theorem b (x : ℝ) (qNonneg : 0 ≤ (q:real)) : x = p - sqrt q → ∀ (m : ℕ), ∃ (a b : ℚ), x^m = a - b * sqrt q := by {
  intros h m,
  induction m with m ih,
  { rw pow_zero,
    existsi (1:rat), existsi (0:rat),
    norm_cast, rw [zero_mul, sub_zero]
  },
  obtain ⟨aM, ⟨bM, ih⟩⟩ := ih,
  rw [pow_succ, ih, h],

  rw [sub_mul, mul_sub (sqrt _), mul_comm _ (_*_), mul_assoc _ (sqrt _), <-pow_two, real.sqr_sqrt qNonneg],
  simp only [sub_eq_add_neg],

  rw [mul_add, neg_mul_eq_neg_mul, neg_mul_eq_neg_mul, neg_add, neg_mul_eq_neg_mul, <-mul_assoc, neg_mul_eq_neg_mul, neg_neg],
  rw [add_comm (-sqrt _*_) (_*_), <-add_assoc, add_assoc (_*_), add_comm (_*_*_)],
  rw [<-add_assoc, add_assoc _ (_ * -_ * sqrt _)],

  norm_cast,
  existsi (p * aM + bM * q),
  conv { congr, funext, rw add_right_inj },

  rw [<-neg_mul_eq_neg_mul, mul_comm (sqrt _), neg_mul_eq_neg_mul, <-add_mul],
  rw [mul_comm p, <-neg_mul_eq_neg_mul, <-sub_eq_add_neg],
  norm_cast,
  rw <-neg_add',
  norm_cast,
  existsi (bM * p + aM),
  rw neg_mul_eq_neg_mul,
  norm_cast
}

end chap2problem15
