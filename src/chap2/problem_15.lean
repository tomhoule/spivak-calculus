import data.real.sqrt

namespace chap2problem15

open real (sqrt)

variables (p q : ℚ)

theorem a (x : ℝ) : x = p + sqrt q → ∀ (m : ℕ), ∃ (a b : ℚ), x^m = a + b * sqrt q := by {
  intros h m,
  induction m with m ih,
  { rw pow_zero,
    existsi (1:rat), existsi (0:rat),
    norm_cast, rw [zero_mul, add_zero]
  },
  rcases (em $ q = 0) with qZero | qNonZero,
  { sorry },
  obtain ⟨aM, ⟨bM, ih⟩⟩ := ih,
  rw [pow_succ, ih, h],
  rw [add_mul, mul_add, mul_comm _ (_*_), add_assoc, mul_comm _ (sqrt _), mul_assoc],
  rw [mul_add, <-mul_assoc (sqrt _) (sqrt _) _, <-pow_two, real.sqr_sqrt sorry, <-add_assoc ((sqrt _) * _)],
  rw [<-mul_add, add_comm (sqrt _ * _), mul_comm (sqrt _), <-add_assoc],
  norm_cast,
  existsi (p * aM + q * bM),
  existsi (bM * p + aM),
  refl
}

theorem b (x : ℝ) : x = p - sqrt q → ∀ (m : ℕ), ∃ (a b : ℚ), x^m = a - b * sqrt q := by {
  intros h m,
  induction m with m ih,
  { rw pow_zero,
    existsi (1:rat), existsi (0:rat),
    norm_cast, rw [zero_mul, sub_zero]
  },
  obtain ⟨aM, ⟨bM, ih⟩⟩ := ih,
  rw [pow_succ, ih],
  sorry
}

end chap2problem15
