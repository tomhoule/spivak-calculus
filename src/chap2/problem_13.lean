import data.real.basic
import data.real.irrational
import data.int.basic
import ring_theory.int.basic

namespace problem13

open real (sqrt)
open has_dvd (dvd)

-- This is all commented out, because following the intended proof method runs
-- into tough coercion issues with divisibility on reals. I don't have the tools
-- to resolve this at the moment.

-- lemma div3Sq (a : ℝ) : 3 ∣ a^2 → 3 ∣ a := by {
--   intro h,
--   sorry
-- }

-- def intGcdMonoid : gcd_monoid ℤ := by apply_instance

-- example : 1 ∣ 2 := one_dvd 2
-- example (a : ℤ) (p : even a) : 2 ∣ a := even_iff_two_dvd.mp p

-- theorem sqrt3Irrational : irrational (sqrt 3) := by {
--   rintros ⟨⟨num, denom, denomPos, hCoprimes⟩, hEq⟩,
--   replace hEq : _^2 = (sqrt 3)^2 := congr_fun (congr_arg pow hEq) 2,
--   rw [<-rat.cast_pow, real.sqr_sqrt (show 0 ≤ (3:real), by norm_num)] at hEq,

--   rw [pow_two, rat.num_denom', rat.mk_eq_div, div_mul_div, <-pow_two, <-pow_two] at hEq,
--   push_cast at hEq,
--   rw div_eq_iff sorry at hEq,
--   have : 3 ∣ (num:real)^2 := dvd.intro (↑denom ^ 2) (eq.symm hEq),
--   have : 3 ∣ (num:real) := div3Sq (num:real) this,
--   have hLeft : 3 ∣ num.nat_abs := sorry,
--   obtain ⟨k, kEq⟩ : ∃ k, k * 3 = (num:real) := ⟨(num:real)/3, div_mul_cancel (num:real) (show (3:real) ≠ 0, by norm_num)⟩,

--   rw [<-kEq, pow_two, mul_assoc, mul_comm, mul_assoc] at hEq,
--   simp only [mul_eq_mul_left_iff, (show (3:ℝ) ≠ 0, by norm_num), or_false] at hEq,
--   rw [mul_assoc, mul_comm, mul_assoc, <-pow_two] at hEq,

--   have : 3 ∣ (denom:real)^2 := dvd.intro (k ^ 2) hEq,
--   have : (3:ℝ) ∣ (denom:real) := div3Sq denom this,
--   have hRight : 3 ∣ denom := by sorry,

--   delta nat.coprime at hCoprimes,

--   have hDvd : 3 ∣ (num.nat_abs.gcd denom) := nat.dvd_gcd_iff.mpr ⟨hLeft , hRight⟩,
--   have hNotDvd : ¬3 ∣ 1 := nat.prime.not_dvd_one nat.prime_three,
--   have hNotDvd : ¬3 ∣ (num.nat_abs.gcd denom) := by {
--     intro h,
--     rw hCoprimes at h,
--     exact absurd h hNotDvd
--   },

--   exact absurd hDvd hNotDvd
-- }

-- theorem sqrt3Irrational' : ¬∃ (k:ℚ), k^2 = 3 := by {
--   have : ∀ (a:ℕ), ((3:ℕ):ℚ) ∣ ↑a → (3:ℕ) ∣ a := by { intros a h, sorry },

--   rw not_exists,
--   rintros ⟨kNum, kDenom, kDenomPos, kCoprime⟩,
--   rw [pow_two, rat.num_denom', rat.mk_eq_div, div_mul_div, <-pow_two, <-pow_two],
--   rw div_eq_iff sorry,
--   intro hRat,
--   have : 3 ∣ (kNum:ℚ)^2 := dvd.intro (↑↑kDenom ^ 2) (eq.symm hRat),
--   norm_cast at this,  rw [<-int.nat_abs_pow_two] at this, norm_cast at this,
--   have : 3 ∣ kNum.nat_abs^2 := by {
--     obtain ⟨c, hC⟩ : ∃ (c:ℚ), ↑(kNum.nat_abs^2) = c * 3 := exists_eq_mul_left_of_dvd this,
--     sorry
--   },

--   sorry
-- }

theorem sqrt3Irrational : irrational (sqrt ((3:nat):real)) := by {
  exact nat.prime.irrational_sqrt nat.prime_three
}

theorem sqrt5Irrational : irrational (sqrt ((5:nat):real)) := by {
  have : nat.prime 5, by norm_num,
  exact nat.prime.irrational_sqrt this
}

theorem sqrt6Irrational : irrational (sqrt ((6:nat):real)) := by {
  refine @irrational_sqrt_of_multiplicity_odd 6 (by norm_num) 2 nat.prime_two _,
  suffices : (multiplicity ((2:ℕ):ℤ) 6).get (⟨1, by norm_num⟩) = 1, by { rw this, norm_num },
  unfold multiplicity,
  rw [enat.find_get, nat.find_eq_iff],
  split,
  { norm_num },
  intros n nLt1,
  have : n = 0, by {
    induction n with n ih, { refl },
    replace ih := nat.le_of_lt_succ nLt1,
    rw [nat.le_zero_iff] at ih,
    exact ih
  },
  rw [not_not, this],
  norm_num
}

end problem13
