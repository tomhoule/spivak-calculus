import data.real.basic
import data.real.irrational
import data.int.basic

namespace problem13

open real (sqrt)
open has_dvd (dvd)

lemma div3Sq (a : ℝ) : 3 ∣ a^2 → 3 ∣ a := by {
  intro h,
  sorry
}

example : 1 ∣ 2 := one_dvd 2
example (a : ℤ) (p : even a) : 2 ∣ a := even_iff_two_dvd.mp p

theorem sqrt3Irrational : irrational (sqrt 3) := by {
  rintros ⟨⟨num, denom, denomPos, hCoprimes⟩, hEq⟩,
  replace hEq : _^2 = (sqrt 3)^2 := congr_fun (congr_arg pow hEq) 2,
  rw [<-rat.cast_pow, real.sqr_sqrt (show 0 ≤ (3:real), by norm_num)] at hEq,

  rw [pow_two, rat.num_denom', rat.mk_eq_div, div_mul_div, <-pow_two, <-pow_two] at hEq,
  push_cast at hEq,
  rw div_eq_iff sorry at hEq,
  have : 3 ∣ (num:real)^2 := dvd.intro (↑denom ^ 2) (eq.symm hEq),
  have : 3 ∣ (num:real) := div3Sq (num:real) this,
  have : 3 ∣ num := sorry,
  obtain ⟨k, kEq⟩ : ∃ k, k * 3 = (num:real) := ⟨(num:real)/3, div_mul_cancel (num:real) (show (3:real) ≠ 0, by norm_num)⟩,

  rw [<-kEq, pow_two, mul_assoc, mul_comm, mul_assoc] at hEq,
  simp only [mul_eq_mul_left_iff, (show (3:ℝ) ≠ 0, by norm_num), or_false] at hEq,
  rw [mul_assoc, mul_comm, mul_assoc, <-pow_two] at hEq,

  have : 3 ∣ (denom:real)^2 := dvd.intro (k ^ 2) hEq,
  have : 3 ∣ denom := by sorry,


  have : int.gcd num denom ≥ 3, by sorry,

  -- have h1 : sqrt ((num:real)^2) = sqrt (3* denom^2) := congr_arg sqrt hEq,
  -- rw [real.sqrt_mul sorry, real.sqrt_sqr sorry, real.sqrt_sqr sorry] at h1,

  -- rw [pow_two, rat.num_denom', rat.mul_def (ne.symm $ ne_of_lt $ nat.cast_lt.mpr denomPos) (ne.symm $ ne_of_lt $ nat.cast_lt.mpr denomPos)] at hEq,
  sorry
}

end problem13
