import analysis.special_functions.pow
import data.real.basic
import data.real.irrational
import tactic.rcases

open real (sqrt)

namespace problem12a

variables (a b : ℝ)

def rational (a:ℝ): Prop := ∃ (x y : ℤ), y ≠ 0 ∧ a = x/y

lemma rational_iff (a : ℝ) : (∃ (x y : ℤ), y ≠ 0 ∧ a = x/y) ↔ rational a := by { unfold rational }

def irrational (a:ℝ) : Prop := ¬rational a

lemma rational_add : rational a → rational b → rational (a + b) := by {
  unfold rational,
  rintros ⟨xA, ⟨yA, ⟨yANonzero, hA⟩⟩⟩ ⟨xB, ⟨yB, ⟨yBNonzero, hB⟩⟩⟩,
  existsi (xA * yB + yA * xB),
  existsi (yA * yB),
  split,
  { exact mul_ne_zero yANonzero yBNonzero },
  rw [hA, hB, div_add_div (xA:ℝ) (xB:ℝ) (int.cast_ne_zero.mpr yANonzero) (int.cast_ne_zero.mpr yBNonzero)],
  push_cast
}

lemma rational_sub : rational a → rational b → rational (a - b) := by {
  unfold rational,
  rintros ⟨xA, ⟨yA, ⟨yANonzero, hA⟩⟩⟩ ⟨xB, ⟨yB, ⟨yBNonzero, hB⟩⟩⟩,
  existsi (xA * yB - yA * xB),
  existsi (yA * yB),
  split,
  { exact mul_ne_zero yANonzero yBNonzero },
  rw [hA, hB, div_sub_div (xA:ℝ) (xB:ℝ) (int.cast_ne_zero.mpr yANonzero) (int.cast_ne_zero.mpr yBNonzero)],
  push_cast
}

lemma irrational_add : irrational (a + b) → irrational a ∨ irrational b := by {
  unfold irrational rational,
  contrapose!,
  rintros ⟨h1, h2⟩,
  rw <-rational at *,
  exact rational_add a b h1 h2
}

example (a b c : ℝ) : a + b = c ↔ b = c - a := eq_sub_iff_add_eq'.symm

theorem a1 : rational a → irrational b → irrational (a+b) := by {
  intros h1 h2,
  unfold irrational rational,
  intro hAB,
  have h3 : rational (a+b) := (rational_iff (a+b)).mp hAB,
  obtain ⟨x, ⟨y, ⟨yNonZero, h4⟩⟩⟩ := hAB,
  have h5 : _ := eq_sub_iff_add_eq'.mpr h4,
  rw <-h4 at h5,
  have h6 : rational (a + b - a) := rational_sub (a+b) a h3 h1,
  rw <-h5 at h6,
  exact absurd h6 h2
}

lemma irrationalSqrt2 : irrational (sqrt 2) := by {
  let h := irrational_sqrt_two,
  unfold irrational rational,
  rw irrational_iff_ne_rational at h,
  rw not_exists,
  intro x,
  rw not_exists,
  intro y,
  rw not_and_distrib,
  right,
  exact h x y
}

lemma irrationalNeg : irrational a → irrational (-a) := by {
  unfold irrational rational,
  contrapose!,
  rintro ⟨x, ⟨y, ⟨yNonZero, h1⟩⟩⟩,
  existsi (-x),
  existsi y,
  split,
  exact yNonZero,
  push_cast,
  rw [neg_div, <-eq_neg_iff_eq_neg],
  exact (eq.symm h1)
}

theorem a2 : ¬(∀ a b, irrational a → irrational b → irrational (a+b)) := by {
  rw not_forall,
  existsi (sqrt 2),
  rw not_forall,
  existsi (-(sqrt 2)),
  push_neg,
  split,
  { exact irrationalSqrt2 },
  split,
  { exact irrationalNeg (sqrt 2) irrationalSqrt2 },
  unfold irrational rational,
  rw [add_neg_self, not_not],
  existsi (0:ℤ),
  existsi (1:ℤ),
  split; norm_num
}

end problem12a

namespace problem12b

variables (a b : ℝ)

def rational (a:ℝ): Prop := ∃ (x y : ℤ), a = x/y

lemma rat0 : rational 0 := by
{ existsi (0:int), existsi (1:int), norm_num }

theorem partB0 : ¬(∀ (a b : real), rational a → irrational b → irrational (a*b)) := by {
  rw [not_forall], existsi (0:real), rw not_forall, existsi (sqrt 2), push_neg,
  split,
  { exact rat0 },
  split,
  { exact irrational_sqrt_two},
  rw [zero_mul, irrational_iff_ne_rational],
  push_neg,
  obtain ⟨a, ⟨b, h⟩⟩ := rat0,
  existsi a, existsi b, exact h
}

theorem partB : a ≠ 0 → rational a → irrational b → irrational (a*b) := by {
  intros aNonzero hA hB,
  rw irrational_iff_ne_rational,
  intros a1 b1 hNeg,
  obtain ⟨x1, ⟨y1, h1⟩⟩ := hA,
  rw [mul_comm, <-eq_div_iff aNonzero, div_eq_inv_mul] at hNeg,
  have bRat : rational b := by {
    existsi (y1*a1),
    existsi (x1*b1),
    rw [h1, inv_div, div_mul_div] at hNeg,
    exact_mod_cast hNeg
  },
  have : ¬rational b := by {
    unfold rational,
    push_neg,
    let h := (irrational_iff_ne_rational _).mp hB,
    intros x y, exact h x y
  },
  exact absurd bRat this
}

end problem12b

namespace problem12c

open problem12b (rational)

noncomputable def a : ℝ := 2^(-(1/4:ℝ))

lemma sqrtEqPow : real.sqrt 2 = 2^((1/2:ℝ)) := by rw real.sqrt_eq_rpow

lemma irrationalSq : irrational (a^(2:ℝ)) := by {
  unfold a,
  rw <-real.rpow_mul (zero_le_two),
  norm_num,
  rw [real.rpow_neg (zero_le_two), <-sqrtEqPow],
  suffices : irrational (sqrt 2), from irrational.inv this,
  exact irrational_sqrt_two
}

lemma rationalPow4 : rational (a^(4:real)) := by {
  unfold a,
  rw <-real.rpow_mul (zero_le_two),
  norm_num,
  rw real.rpow_neg_one,
  unfold rational,
  existsi (1:int),
  existsi (2:int),
  simp only [one_div, int.cast_bit0, int.cast_one]
}

end problem12c

namespace problem12d

open problem12b (rational rat0)

theorem D : ∃ (a b : ℝ),
  irrational a ∧ irrational b ∧
  rational (a+b) ∧ rational (a*b)
:= by {
  existsi (sqrt 2),
  existsi (-(sqrt 2)),
  split,
  { exact irrational_sqrt_two},
  split,
  { rw irrational_neg_iff, exact irrational_sqrt_two},
  split,
  { norm_num, exact rat0 },
  norm_num,
  existsi (-2:int),
  existsi (1:int),
  norm_num
}

end problem12d
