import data.real.basic
import tactic.rcases

namespace problem12a

variables (a b : ℝ)

def rational (a:ℝ): Prop := ∃ (x y : ℚ), y ≠ 0 ∧ a = x/y

lemma rational_iff (a : ℝ) : (∃ (x y : ℚ), y ≠ 0 ∧ a = x/y) ↔ rational a := by { unfold rational }

def irrational (a:ℝ) : Prop := ¬rational a

lemma rational_add : rational a → rational b → rational (a + b) := by {
  unfold rational,
  rintros ⟨xA, ⟨yA, ⟨yANonzero, hA⟩⟩⟩ ⟨xB, ⟨yB, ⟨yBNonzero, hB⟩⟩⟩,
  existsi (xA * yB + yA * xB),
  existsi (yA * yB),
  split,
  { exact mul_ne_zero yANonzero yBNonzero },
  rw [hA, hB, div_add_div (xA:ℝ) (xB:ℝ) (rat.cast_ne_zero.mpr yANonzero) (rat.cast_ne_zero.mpr yBNonzero)],
  push_cast
}

lemma rational_sub : rational a → rational b → rational (a - b) := by {
  unfold rational,
  rintros ⟨xA, ⟨yA, ⟨yANonzero, hA⟩⟩⟩ ⟨xB, ⟨yB, ⟨yBNonzero, hB⟩⟩⟩,
  existsi (xA * yB - yA * xB),
  existsi (yA * yB),
  split,
  { exact mul_ne_zero yANonzero yBNonzero },
  rw [hA, hB, div_sub_div (xA:ℝ) (xB:ℝ) (rat.cast_ne_zero.mpr yANonzero) (rat.cast_ne_zero.mpr yBNonzero)],
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


end problem12a
