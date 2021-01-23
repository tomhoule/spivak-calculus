import data.polynomial.basic
import data.mv_polynomial.basic
import data.finset.basic
import data.finsupp.basic

-- order -> coefficient
-- represents 3*x+5
def f : ℕ → ℤ := λ n,
(match n with
| 0 := 5
| 1 := 3
| _ := 0
end)

def f' : polynomial ℤ := {
  to_fun := f,
  support := {0, 1},
  mem_support_to_fun := by {
    intros s, rw [finset.mem_insert, finset.mem_singleton], split,
    { intro h, unfold f, delta f._match_1,
      cases h; simp [h]; delta id_rhs; norm_num
    },
    intro h1,
    by_contradiction,
    have : f s = 0, by {
      unfold f, delta f._match_1,
      obtain ⟨hNotZero, hNotOne⟩ := not_or_distrib.mp h,
      simp [hNotZero, hNotOne]
    },
    exact absurd this h1
  },
}

inductive Var
| x

instance : unique Var := {
  default := Var.x,
  uniq := by { intro v, unfold default, cases v, refl }
}

noncomputable instance : decidable_eq Var := assume a b, classical.dec (a = b)

noncomputable def x0 : Var →₀ ℕ := finsupp.single Var.x 0

lemma x0Unique : ∀ (s : Var →₀ ℕ), s (default Var) = x0 (default Var) → s = x0 := by { intros s, exact finsupp.unique_ext}

noncomputable def x1 : Var →₀ ℕ := finsupp.single Var.x 1

-- order -> coefficient
-- represents 3*x+5
noncomputable def f2 : (Var →₀ ℕ) → ℤ := λ s,
if s = x0 then 5
else if s = x1 then 3
else 0

lemma x0NeX1 : x1 ≠ x0 := by { intro h, rw finsupp.ext_iff at h, apply absurd h, rw not_forall, existsi Var.x, unfold x0 x1, simp only [finsupp.coe_zero, finsupp.single_eq_same, not_false_iff, one_ne_zero] }

noncomputable def f'' : mv_polynomial Var ℤ := {
  to_fun := f2,
  support := {x0, x1},
  mem_support_to_fun := by {
    intros s, rw [finset.mem_insert, finset.mem_singleton], split,
    { intro h, unfold f2, induction h; { simp [h, x0NeX1], norm_num } },
    intro h1,
    by_contradiction,
    rcases (not_or_distrib.mp h) with ⟨notX0, notX1⟩,
    have : f2 s = 0, by {
      unfold f2,
      simp [notX0, notX1],
    },
    contradiction
  },
}

#check f''
