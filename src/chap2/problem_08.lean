import logic.basic
import tactic.suggest
import tactic.rcases
import tactic.dec_trivial
import algebra.group.basic

namespace modSolution

variables (n : ℕ)

def even' : Prop := n % 2 = 0
def odd' : Prop := n % 2 = 1

def mod2Decidable : n % 2 = 0 ∨ n % 2 = 1 := nat.mod_two_eq_zero_or_one n

theorem evenIffNotOdd : even' n ↔ ¬odd' n := by {
  delta even' odd',
  split,
  { intros h1 hEqOne,
    have h2 : n % 2 ≠ 0, by { rw hEqOne, exact nat.one_ne_zero },
    exact absurd h1 h2
  },
  intro hNotOdd,
  cases (mod2Decidable n) with h0 h1,
  { exact h0 },
  exact (false.elim $ absurd h1 hNotOdd)
}

end modSolution

-- Solving this again with the definitions from the book
namespace mulSolution

variables (n : ℕ)

def even' : Prop := ∃ k, n = 2 * k
def odd' : Prop := ∃ k, n = 2 * k + 1

theorem evenOrOddOfN (n : ℕ) : even' n ∨ odd' n := by {
  delta even' odd',
  induction n with n ih,
  { left, existsi 0, exact (eq.symm $ nat.mul_zero 2) },
  rcases ih with ⟨k, ih⟩ | ⟨k, ih⟩,
  { right, existsi k, exact congr_arg nat.succ ih },
  left, existsi (k+1), rw [ih, nat.mul_succ]
}

-- It would be easy to do using mods, divisibility, etc. but we restrict
-- ourselves to basic induction here.
lemma oddDecidable : ∀ (x y : ℕ), 2*x ≠ (2*y).succ
| 0 0 := dec_trivial
| (x+1) 0 := dec_trivial
| 0 (y+1) := dec_trivial
| (x+1) (y+1) := by {
  let ih := oddDecidable x y,
  rw [nat.mul_succ, nat.mul_succ, <-nat.succ_add],
  intro h,
  replace h := @nat.add_right_cancel _ (2:nat) _ h,
  exact ih h
}

theorem evenIffNotOdd : even' n ↔ ¬odd' n := by {
  split,
  { rintros ⟨k', hEven⟩,
    rw hEven,
    rintros ⟨x, hOdd⟩,
    exact oddDecidable k' x hOdd
  },
  intro h₂,
  rcases (evenOrOddOfN n) with nEven | nOdd,
  { exact nEven },
  exact absurd nOdd h₂
}

end mulSolution
