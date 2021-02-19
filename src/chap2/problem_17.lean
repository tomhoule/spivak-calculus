import tactic.induction
import data.real.sqrt
import data.nat.prime
import data.finset.basic

namespace chap2problem17

theorem a : ∀ (n : ℕ), n = 0 ∨ nat.prime n ∨ ∃ (m : multiset ℕ), n = (m.filter nat.prime).fold has_mul.mul 1 := by {
  intro n,
  induction' n,
  { left, refl },
  right,
  rcases ih with nZero | nPrime | nNotPrime,
  { right,
    have : n.succ = 1 := congr_arg nat.succ nZero,
    rw this,
    exact ⟨multiset.zero, rfl⟩
  },
  { -- n is two or odd because it is prime
    -- if it is two, then n+1 = 3, it's prime
    -- if it is odd, n+1 is even, so not prime
    sorry },
  rcases (em $ ∃ a b, a < n.succ ∧ b < n.succ ∧ a ≠ 1 ∧ b ≠ 1 ∧  n.succ = a * b) with hasFactors | hasNoFactors,
  { right,
    obtain ⟨a, ⟨b, _⟩⟩ := hasFactors,
    -- a is prime or has a multiset
    -- b is prime or has a multiset,
    -- note: we need complete induction there
    -- existsi the primes + the multisets
    sorry -- aggregate the two multisets
  },
  left,
  unfold nat.prime,
  split,
  { sorry },
  intros m hM,
  rcases (em $ m = 1) with mOne | mNotOne,
  { left, exact mOne },
  rcases (em $ m = n.succ) with mN | mNotN,
  { right, exact mN },
  refine absurd _ hasNoFactors,
  have : m ≤ n.succ := nat.le_of_dvd (nat.succ_pos n) hM,
  have : m < n.succ := by { replace this := eq_or_lt_of_le this, rcases this, { exact absurd this mNotN }, exact this },
  existsi m,
  obtain ⟨b, hB⟩ : ∃ b, n.succ = b * m := exists_eq_mul_left_of_dvd hM,
  existsi b,
  split,
  { exact this },
  split,
  { sorry },
  split,
  { exact mNotOne },
  split,
  { sorry },
  rw mul_comm,
  exact hB
}

end chap2problem17
