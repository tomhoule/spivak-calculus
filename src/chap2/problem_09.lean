import data.nat.basic
import tactic.suggest

theorem problem09 (s : set ℕ) (n₀ : ℕ) : n₀ ∈ s → (∀ (k:ℕ), k ∈ s → (k.succ ∈ s)) → {n:nat | n >= n₀} ⊆ s := by {
  intros hMin hKMem,
  unfold has_subset.subset set.has_subset set.subset,
  intros a hA,
  unfold has_mem.mem set.mem at *,
  refine nat.le_induction hMin (λ x _ hX, hKMem x hX) a hA,
}
