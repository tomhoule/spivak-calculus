import order.rel_classes

def natInductionOfIsWellOrder
  [wo : is_well_order ℕ nat.lt]
  {P : ℕ → Prop} :
  P 0 → (∀ a, P a → P (a+1)) → (∀ n, P n) := (
λ hZero hSucc n,
acc.rec_on
  (wo.wf.apply n)
  (λ x (h₁ : ∀ (y : ℕ), y.lt x → acc nat.lt y) (h₂ : (∀ (y : ℕ), y.lt x → P y)),
      or.elim (em $ x = 0)
        (λ xZero, by { rw xZero, exact hZero })
        (λ xSucc, by {
          have xPos : 0 < x := nat.pos_of_ne_zero xSucc,
          have xPredLt : x.pred < x := nat.pred_lt xSucc,
          have xpredPlusOne : x.pred + 1 = x := nat.succ_pred_eq_of_pos xPos,
          let h := hSucc x.pred (h₂ x.pred xPredLt),
          rw xpredPlusOne at h,
          exact h
        }))
)

example : ∀ (n:nat), (n * 2) % 2 = 0 := by {
  refine natInductionOfIsWellOrder _ _,
  {
    rw [nat.zero_mul], exact nat.zero_mod 2
  },
  intros,
  exact (a + 1).mul_mod_left 2
}
