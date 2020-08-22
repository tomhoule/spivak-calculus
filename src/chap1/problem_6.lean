import algebra.ordered_field
import algebra.group_with_zero_power
import tactic.basic
import tactic.suggest
import data.int.parity

variables {α : Type } [discrete_linear_ordered_field α]
variables {a b c d : α} {n : ℕ}

-- (a)
theorem pow_lt : ∀ (n : ℕ), 0 < n → 0 ≤ a → a < b → a^n < b^n
| 0 npos _ _ := false.elim $ lt_irrefl 0 npos
| 1 _ anonneg altb := by rwa [←pow_one a, ←pow_one b] at altb
| (n+2) npos anonneg altb :=
    have bpos : 0 < b, from gt_of_gt_of_ge altb anonneg,
    have ih : a^(n+1) < b^(n+1), from pow_lt (n+1) (by simp only [nat.succ_pos']) anonneg altb,
    begin
        have hb : 0 < b^(n+2), by exact pow_pos bpos (n + 2),
        cases (lt_or_eq_of_le anonneg),
        case or.inr:
        {
            have h1 : 0^(n+2) = a^(n+2), by rw [h],
            have : (0 : α)^(n+2) = (0 : α), from zero_pow (by simp only [nat.succ_pos']),
            have ha : a^(n+2) = 0, from eq.trans (eq.symm h1) this,
            show a^(n+2) < b^(n+2), by rwa [←ha] at hb
        },
        have ha : 0 < a^(n+1), by exact pow_pos h (n + 1),
        have : a * a^(n+1) < b * b^(n+1), from mul_lt_mul altb (le_of_lt ih) ha (le_of_lt bpos),
        by assumption
    end


theorem neg_pow_odd : ∀ (n : ℕ), a < 0 → n % 2 = 1 → a^n < 0 :=
assume n aneg nodd,
have (-1 : α)^n = -1^(n%2), from neg_one_pow_eq_pow_mod_two,
have oddpow : (-1 : α)^n = -1, by rwa [nodd, pow_one] at this,
have a^n = (1 * a)^n, by rw [one_mul],
have a^n = (-1 * -a)^n, by rwa [←neg_mul_neg] at this,
have h1 : a^n = -1 * (-a)^n, by rwa [mul_pow, oddpow] at this,
have h2 : 0 < -a, from neg_pos.mpr aneg,
have h3 : 0 < (-a)^n, from pow_pos h2 n,
have h4 : -1 * (-a)^n < 0, by simpa,
show a^n < 0, by rwa [←h1] at h4

-- (b)
theorem odd_pow_lt : ∀ (n : ℕ), a < b → n % 2 = 1 → a^n < b^n
| 0 altb nodd := by contradiction
| 1 altb nodd :=
    have h1 : a^1 = a, from pow_one a,
    have h2 : b^1 = b, from pow_one b,
    by rwa [h1, h2]
| (n+2) altb nodd :=
    have nsuccpos : 0 < n+2, from nat.succ_pos (n+1),
    have ih : a^n < b^n, from odd_pow_lt n altb nodd,
    have positiveCase: 0 ≤ a → 0 < b → a^(n+2) < b^(n+2), from λ apos bpos, pow_lt_pow_of_lt_left altb apos nsuccpos,
    or.elim3 (decidable.lt_trichotomy 0 a)
        (λ apos,
            or.elim3 (decidable.lt_trichotomy 0 b)
                -- everything is positive, proving this is trivial
                (λ bpos, positiveCase (le_of_lt apos) bpos)

                -- positive less than 0 (or negative) -> contradiction
                (λ bzero,
                    have a < 0, by rwa [←bzero] at altb,
                    have ¬(0 < a), from not_lt_of_lt this,
                    by contradiction
                )
                (λ bneg,
                    have a < 0, from gt.trans bneg altb,
                    have ¬(0 < a), from not_lt_of_lt this,
                    by contradiction
                )
        )
        (λ azero,
            or.elim3 (decidable.lt_trichotomy 0 b)
                (λ bpos, positiveCase (le_of_eq azero) bpos)
                (λ bzero,
                    have a = b, by rwa [←azero, ←bzero],
                    have a < a, by rwa [←this] at altb,
                    false.elim $ lt_irrefl a this
                )
                (λ bneg,
                    have b < a, by rwa [azero] at bneg,
                    have ¬(a < b), from not_lt_of_lt this,
                    by contradiction
                )
        )
        (λ aneg,
            have h1 : a^(n+2) < 0, from neg_pow_odd (n + 2) aneg nodd,
            or.elim3 (decidable.lt_trichotomy 0 b)
                (λ bpos,
                    have h2 : 0 < b^(n+2), from pow_pos bpos (n + 2),
                    lt_trans h1 h2
                )
                (λ bzero,
                    have h2 : b^(n+2) = 0, by rw [←bzero, zero_pow nsuccpos],
                    by rwa [←h2] at h1
                )
                (λ bneg,
                    have minusbpos : 0 < -b, from neg_pos.mpr bneg,
                    have minusapos : 0 < -a, from neg_pos.mpr aneg,
                    have minusasqpos : 0 < -a * -a, from mul_pos minusapos minusapos,
                    have altbopps : -b < -a, from neg_lt_neg altb,
                    have bnneg : b^n < 0, from neg_pow_odd n bneg nodd,
                    have h1 : -b * -b < -a * -a, from mul_lt_mul altbopps (le_of_lt altbopps) minusbpos (le_of_lt minusapos),
                    have h2 : -(b^n) < -(a^n), from neg_lt_neg ih,
                    have (-b) * (-b) * -(b^n) < (-a) * (-a) * -(a^n), from mul_lt_mul h1 (le_of_lt h2) (neg_pos.mpr bnneg) (le_of_lt minusasqpos),
                    have -(b * -b * -(b^n)) < -(a * -a * -(a^n)), by simpa only [neg_mul_eq_neg_mul_symm],
                    have a * -a * -(a^n) < b * -b * -(b^n), from neg_lt_neg_iff.mp this,
                    have a * (a * (a^n)) < b * (b * (b^n)), by rwa [mul_assoc, mul_assoc, neg_mul_neg, neg_mul_neg] at this,
                    by assumption
                )
        )

-- (c)
theorem pow_odd_eq : ∀ (n : ℕ), n % 2 = 1 → a^n = b^n → a = b
| 0 zeroodd h := by contradiction
| 1 oneodd h :=
    have h1 : a^1 = a, by rw pow_one,
    have h2 : b^1 = b, by rw pow_one,
    by rwa [←h1, ←h2]
| n nodd h := begin
    -- have ih : a^n = b^n → a = b, from pow_odd_eq n nodd,

    -- neg_one_pow_eq_pow_mod_two

    have ih : ((a^(n-2) = b^(n-2)) → (a = b)), from sorry,
    have h : a^(n) = b^(n), from h,
    -- have ih : a^(n-2) = b^(n-2) → a = b, from pow_odd_eq (n-2),
    have nodd' : n % 2 = 1, from nodd,
    sorry
end


-- | (n+3) nodd h :=
--     have h : a^(n+3) = b^(n+3), from h,
--     have nplusonepos : 0 < (n+1), by exact n.succ_pos,
--     have nplusthreepos : 0 < (n+3), by exact (n + 2).succ_pos,
--     have npredpos : 0 < (n+1), by exact nat.succ_pos n,
--     have ih : a^(n+1) = b^(n+1) → a = b, from (λ h2, pow_odd_eq (n+1) nodd h2),
--     or.elim3 (decidable.lt_trichotomy a 0)
--         (λ aneg,
--             or.elim3 (decidable.lt_trichotomy b 0)
--                 (λ bneg, sorry)
--                 (λ bzero, sorry)
--                 (λ bpos, sorry)
--         )
--         (λ azero,
--             or.elim (decidable.em (b = 0))
--                 (λ bzero,
--                     have apowzero : a^(n+1) = 0, by rwa [azero, zero_pow nplusonepos],
--                     have bpowzero : b^(n+1) = 0, by rwa [bzero, zero_pow nplusonepos],
--                     have anbn : a^(n+1) = b^(n+1), by rwa [apowzero, bpowzero],
--                     ih anbn
--                 )
--                 (λ bnonzero,
--                     have apowzero : a^(n+3) = 0, by rwa [azero, zero_pow nplusthreepos],
--                     have b^(n+3) ≠ 0, by exact pow_ne_zero (n+3) bnonzero,
--                     have a^(n+3) ≠ b^(n+3), from ne_of_eq_of_ne apowzero (ne.symm this),
--                     by contradiction
--                 )
--         )
--         (λ apos,
--             or.elim3 (decidable.lt_trichotomy b 0)
--                 (λ bneg, sorry)
--                 (λ bzero, sorry)
--                 (λ bpos, sorry)
--         )
