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
have (-1 : α)^n = (-1)^(n%2), from neg_one_pow_eq_pow_mod_two,
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
theorem pow_odd_eq : ∀ (n : ℕ), n % 2 = 1 → b^n = c^n → b = c :=
assume (n : ℕ) (nodd : n % 2 = 1) (heq : b^n = c^n),
by_contradiction $ λ (hn : b ≠ c), or.elim3 (lt_trichotomy b c)
    (λ hbltc,
        have b^n < c^n, from odd_pow_lt n hbltc nodd,
        have b^n ≠ c^n, from ne_of_lt this,
        false.elim $ absurd heq this
    )
    (λ h, by contradiction)
    (λ hcltb,
        have c^n < b^n, from odd_pow_lt n hcltb nodd,
        have b^n ≠ c^n, from ne_of_gt this,
        false.elim $ absurd heq this
    )

-- (d)
theorem even_pows : ∀ (n : ℕ), n % 2 = 0 → a^n = (-a)^n
| 0 zeroeven := rfl
| 1 oneeven := by contradiction
| (n+2) neven := (
    have neven : n % 2 = 0, from neven,
    have ih : a^n = (-a)^n, from even_pows n neven,
    have sq_eq : a^2 = (-a)^2, from eq.symm $ calc
        (-a)^2  = (-a) * (-a) : pow_two (-a)
            ... = a * a : by rw neg_mul_neg
            ... = a^2 : by rw pow_two
    ,
    show a^(n+2) = (-a)^(n+2), from eq.symm $ calc
        (-a)^(n+2)  = (-a)^n * (-a)^2 : pow_add (-a) n 2
                ... = a^n * (-a)^2 : by rw ih
                ... = a^n * a^2 : by rw sq_eq
                ... = a^(n+2) : by rw pow_add
)


-- could be shortened by matching on positive/negative first, then whether b < c
-- or reverse
theorem pow_even_eq : ∀ (n : ℕ), 0 < n → n % 2 = 0 → b^n = c^n → (b = c ∨ b = -c) :=
assume n npos neven h,
have negcpowneq : (-c)^n = c^n, from eq.symm $ even_pows n neven,
have negbpowneq : (-b)^n = b^n, from eq.symm $ even_pows n neven,
or.elim (le_or_lt 0 b)
    (λ bnonneg,
        or.elim3 (lt_trichotomy b c)
            (λ bltc,
                have b^n < c^n, from pow_lt n npos bnonneg bltc,
                have b^n ≠ c^n, from ne_of_lt this,
                false.elim $ absurd h this
            )
            (λ beqc, or.inl beqc)
            (λ cltb,
                or.elim (le_or_lt 0 c)
                    (λ cnonneg,
                        have c^n < b^n, from pow_lt n npos cnonneg cltb,
                        have b^n ≠ c^n, from ne_of_gt this,
                        false.elim $ absurd h this
                    )
                    (λ cneg,
                        have negcpos : 0 < -c, from neg_pos.elim_right cneg,
                        or.elim3 (lt_trichotomy b (-c))
                            (λ bltnegc,
                                have b^n < (-c)^n, from pow_lt n npos bnonneg bltnegc,
                                have b^n < c^n, by rwa negcpowneq at this,
                                false.elim $ absurd h (ne_of_lt this)
                            )
                            (λ beqnegc, or.inr beqnegc)
                            (λ negcltb,
                                have (-c)^n < b^n, from pow_lt n npos (le_of_lt negcpos) negcltb,
                                have c^n < b^n, by rwa negcpowneq at this,
                                false.elim $ absurd h (ne_of_gt this)
                            )
                    )
            )
    )
    (λ bneg,
        have negbpos : 0 < -b, from neg_pos.elim_right bneg,
        or.elim3 (lt_trichotomy (-b) c)
            (λ (hbc : (-b) < c),
                have (-b)^n < c^n, from pow_lt n npos (le_of_lt negbpos) hbc,
                have b^n < c^n, by rwa [negbpowneq] at this,
                false.elim $ absurd h (ne_of_lt this)
            )
            (λ hnegbeqc, or.inr $ eq_neg_of_eq_neg $ eq.symm hnegbeqc)
            (λ (hbc : c < (-b)),
                or.elim (le_or_lt 0 c)
                    (λ cnonneg,
                        have c^n < (-b)^n, from pow_lt n npos cnonneg hbc,
                        have c^n < b^n, by rwa negbpowneq at this,
                        false.elim $ absurd h (ne_of_gt this)
                    )
                    (λ cneg,
                        have negcpos : 0 < -c, from neg_pos.elim_right cneg,
                        or.elim3 (lt_trichotomy (-b) (-c))
                            (λ (hlt: (-b < -c)),
                                have (-b)^n < (-c)^n, from pow_lt n npos (le_of_lt negbpos) hlt,
                                have b^n < c^n, by rwa [negcpowneq, negbpowneq] at this,
                                false.elim $ absurd h (ne_of_lt this)
                            )
                            (λ h,
                                have b = c, from neg_inj.elim_left h,
                                or.inl this
                            )
                            (λ (hlt : (-c) < (-b)),
                                have (-c)^n < (-b)^n, from pow_lt n npos (le_of_lt negcpos) hlt,
                                have c^n < b^n, by rwa [negcpowneq, negbpowneq] at this,
                                false.elim $ absurd h (ne_of_gt this)
                            )
                    )
            )
    )
