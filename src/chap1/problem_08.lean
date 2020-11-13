import data.real.basic

variables { a b c : ℝ }

-- First definitions

noncomputable def p10' : linear_ordered_field ℝ := by apply_instance

def p11' : a < b → b < c → a < c := lt_trans

def p12' : a < b → a + c < b + c := (add_lt_add_iff_right c).mpr

def p13' : a < b → 0 < c → a*c < b*c := mul_lt_mul_of_pos_right

-- Now the problem

def newP10 : a = 0 ∨ 0 < a ∨ a < 0 :=
begin
    rcases (lt_trichotomy 0 a) with aGt | aEq | aLt,
    right, left, exact aGt,
    left, exact (eq.symm $ aEq),
    right, right, exact aLt
end

def newP11 : 0 < a → 0 < b → 0 < a + b :=
assume aPos bPos,
have 0 + b < a + b, from p12' aPos,
have b < a + b, by rwa zero_add at this,
p11' bPos this

def newP12 : 0 < a → 0 < b → 0 < a * b :=
assume aPos bPos,
have 0*b < a*b, from p13' aPos bPos,
by rwa [zero_mul] at this
