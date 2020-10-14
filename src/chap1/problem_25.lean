
inductive MiniNumber : Type
| Zero : MiniNumber
| One : MiniNumber

open MiniNumber (One Zero)

def add : MiniNumber → MiniNumber → MiniNumber
| Zero Zero := Zero
| Zero One := One
| One Zero := One
| One One := Zero

def mul : MiniNumber → MiniNumber → MiniNumber
| One One := One
| _  _ := Zero

-- Now check P{1 to 9}

instance : has_add MiniNumber := ⟨add⟩
instance : has_mul MiniNumber := ⟨mul⟩

def p1 : ∀ (a b c : MiniNumber), a + (b + c) = (a + b) + c
| Zero Zero Zero := rfl
| Zero Zero One := rfl
| Zero One Zero := rfl
| One Zero Zero := rfl
| Zero One One := rfl
| One One Zero := rfl
| One Zero One := rfl
| One One One := rfl

def p2 : ∀ a, a + Zero = a
| Zero := rfl
| One := rfl

def neg : ∀ (a : MiniNumber), MiniNumber
| Zero := Zero
| One := One

def p3 : ∀ a, a + (neg a) = Zero
| Zero := rfl
| One := rfl

def p4 : ∀ (a b : MiniNumber), a + b = b + a
| Zero Zero := rfl
| One One := rfl
| Zero One := rfl
| One Zero := rfl

def p5 : ∀ (a b c : MiniNumber), a * (b*c) = (a*b) * c
| Zero Zero Zero := rfl
| Zero Zero One := rfl
| Zero One Zero := rfl
| One Zero Zero := rfl
| Zero One One := rfl
| One One Zero := rfl
| One Zero One := rfl
| One One One := rfl

def p6 : ∀ (a : MiniNumber), a * One = a
| Zero := rfl
| One := rfl

def inv : ∀ (a : MiniNumber), MiniNumber
| Zero := Zero
| One := One

def p7 : ∀ (a : MiniNumber), a ≠ Zero → a * inv a = One
| Zero _ := by contradiction
| One _ := rfl

def p8 : ∀ (a b : MiniNumber), a * b = b * a
| Zero Zero := rfl
| Zero One := rfl
| One Zero := rfl
| One One := rfl

def p9 : ∀ (a b c : MiniNumber), a * (b + c) = a * b + a * c
| Zero Zero Zero := rfl
| Zero Zero One := rfl
| Zero One Zero := rfl
| One Zero Zero := rfl
| Zero One One := rfl
| One One Zero := rfl
| One Zero One := rfl
| One One One := rfl
