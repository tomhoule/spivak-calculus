namespace properties
    open int

    variables (a b c x : ℤ)

    -- P1
    def add_assoc : a + (b + c) = (a + b) + c := by rw [@int.add_assoc a b c]

    -- P2
    def add_zero : a + 0 = a := @int.add_zero a
    def zero_add : 0 + a = a := @int.zero_add a

    -- P3
    def add_opp : a + (-a) = 0 := by rw [@int.add_comm, @int.add_left_neg a]
    def opp_add : (-a) + a = 0 := @int.add_left_neg a

    example : (a + x = a) → x = 0 :=
    assume h,
    calc
        x = 0 + x : by rw zero_add
            ... = (-a + a) + x : by rw opp_add
            ... = -a + (a + x) : by rw add_assoc
            ... = -a + a : by rw h
            ... = 0 : by rw opp_add

    example : (x + 3 = 5) → (x = 2) :=
    assume h,
    calc
        x   = x + 0 : by rw add_zero
        ... = x + (3 + -3) : by rw add_opp
        ... = 5 + (-3) : by rw [add_assoc, h]
        ... = 5 - 3 : rfl
        ... = 2 : by reflexivity

    -- P4
    def add_comm : a + b = b + a := @int.add_comm a b



end properties
