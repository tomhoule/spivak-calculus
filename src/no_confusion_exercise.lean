

-- see https://xenaproject.wordpress.com/2018/03/24/no-confusion-over-no_confusion/

inductive xnat : Type
| zero : xnat
| succ : xnat → xnat

open xnat

def xnat_equal : xnat → xnat → Prop
| zero zero := true
| zero _ := false
| _ zero := false
| (succ m) (succ n) := xnat_equal m n

example : xnat_equal zero zero = true := rfl
example : xnat_equal zero (succ zero) = false := rfl
example : xnat_equal (succ zero) (succ zero) = true := rfl
example : xnat_equal (succ (succ zero)) (succ zero) = false := rfl

lemma xnat_equal_self : ∀ n, xnat_equal n n := λ n,
xnat.rec_on n
    (show xnat_equal zero zero, from trivial)
    (λ n ih, show xnat_equal n.succ n.succ, by assumption)

def xnat_no_confusion {m n : xnat} : m = n → xnat_equal m n :=
begin
intro heq,
rw heq,
exact xnat_equal_self n
end

#check @xnat_no_confusion

example : ∀ n : xnat, zero ≠ succ n :=
assume hn hzerosucc, xnat_no_confusion hzerosucc
