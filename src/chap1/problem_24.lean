import data.real.basic
import algebra.big_operators.basic
import data.vector

open_locale big_operators

variables { a a1 a2 a3 : ℝ }
    { n k : ℕ }
    { as : vector ℝ k }
    { bs : vector ℝ n }

-- Make addition right-associative.
reserve infix ` + ` :80

example : a1 + a2 + a3 = a1 + (a2 + a3) := rfl

-- The line below shouldn't type-check:
-- example : a1 + a2 + a3 = (a1 + a2) + a3 := rfl

-- (a)
def list_sum : list ℝ → ℝ
| list.nil := 0
| (list.cons n tail) := n + list_sum tail

def list_sum_nil : list_sum list.nil = 0 := rfl
def list_sum_singleton : ∀ n, n = list_sum [n] :=
λ n,
have list_sum [n] = n + 0, from rfl,
eq.symm $ by rwa [add_zero n] at this

def part_a : ∀ (nums : list ℝ), list_sum (a::nums) = list_sum (list.append nums (list.cons a list.nil))
| list.nil := rfl
| (list.cons n list.nil) := by {
    have left : list_sum [a, n] = a + n + 0, from rfl,
    have right : list_sum (list.append [n] [a]) = n + a + 0, from rfl,
    rw [left, right, add_zero, add_zero, add_comm]
}
| (list.cons n tail) := by {
    have ih : list_sum (a :: tail) = list_sum (list.append tail [a]), from part_a tail,
    have left : list_sum (a :: n :: tail) = list_sum (n :: a :: tail), from (
        calc
        list_sum (a :: n :: tail) = a + n + list_sum tail : rfl
        ... = n + a + list_sum tail : add_left_comm a n (list_sum tail)
        ... = list_sum (n :: a :: tail) : rfl
    ),
    have right : list_sum (n :: a :: tail) = list_sum (list.append (n :: tail) [a]), from (
        calc
        list_sum (n :: a :: tail) = n + list_sum (a :: tail) : rfl
        ... = n + list_sum (list.append tail [a]) : by rw [ih]
        ... = list_sum (list.append (n::tail) [a]) : rfl
    ),
    cc
}

-- (b)


-- First try with vectors: it turned out really complicated to compose the
-- induction proof with dependent types. The list proof that follows proves the
-- point.

-- def vector_sum : ∀ n, vector ℝ n → ℝ
-- | 0 v := 0
-- | (n+1) nums := by {
--     exact vector.head nums + vector_sum n (vector.tail nums)
-- }


-- def part_b : ∀ (k n : ℕ) (v1 : vector ℝ k) (v2 : vector ℝ (n-k)), k ≤ n →
--     vector_sum k v1 + vector_sum (n-k) v2 = vector_sum (k + (n-k)) (vector.fappend v1 v2)
-- | 0 0 v1 v2 kLtN := by {
--     have left : vector_sum 0 v1 + vector_sum (0-0) v2 = 0, from (
--         calc
--         vector_sum 0 v1 + vector_sum (0-0) v2 = 0 + 0 : rfl
--         ... = 0 : add_zero 0
--     ),
--     have right : vector_sum (0 + (0-0)) (vector.fappend v1 v2) = 0, from (
--         calc
--         vector_sum (0 + (0-0)) (vector.fappend v1 v2) = vector_sum 0 (vector.fappend v1 v2) : by norm_num
--         ... = 0 : rfl
--     ),
--     cc
-- }
-- | 0 n v1 v2 kLtN := by {
--     have v1 : vector ℝ 0, from v1,
--     have v2 : vector ℝ n, from v2,
--     have left : vector_sum 0 v1 + vector_sum (n-0) v2 = vector_sum n v2, from (
--         calc
--         vector_sum 0 v1 + vector_sum (n-0) v2 = 0 + vector_sum (n-0) v2 : rfl
--         ... = vector_sum (n-0) v2 : by rw zero_add
--         ... = vector_sum n v2 : by simpa
--     ),
--     have right : vector_sum (0 + (n-0)) (v1.fappend v2) = vector_sum n v2, from (
--         have v1 = vector.nil, from vector.eq_nil v1,
--         sorry
--     ),
--     have : vector_sum 0 v1 + vector_sum (n - 0) v2 = vector_sum (0 + (n - 0)) (v1.fappend v2), from sorry,
--     assumption
-- }
-- | k n v1 v2 kLtN := sorry

def part_b : ∀ (l1 : list ℝ) (l2 : list ℝ), list_sum l1 + list_sum l2 = list_sum (l1 ++ l2)
| [] [] := by {
    have left : list_sum list.nil + list_sum list.nil = 0, from (
        calc
        list_sum list.nil + list_sum list.nil = 0 + 0 : rfl
        ... = 0 : zero_add 0
    ),
    have right : list_sum (list.nil ++ list.nil) = 0, from rfl,
    cc
}
| [] right := by {
    have left : list_sum list.nil + list_sum right = list_sum right, from (
        calc
        list_sum list.nil + list_sum right = 0 + list_sum right : rfl
        ... = list_sum right : zero_add (list_sum right)
    ),
    have right : list_sum (list.nil ++ right) = list_sum right, from rfl,
    cc

}
| leftL [] := by {
    have left : list_sum leftL + list_sum list.nil = list_sum leftL, from (
        calc
        list_sum leftL + list_sum list.nil = list_sum leftL + 0 : rfl
        ... = list_sum leftL : add_zero (list_sum leftL)
    ),
    have right : list_sum (leftL ++ list.nil) = list_sum leftL, by rw [list.append_nil],
    cc

}
| (headL::tailL) (rightL) := by {
    have ih : list_sum tailL + list_sum rightL = list_sum (tailL ++ rightL), from part_b tailL rightL,
    have left : list_sum (headL::tailL) + list_sum (rightL) = headL + list_sum tailL + list_sum rightL, from (
        calc
        list_sum (headL::tailL) + list_sum rightL = (headL + list_sum tailL) + list_sum rightL : rfl
        ... = headL + list_sum tailL + list_sum rightL : by ring
    ),
    have right : list_sum ((headL::tailL) ++ rightL) = headL + list_sum tailL + list_sum rightL, from (
        calc
        list_sum ((headL::tailL) ++ rightL) = headL + list_sum (tailL ++ rightL) : rfl
        ... = headL + list_sum tailL + list_sum rightL : by rw ih
    ),
    cc
}

-- (c)

example : list_sum list.nil = 0 := rfl
example : ∀ (l : list ℝ), list_sum (list.nil ++ l) = list_sum l := assume l, by rw [list.nil_append]

-- Helpers for part_c
def running_list_sum : ℝ → list ℝ → ℝ
| n l := n + list_sum l

def running_list_sum_nil : ∀ n : ℝ, running_list_sum n list.nil = n := assume n,
have running_list_sum n list.nil = n + 0, from rfl,
by rwa add_zero at this

-- There is probably a much shorter proof using monoid instances.
def foldl_running_list_assoc : ∀ (l : list (list ℝ)) (n : ℝ), l.foldl running_list_sum n = n + l.foldl running_list_sum 0
| [] := λ n, (
    calc
    [].foldl running_list_sum n = n : rfl
    ... = n + 0 : by rw [add_zero]
)
| ([]::tail) := λ n, (
    have ih : tail.foldl running_list_sum n = n + tail.foldl running_list_sum 0, from foldl_running_list_assoc tail n,
    calc
    (list.cons [] tail).foldl running_list_sum n = tail.foldl running_list_sum (n + list_sum []) : rfl
    ... = tail.foldl running_list_sum (n + 0) : rfl
    ... = n + tail.foldl running_list_sum 0 : by rw [add_zero, ih]
    ... = n + tail.foldl running_list_sum (list_sum []) : by rw [<-list_sum_nil]
    ... = n + tail.foldl running_list_sum (0 + list_sum []) : by rw [zero_add]
    ... = n + (list.cons [] tail).foldl running_list_sum 0 : rfl
)
| ((head::innerTail)::tail) := λ n, (
    have ih : (list.cons innerTail tail).foldl running_list_sum (n+head) = (n+head) + (list.cons innerTail tail).foldl running_list_sum 0, from foldl_running_list_assoc (list.cons innerTail tail) (n+head),
    have ih' : (list.cons innerTail tail).foldl running_list_sum head = head + (list.cons innerTail tail).foldl running_list_sum 0, from foldl_running_list_assoc (list.cons innerTail tail) head,
    calc
    (list.cons (list.cons head innerTail) tail).foldl running_list_sum n = tail.foldl running_list_sum (n + list_sum (head::innerTail)) : rfl
    ... = tail.foldl running_list_sum (n + head + list_sum innerTail) : rfl
    ... = tail.foldl running_list_sum ((n + head) + list_sum innerTail) : by rw [add_assoc]
    ... = (list.cons innerTail tail).foldl running_list_sum (n + head) : rfl
    ... = (n+head) + (list.cons innerTail tail).foldl running_list_sum 0 : by rw [ih]
    ... = n + ((list.cons innerTail tail).foldl running_list_sum head) : by rw [add_assoc, <-ih']
    ... = n + ((list.cons innerTail tail).foldl running_list_sum (0 + list_sum [head])) : by rw [<-list_sum_singleton head, zero_add]
    ... = n + tail.foldl running_list_sum ((0 + list_sum [head]) + list_sum innerTail) : by refl
    ... = n + tail.foldl running_list_sum (0 + (list_sum [head] + list_sum innerTail)) : by rw [add_assoc 0 (list_sum [head])]
    ... = n + tail.foldl running_list_sum (0 + (list_sum ([head] ++ innerTail))) : by rw [<-part_b ([head]) innerTail]
    ... = n + tail.foldl running_list_sum (0 + list_sum (head::innerTail)): by rw [list.singleton_append]
    ... = n + (list.cons (list.cons head innerTail) tail).foldl running_list_sum 0 : rfl
)

-- For any list of lists of sums, show that the sum of the list_sum's is equal
-- to the list_sum of the concatenated lists. This shows the precedent of
-- additions does not matter.
def part_c : ∀ (sums : list (list ℝ)), list_sum (list.join sums) = sums.foldl running_list_sum 0
| [] := rfl
-- Works, but no longer needed.
-- | ([]::tail) := by {
--     have ih : list_sum (list.join tail) = tail.foldl running_list_sum 0, from part_c tail,
--     have left : list_sum (list.join ([]::tail)) = list_sum (list.join tail), by {
--         have : list_sum (list.join ([]::tail)) = list_sum ([] ++ list.join tail), by refl,
--         have : list_sum ([] ++ list.join tail) = list_sum [] + list_sum (list.join tail), from (part_b list.nil (list.join tail)).symm,
--         have : list_sum [] + list_sum (list.join tail) = list_sum (list.join tail), by rw [list_sum_nil, zero_add],
--         cc
--     },
--     have right : ([]::tail).foldl running_list_sum 0 = tail.foldl running_list_sum 0, by {
--         have : ([]::tail).foldl running_list_sum 0 = tail.foldl running_list_sum (running_list_sum 0 []), from rfl,
--         rwa running_list_sum_nil at this
--     },
--     cc
-- }
| (head::tail) := by {
    let consed := list.cons head tail,
    have ih : list_sum (list.join tail) = tail.foldl running_list_sum 0, from part_c tail,
    have left : list_sum (list.join consed) = list_sum head + list_sum (list.join tail), from (
        calc
        list_sum (list.join (head::tail)) = list_sum (head ++ list.join tail) : rfl
        ... = list_sum head + list_sum (list.join tail) : (part_b head (list.join tail)).symm
    ),
    have right : consed.foldl running_list_sum 0 = list_sum head + tail.foldl running_list_sum 0, from (
      calc
      consed.foldl running_list_sum 0 = tail.foldl running_list_sum (0 + list_sum head) : rfl
      ... = tail.foldl running_list_sum (list_sum head) : by rw [zero_add]
      ... = list_sum head + tail.foldl running_list_sum 0 : foldl_running_list_assoc tail (list_sum head)
    ),
    rw [<-ih] at right,
    exact eq.trans left (eq.symm right)
}
