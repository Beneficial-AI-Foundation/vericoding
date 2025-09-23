-- <vc-preamble>
def List.sum (xs : List Nat) : Nat :=
match xs with
| [] => 0
| x::xs => x + xs.sum
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (numbers : List Nat) (n : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_sum_divisible_by_n {numbers : List Nat} {n : Nat} 
  (h1: 0 < n) (h2: ∀ x ∈ numbers, 0 < x) :
  (numbers.sum % n = 0) → solve numbers n = true :=
sorry

theorem solve_single_divisible_by_n {numbers : List Nat} {n : Nat}
  (h1: 0 < n) (h2: ∀ x ∈ numbers, 0 < x) :
  (∃ x ∈ numbers, x % n = 0) → solve numbers n = true :=
sorry

theorem solve_multiply_by_n {numbers : List Nat} {n : Nat}
  (h1: 0 < n) (h2: ∀ x ∈ numbers, 0 < x) :
  solve (List.map (· * n) numbers) n = true :=
sorry

theorem solve_with_sum_as_n {numbers : List Nat}
  (h: ∀ x ∈ numbers, 0 < x) :
  solve numbers numbers.sum = true :=
sorry

theorem solve_single_element {x n : Nat} (h1: 0 < x) (h2: 0 < n) :
  solve [x] n = (x % n = 0) :=
sorry

theorem solve_all_larger_than_n {numbers : List Nat} {n : Nat}
  (h1: 0 < n) (h2: ∀ x ∈ numbers, n < x) :
  solve numbers n = true :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval solve [1, 2, 3, 4, 5] 10

/-
info: False
-/
-- #guard_msgs in
-- #eval solve [8, 5, 3] 7

/-
info: True
-/
-- #guard_msgs in
-- #eval solve [8, 5, 3, 9] 7
-- </vc-theorems>