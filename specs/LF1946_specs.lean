-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + xs.sum
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_coloring (n : Nat) (m : Nat) (lengths : List Nat) : Option (List Nat) := sorry

theorem impossible_cases_sum_too_small {n m : Nat} {lengths : List Nat} 
  (h₁ : m > 0)
  (h₂ : n > 0) 
  (h₃ : lengths.length = m)
  (h₄ : lengths.sum < n) :
  solve_coloring n m lengths = none := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem impossible_cases_lengths_too_long {n m : Nat} {lengths : List Nat}
  (h₁ : m > 0)
  (h₂ : n > 0)
  (h₃ : lengths.length = m)
  (h₄ : ∀ l ∈ lengths, l > n) :
  solve_coloring n m lengths = none := sorry

theorem solution_basic_properties {n m : Nat} {lengths : List Nat} {result : List Nat}
  (h₁ : m > 0)
  (h₂ : n > 0)
  (h₃ : lengths.length = m)
  (h₄ : solve_coloring n m lengths = some result) :
  result.length = m ∧ 
  (∀ x ∈ result, x > 0 ∧ x ≤ n) ∧
  (∀ i < result.length - 1, result[i]! < result[i+1]!) := sorry

/-
info: [1, 2, 4]
-/
-- #guard_msgs in
-- #eval solve_coloring 5 3 [3, 2, 2]

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_coloring 10 1 [1]

/-
info: [1]
-/
-- #guard_msgs in
-- #eval solve_coloring 1 1 [1]
-- </vc-theorems>