-- <vc-preamble>
def List.sum (xs : List Nat) : Nat :=
match xs with
| [] => 0
| x :: xs => x + List.sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_max_subsequence (n : Nat) (k : Nat) (arr : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_max_subsequence_basic_properties 
  (n k : Nat)
  (arr : List Nat) 
  (h1 : n > 0)
  (h2 : k > 0)
  (h3 : n = arr.length) :
  let result := solve_max_subsequence n k arr
  -- Result is non-negative
  (result ≥ 0) ∧
  -- Result doesn't exceed array sum  
  (result ≤ arr.sum) ∧ 
  -- Result positive unless all zeros
  (result > 0 ∨ arr.all (·= 0)) ∧
  -- Result respects even/odd sum
  (result ≤ (arr.filter (·%2 = 0)).sum + (arr.filter (·%2 = 1)).sum) :=
sorry

theorem solve_max_subsequence_single_element
  (n : Nat)
  (h : n > 0) :
  solve_max_subsequence 1 1 [n] = n :=
sorry

theorem solve_max_subsequence_consecutive
  (arr : List Nat)
  (h1 : arr.length ≥ 2) :
  let n := arr.length
  let result := solve_max_subsequence n 1 arr
  let max_consecutive := (List.range (n-1)).foldl (fun acc i => 
    max acc (arr[i]! + arr[i+1]!)) 0
  result ≥ max_consecutive / 2 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_max_subsequence 1 1 [3]

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_max_subsequence 2 1 [2, 2]

/-
info: 11
-/
-- #guard_msgs in
-- #eval solve_max_subsequence 5 2 [1, 2, 3, 4, 6]
-- </vc-theorems>