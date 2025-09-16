-- <vc-preamble>
def solve_array_sort (n : Nat) (arr : List Nat) : List Nat := sorry

def List.sort (l : List Nat) : List Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.swap3 (l : List α) (pos : Nat) : List α := sorry

theorem sort_already_sorted {n : Nat} {arr : List Nat} (h1 : n ≥ 3)
  (h2 : arr = List.range' 1 n) : 
  solve_array_sort n arr = [0] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_result_correctness {n : Nat} {arr : List Nat} (h1 : n ≥ 3)
  (h2 : arr.length = n)
  (result : List Nat) (h3 : result = solve_array_sort n arr) :
  result = [0] ∨ result = [Nat.zero] ∨
  (match result with
  | [] => False
  | num_moves :: moves =>
    moves.length = num_moves ∧
    let final := moves.foldl 
      (λ acc pos => acc.swap3 (pos-1)) arr;
    final.sort = List.range' 1 n) := sorry

/-
info: [0]
-/
-- #guard_msgs in
-- #eval solve_array_sort 5 [1, 2, 3, 4, 5]

/-
info: [6, 3, 1, 3, 2, 2, 3]
-/
-- #guard_msgs in
-- #eval solve_array_sort 5 [5, 4, 3, 2, 1]

/-
info: [4, 3, 3, 4, 4]
-/
-- #guard_msgs in
-- #eval solve_array_sort 6 [1, 2, 3, 3, 6, 4]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded