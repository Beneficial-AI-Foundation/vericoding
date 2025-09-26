-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_chess_subboard (n m : Nat) (board : List String) (queries : List Nat) : List Nat := sorry 

theorem max_chess_subboard_result_length {n m : Nat} {board : List String} {queries : List Nat} :
  (List.length (max_chess_subboard n m board queries)) = (List.length queries) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_chess_subboard_bounds {n m : Nat} {board : List String} {queries : List Nat} (result : List Nat) :
  result = max_chess_subboard n m board queries →
  ∀ x ∈ result, 1 ≤ x ∧ x ≤ min n m := sorry

theorem max_chess_subboard_monotonic {n m : Nat} {board : List String} (queries : List Nat) :
  let result := max_chess_subboard n m board queries
  ∀ i j : Nat, i < j → i < result.length → j < result.length → 
    result[i]! ≤ result[j]! := sorry

theorem max_chess_subboard_dimension_bound {n m : Nat} {board : List String} {queries : List Nat} (result : List Nat) : 
  result = max_chess_subboard n m board queries →
  ∀ x ∈ result, x ≤ min n m := sorry

theorem perfect_board_max_size {n m : Nat} (h1 : n > 0) (h2 : m > 0) :
  let board := List.range n |>.map (fun i => 
    String.mk (List.range m |>.map (fun j => if (i + j) % 2 = 0 then '0' else '1')))
  (max_chess_subboard n m board [0]).head! = min n m := sorry
-- </vc-theorems>