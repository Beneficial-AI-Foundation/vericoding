-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def black_and_white (height : Nat) (width : Nat) (input : List Nat) : List (List Nat) := sorry

-- Basic cases
-- </vc-definitions>

-- <vc-theorems>
theorem basic_case1 : 
  black_and_white 2 100 [40, 120, 40, 0] = [[40, 60], [0, 60, 40, 0]] := sorry

theorem basic_case2 :
  black_and_white 2 100 [0, 180, 20, 0] = [[0, 100], [0, 80, 20, 0]] := sorry

-- Structural properties

theorem result_height (h w : Nat) (input : List Nat) :
  h > 0 → w > 0 → h ≤ 10 → w ≤ 100 →
  List.length (black_and_white h w [w]) = h := sorry

theorem row_length_even (h w : Nat) (input : List Nat) (row : List Nat) :
  h > 0 → w > 0 → h ≤ 10 → w ≤ 100 →
  row ∈ black_and_white h w [w] →
  ∃ k, List.length row = 2 * k := sorry

theorem values_nonnegative (h w : Nat) (input : List Nat) (row : List Nat) (x : Nat) :
  h > 0 → w > 0 → h ≤ 10 → w ≤ 100 →
  row ∈ black_and_white h w [w] →
  x ∈ row →
  x ≥ 0 := sorry

-- Single row case

theorem single_row :
  black_and_white 1 10 [10] = [[10, 0]] := sorry
-- </vc-theorems>