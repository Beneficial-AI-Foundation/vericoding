-- <vc-preamble>
def List.min_length (a b : List α) : Nat :=
  min a.length b.length

def List.everyOther : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: everyOther xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_uncrossed_lines (a b : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_uncrossed_lines_nonnegative (a b : List Nat) :
  max_uncrossed_lines a b ≥ 0 :=
sorry

theorem max_uncrossed_lines_upper_bound (a b : List Nat) :
  max_uncrossed_lines a b ≤ min a.length b.length :=
sorry

theorem max_uncrossed_lines_empty (a b : List Nat) :
  a = [] ∨ b = [] → max_uncrossed_lines a b = 0 :=
sorry

theorem max_uncrossed_lines_identical (a : List Nat) :
  max_uncrossed_lines a a = a.length :=
sorry

theorem max_uncrossed_lines_reverse (a b : List Nat) :
  max_uncrossed_lines a b = max_uncrossed_lines a.reverse b.reverse :=
sorry

theorem max_uncrossed_lines_edge_cases :
  max_uncrossed_lines [] [] = 0 ∧
  max_uncrossed_lines [1] [] = 0 ∧
  max_uncrossed_lines [] [1] = 0 :=
sorry
-- </vc-theorems>