-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pascal (n : Nat) : List (List Nat) := sorry

theorem pascal_row_count {n : Nat} (h : n > 0) : 
  List.length (pascal n) = n := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>