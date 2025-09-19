-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_string_alternation (n : Nat) (s : String) : Nat := sorry

/- Main theorem combining several properties of solve_string_alternation:
  1. Output is non-negative
  2. Output is less than string length 
  3. Output relates to number of adjacent duplicates
-/
-- </vc-definitions>

-- <vc-theorems>
theorem solve_string_alternation_properties (s : String) (n : Nat) 
  (h1 : s.length = n) (h2 : n > 0) (h3 : ∀c ∈ s.data, c = '0' ∨ c = '1') :
  let result := solve_string_alternation n s
  let adjacent_same := (List.zip s.data s.data.tail).filter (fun p => p.1 = p.2) |>.length
  (result ≥ 0) ∧ 
  (result < n) ∧
  (result = (adjacent_same + adjacent_same % 2) / 2) := sorry
-- </vc-theorems>