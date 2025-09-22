-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def format_numbers (n : Nat) : String := sorry

def length_nat (s : List String) : Nat := s.length
-- </vc-definitions>

-- <vc-theorems>
theorem format_numbers_equal_line_lengths (n : Nat)
  (h : 0 < n ∧ n ≤ 100) :
  ∀ i j, i < n → j < n → 
  (((format_numbers n).splitOn "\n")[i]!).length = 
  (((format_numbers n).splitOn "\n")[j]!).length :=
sorry
-- </vc-theorems>