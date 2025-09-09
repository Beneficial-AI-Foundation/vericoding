-- <vc-helpers>
-- </vc-helpers>

def format_numbers (n : Nat) : String := sorry

def length_nat (s : List String) : Nat := s.length

theorem format_numbers_equal_line_lengths (n : Nat)
  (h : 0 < n ∧ n ≤ 100) :
  ∀ i j, i < n → j < n → 
  (((format_numbers n).splitOn "\n")[i]!).length = 
  (((format_numbers n).splitOn "\n")[j]!).length :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible