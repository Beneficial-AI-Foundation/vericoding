-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) : Bool :=
  sorry

def eraseDuplicates (xs : List α) : List α :=
  sorry

def sortList (xs : List α) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_valid_string_properties (s : String) :
  solve s →
  (s.length : Nat) = (eraseDuplicates s.toList).length ∧
  sortList (s.toList.map Char.toLower) = s.toList := by
  sorry

theorem solve_invalid_chars (s : String) :
  s.toList.all (λ c => ¬c.isLower) →
  ¬(solve s) := by
  sorry

theorem solve_duplicates (s : String) :
  s.length > 0 →
  ¬(solve (s ++ s)) := by
  sorry

theorem solve_empty :
  ¬(solve "") := by
  sorry
-- </vc-theorems>