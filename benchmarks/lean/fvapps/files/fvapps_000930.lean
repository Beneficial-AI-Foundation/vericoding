-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_pattern (k : Nat) : List String := sorry

theorem minimal_cases:
  generate_pattern 1 = ["*"] ∧
  generate_pattern 2 = ["*", "***"] ∧
  generate_pattern 3 = ["  *  ", " * * ", "*****"] :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_length (k : Nat) (h : k > 0):
  (generate_pattern k).length = k :=
sorry

theorem pattern_valid_chars (k : Nat) (h : k > 0):
  ∀ line ∈ generate_pattern k,
  ∀ c ∈ line.data, c = ' ' ∨ c = '*' :=
sorry

theorem last_line_asterisks (k : Nat) (h : k > 1):
  (generate_pattern k).getLast (by sorry) =
  String.mk (List.replicate (2*k - 1) '*') :=
sorry

theorem first_line_centered (k : Nat) (h : k > 2):
  (generate_pattern k).head! =
  String.mk (List.replicate (k-1) ' ' ++ '*' :: List.replicate (k-1) ' ') :=
sorry
-- </vc-theorems>