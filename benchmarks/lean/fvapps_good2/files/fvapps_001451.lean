-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_valid_bracket_sequence (n : Nat) : List Nat :=
  sorry

def analyze_brackets (n : Nat) (brackets : List Nat) : Nat × Nat × Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minimal_valid_case :
  analyze_brackets 2 [1,2] = (1,1,2,1) :=
sorry

theorem nested_depth_increases :
  (analyze_brackets 4 [1,1,2,2]).1 = 2 :=
sorry
-- </vc-theorems>