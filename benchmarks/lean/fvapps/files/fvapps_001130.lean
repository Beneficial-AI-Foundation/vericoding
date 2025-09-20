-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ValidResult := ["FRIENDS", "LOVE", "ADORE", "MARRIAGE", "ENEMIES", "SISTER"]

def calculate_flames (name1 : String) (name2 : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_flames_symmetry (name1 name2 : String) :
  name1 ≠ "" → name2 ≠ "" →
  calculate_flames name1 name2 = calculate_flames name2 name1 :=
sorry

theorem calculate_flames_whitespace_invariant (name : String) :
  name ≠ "" →
  calculate_flames name "test" = calculate_flames (name ++ "  ") "test" ∧
  calculate_flames name "test" = calculate_flames (" " ++ name ++ " ") "test" :=
sorry

theorem calculate_flames_identical_names (name : String) :
  name ≠ "" →
  calculate_flames name name = calculate_flames "a" "a" :=
sorry
-- </vc-theorems>