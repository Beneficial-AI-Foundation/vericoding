-- <vc-helpers>
-- </vc-helpers>

def ValidResult := ["FRIENDS", "LOVE", "ADORE", "MARRIAGE", "ENEMIES", "SISTER"]

def calculate_flames (name1 : String) (name2 : String) : String :=
  sorry

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

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible