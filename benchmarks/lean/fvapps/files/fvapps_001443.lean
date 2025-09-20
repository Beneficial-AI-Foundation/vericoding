-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_path_number : String → Nat :=
  sorry

def MOD : Nat := 1000000007

def mkString (c : String) (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_path_number_positive (s : String) :
  find_path_number s > 0 := by
sorry

theorem find_path_number_within_bounds (s : String) :
  find_path_number s < MOD := by
sorry

theorem find_path_number_empty :
  find_path_number "" = 1 := by
sorry

theorem find_path_number_single_char :
  find_path_number "l" = 2 ∧ find_path_number "r" = 4 := by
sorry

theorem find_path_number_concat_bounds (s : String) :
  find_path_number (s ++ s) < MOD := by
sorry

theorem find_path_number_lr_distinct (n : Nat) (h : n > 0) (h2 : n ≤ 100) :
  find_path_number (mkString "l" n) ≠
  find_path_number (mkString "r" n) := by
sorry

theorem find_path_number_modulo (s : String) :
  find_path_number s = find_path_number s % MOD := by
sorry

theorem find_path_number_concat_distinct (s1 s2 : String)
  (h1 : s1 ≠ "") (h2 : s2 ≠ "") :
  find_path_number (s1 ++ s2) ≠ find_path_number s1 ∧
  find_path_number (s1 ++ s2) ≠ find_path_number s2 := by
sorry
-- </vc-theorems>