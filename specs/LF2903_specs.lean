-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_str (a b : String) : String := sorry

def isValidInt (s : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_str_matches_actual_sum (a b : Int) : 
  sum_str (toString a) (toString b) = toString (a + b) := sorry

theorem empty_string_treated_as_zero (empty : Option String) : 
  sum_str "1" (empty.getD "") = "1" ∧ 
  sum_str (empty.getD "") "1" = "1" ∧
  sum_str (empty.getD "") (empty.getD "") = "0" := sorry

theorem invalid_inputs_raise (s : String) : 
  ¬s.trim.isEmpty → ¬(isValidInt s) →
  (∀ (t : String), sum_str s t = "error" ∧ sum_str t s = "error") := sorry
-- </vc-theorems>