-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.repeat (s : String) (n : Nat) : String := sorry

def repeater (s : String) (n : Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem repeater_format_match (s : String) (n : Nat) (h : s.length > 0) :
  repeater s n = "\"" ++ s ++ "\" repeated " ++ toString n ++ " times is: \"" ++ (String.repeat s n) ++ "\"" := sorry

theorem repeater_length (s : String) (n : Nat) (h : s.length > 0) :
  (repeater s n).length = 
    s.length * n + ("\" repeated " ++ toString n ++ " times is: \"\"").length := sorry

theorem repeater_zero_empty_result (s : String) :
  ∃ (p : String), repeater s 0 = p ++ "\"\"" := sorry
-- </vc-theorems>