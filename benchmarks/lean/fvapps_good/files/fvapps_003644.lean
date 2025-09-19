-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def goto (level : Int) (button : String) : Int := sorry

theorem goto_valid_inputs (level : Int) (button : String) 
  (h1 : 0 ≤ level ∧ level ≤ 3) 
  (h2 : button = "0" ∨ button = "1" ∨ button = "2" ∨ button = "3") : 
  ∃ result : Int, goto level button = result ∧ result = button.toInt! - level := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem goto_invalid_level (level : Int) (button : String)
  (h1 : level < 0 ∨ level > 3)
  (h2 : button = "0" ∨ button = "1" ∨ button = "2" ∨ button = "3") :
  goto level button = 0 := sorry

theorem goto_invalid_button (level : Int) (button : String)
  (h1 : 0 ≤ level ∧ level ≤ 3)
  (h2 : button ≠ "0" ∧ button ≠ "1" ∧ button ≠ "2" ∧ button ≠ "3") :
  goto level button = 0 := sorry

theorem goto_invalid_level_type (level : String) (button : String)
  (h : button = "0" ∨ button = "1" ∨ button = "2" ∨ button = "3") : 
  goto 0 button = 0 := sorry

theorem goto_invalid_button_type (level : Int) (button : Int)
  (h : 0 ≤ level ∧ level ≤ 3) :
  goto level "" = 0 := sorry
-- </vc-theorems>