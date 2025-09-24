-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mobile_keyboard (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mobile_keyboard_non_negative (s : String) :
  mobile_keyboard s ≥ 0 := sorry 

theorem mobile_keyboard_sum_of_costs (s : String) (char_costs : Char → Nat) :
  mobile_keyboard s = s.foldl (fun acc c => acc + char_costs c) 0 := sorry

theorem mobile_keyboard_empty :
  mobile_keyboard "" = 0 := sorry

theorem mobile_keyboard_single_char (c : Char) (pos : Nat) :
  mobile_keyboard c.toString = pos := sorry

theorem mobile_keyboard_valid_chars (s : String) :
  s.all (fun c => c ∈ ['1', '2', '3', '4', '5', '6', '7', '8', '9', '0', '*', '#', 
                      'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 
                      'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z']) →
  mobile_keyboard s ≥ 0 := sorry
-- </vc-theorems>