-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def repeater (s : String) (n : Nat) : String := sorry

theorem repeater_length (s : String) (n : Nat) : 
  (repeater s n).length = s.length * n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem repeater_eq_concat (s : String) (n : Nat) :
  repeater s n = String.join (List.replicate n s) := sorry
-- </vc-theorems>