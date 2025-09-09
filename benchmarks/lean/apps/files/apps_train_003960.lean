-- <vc-helpers>
-- </vc-helpers>

def cake (candles: Nat) (s: String) : String :=
  sorry

theorem cake_empty_string :
  cake 10 "" = "That was close!" :=
sorry

theorem cake_zero_candles :
  cake 0 "abc" = "That was close!" :=
sorry 

theorem cake_known_case1 :
  cake 900 "abcdef" = "That was close!" :=
sorry

theorem cake_known_case2 :
  cake 56 "ifkhchlhfd" = "Fire!" := 
sorry

/-
info: 'That was close!'
-/
-- #guard_msgs in
-- #eval cake 900 "abcdef"

/-
info: 'Fire!'
-/
-- #guard_msgs in
-- #eval cake 56 "ifkhchlhfd"

/-
info: 'That was close!'
-/
-- #guard_msgs in
-- #eval cake 0 "jpipe"

-- Apps difficulty: introductory
-- Assurance level: unguarded