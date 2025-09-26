-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_cyclic_shift_game (s : String) : Float := sorry

def is_valid_result (s : String) (result : Float) : Prop :=
  0 ≤ result ∧ result ≤ 1 ∧ 
  (Float.abs (result - ((Float.floor (result * (Float.ofNat s.length))) / (Float.ofNat s.length))) < 0.000001)
-- </vc-definitions>

-- <vc-theorems>
theorem solve_cyclic_shift_game_properties (s : String) (h : s.length > 0) :
  is_valid_result s (solve_cyclic_shift_game s) := sorry

theorem binary_string_properties (s : String) 
  (h1 : s.length > 0)
  (h2 : ∀ c ∈ s.data, c = 'a' ∨ c = 'b') :
  is_valid_result s (solve_cyclic_shift_game s) := sorry

theorem repeated_string_properties (s : String) (t : String)
  (h1 : s.length > 0) 
  (h2 : t = s ++ s) :
  is_valid_result t (solve_cyclic_shift_game t) := sorry

theorem single_char :
  solve_cyclic_shift_game "a" = 0 := sorry
-- </vc-theorems>