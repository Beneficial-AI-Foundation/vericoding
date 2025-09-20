-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hex_color (input : String) : String := sorry

theorem valid_color_output (input : String) :
  hex_color input ∈ ["black", "red", "green", "blue", "magenta", "yellow", "cyan", "white"] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_values_black (r g b : Nat) :
  r = 0 → g = 0 → b = 0 → hex_color s!"${r} ${g} ${b}" = "black" := sorry 

theorem equal_nonzero_white (n : Nat) :
  n > 0 → hex_color s!"${n} ${n} ${n}" = "white" := sorry

theorem single_nonzero_primary (r g b : Nat) :
  (r > 0 ∧ g = 0 ∧ b = 0) → hex_color s!"${r} ${g} ${b}" = "red"
  ∧ (r = 0 ∧ g > 0 ∧ b = 0) → hex_color s!"${r} ${g} ${b}" = "green"
  ∧ (r = 0 ∧ g = 0 ∧ b > 0) → hex_color s!"${r} ${g} ${b}" = "blue" := sorry

theorem two_equal_maxes_secondary (r g b : Nat) :
  (r > 0 ∧ g > 0 ∧ b = 0 ∧ r = g) → hex_color s!"${r} ${g} ${b}" = "yellow"
  ∧ (r > 0 ∧ g = 0 ∧ b > 0 ∧ r = b) → hex_color s!"${r} ${g} ${b}" = "magenta"
  ∧ (r = 0 ∧ g > 0 ∧ b > 0 ∧ g = b) → hex_color s!"${r} ${g} ${b}" = "cyan" := sorry
-- </vc-theorems>