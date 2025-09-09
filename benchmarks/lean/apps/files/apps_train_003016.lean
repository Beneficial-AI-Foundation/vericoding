-- <vc-helpers>
-- </vc-helpers>

def derivative (s : String) : String := sorry

theorem derivative_constant (n : Nat) (h : n > 0 ∧ n ≤ 100) : 
  derivative s!"${n}x" = s!"${n}" := sorry

theorem derivative_power_rule (n : Nat) (h : n > 0 ∧ n ≤ 10) :
  derivative s!"x^${n}" = 
    if n > 2 then s!"${n}x^${n-1}"
    else if n = 2 then s!"${n}x"
    else "1" := sorry

theorem derivative_linearity (s : String) :
  ∃ result : String, derivative s = result ∧ result.length > 0 := sorry

/-
info: '4'
-/
-- #guard_msgs in
-- #eval derivative "4x+1"

/-
info: '-2x+3'
-/
-- #guard_msgs in
-- #eval derivative "-x^2+3x+4"

/-
info: '2x+2'
-/
-- #guard_msgs in
-- #eval derivative "x^2+2x+1"

-- Apps difficulty: introductory
-- Assurance level: unguarded