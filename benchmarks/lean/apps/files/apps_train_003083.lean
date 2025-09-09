-- <vc-helpers>
-- </vc-helpers>

def cheapest_quote (n : Nat) : Float := sorry

/- Ensures cheapest_quote returns a non-negative float -/

theorem cheapest_quote_non_negative (n : Nat) :
  let result := cheapest_quote n
  result ≥ 0 := sorry

/- Ensures cheapest_quote is strictly monotonically increasing -/

theorem cheapest_quote_monotonic (n : Nat) : n > 0 →
  cheapest_quote n > cheapest_quote (n-1) := sorry

/-
info: 3.95
-/
-- #guard_msgs in
-- #eval cheapest_quote 41

/-
info: 2.52
-/
-- #guard_msgs in
-- #eval cheapest_quote 26

/-
info: 48.06
-/
-- #guard_msgs in
-- #eval cheapest_quote 499

-- Apps difficulty: introductory
-- Assurance level: unguarded