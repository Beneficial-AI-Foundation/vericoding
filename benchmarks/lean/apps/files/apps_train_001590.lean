-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def spinning_rings (inner_max outer_max : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem spinning_rings_positive (inner_max outer_max : Nat) 
  (h1 : inner_max > 0) (h2 : outer_max > 0) (h3 : inner_max ≤ 10) (h4 : outer_max ≤ 10) :
  spinning_rings inner_max outer_max > 0 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval spinning_rings 5 5

/-
info: 13
-/
-- #guard_msgs in
-- #eval spinning_rings 2 10

/-
info: 23951671
-/
-- #guard_msgs in
-- #eval spinning_rings 16777216 14348907
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible