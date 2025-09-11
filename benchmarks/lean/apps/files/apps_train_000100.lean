-- <vc-preamble>
def abs (x : Int) : Int :=
  if x ≥ 0 then x else -x

def maximum (x y : Int) : Int :=
  if x ≥ y then x else y
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def time_without_coverage (a b c r : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem time_without_coverage_nonneg 
  (a b c : Int) (r : Nat) :
  time_without_coverage a b c r ≥ 0 := 
  sorry

theorem time_without_coverage_symmetric
  (a b c : Int) (r : Nat) :
  time_without_coverage a b c r = time_without_coverage b a c r :=
  sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval time_without_coverage 1 10 7 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval time_without_coverage 3 3 3 0

/-
info: 4
-/
-- #guard_msgs in
-- #eval time_without_coverage 8 2 10 4
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible