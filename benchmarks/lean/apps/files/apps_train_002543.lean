-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_needed_guards (islands : List Bool) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem guard_count_nonnegative (islands : List Bool) : 
  find_needed_guards islands ≥ 0 :=
sorry

theorem guard_count_bounded_by_unguarded (islands : List Bool) :
  let unguarded := (islands.filter (fun x => !x)).length
  find_needed_guards islands ≤ (unguarded + 1) / 2 :=
sorry

theorem single_island_needs_no_guards (islands : List Bool) :
  islands.length = 1 → find_needed_guards islands = 0 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_needed_guards [True, True, False, True, False]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_needed_guards [False, False, True, False, False]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_needed_guards [False, False, False, False, False]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible