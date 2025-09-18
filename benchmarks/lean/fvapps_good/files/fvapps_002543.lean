-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>