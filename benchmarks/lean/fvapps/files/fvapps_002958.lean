-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def avoid_obstacles (obstacles : List Nat) : Nat := sorry

theorem avoid_obstacles_jumps_over_all (obstacles : List Nat)
  (h1 : ∀ x ∈ obstacles, 1 ≤ x ∧ x ≤ 1000)
  (h2 : obstacles.length ≥ 1 ∧ obstacles.length ≤ 100) :
  let jump := avoid_obstacles obstacles
  2 ≤ jump ∧ ∀ pos ∈ obstacles, pos % jump ≠ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem avoid_obstacles_monotonic_with_subset (obstacles : List Nat)
  (h1 : ∀ x ∈ obstacles, 1 ≤ x ∧ x ≤ 50)
  (h2 : obstacles.length ≥ 2 ∧ obstacles.length ≤ 10) :
  avoid_obstacles obstacles ≥ avoid_obstacles (obstacles.take (obstacles.length / 2)) := sorry
-- </vc-theorems>