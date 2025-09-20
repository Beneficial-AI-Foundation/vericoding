-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Point := Int × Int

def solve_checkpoints (n : Int) (c : Int) (points : List Point) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_checkpoints_output_type {n c : Int} {points : List Point} :
  (solve_checkpoints n c points).1 ≥ 0 ∧ (solve_checkpoints n c points).2 ≥ 0 := sorry

theorem solve_checkpoints_groups_bounded {n c : Int} {points : List Point} 
  (hn : n > 0) (hc : c > 0) :
  (solve_checkpoints n c points).1 ≤ points.length := sorry

theorem solve_checkpoints_moves_nonneg {n c : Int} {points : List Point}
  (hn : n > 0) (hc : c > 0) :
  (solve_checkpoints n c points).2 ≥ 0 := sorry

theorem solve_checkpoints_identical_points {n c x y : Int} {count : Nat}
  (hn : n > 0) (hc : c > 0) (hcount : count > 0) :
  let points := List.replicate count (x, y)
  solve_checkpoints n c points = (1, 0) := sorry

theorem solve_checkpoints_empty {n c : Int}
  (hn : n > 0) (hc : c > 0) :
  solve_checkpoints n c [] = (0, 0) := sorry
-- </vc-theorems>