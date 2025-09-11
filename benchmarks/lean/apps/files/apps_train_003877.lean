-- <vc-preamble>
def Position := String
def Command := String

def tetris (commands : List Command) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumHeights (commands : List Command) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tetris_output_natural (commands : List Command) : 
  tetris commands ≥ 0 :=
  sorry

theorem tetris_height_limit (commands : List Command) (h : commands ≠ []) :
  tetris commands < 30 :=
  sorry

theorem tetris_cleared_lines (commands : List Command) (h : commands ≠ []) :
  tetris commands ≤ sumHeights commands :=
  sorry

theorem tetris_idempotent_empty_moves (commands : List Command) (h : commands ≠ []) :
  let emptyMoves : List Command := ["1L0", "1R0"]
  tetris commands = tetris (commands ++ emptyMoves) :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval tetris ["1R4", "2L3", "3L2", "4L1", "1L0", "2R1", "3R2", "4R3", "1L4"]

/-
info: 0
-/
-- #guard_msgs in
-- #eval tetris ["1L2", "4R2", "3L3", "3L1", "1L4", "1R4"]

/-
info: 3
-/
-- #guard_msgs in
-- #eval tetris ["4R4", "4L3", "4L2", "4L1", "4L0", "4R1", "4R2", "4R3", "3L4"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded