-- <vc-preamble>
def Position := String
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Command := String

def tetris (commands : List Command) : Nat :=
  sorry

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
-- </vc-theorems>