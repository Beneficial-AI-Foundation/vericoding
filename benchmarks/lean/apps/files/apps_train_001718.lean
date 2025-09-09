def choose_move (gameState : List Nat) : Nat × Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def nimSum (xs : List Nat) : Nat :=
  sorry

theorem choose_move_valid {gameState : List Nat} (h : gameState ≠ []) :
  let move := choose_move gameState
  let (pileIdx, straws) := move
  pileIdx < gameState.length ∧ 
  0 < straws ∧
  straws ≤ gameState[pileIdx]! :=
sorry

theorem winning_move_reduces_nim_sum {gameState : List Nat} (h : gameState ≠ []) :
  let move := choose_move gameState
  let (pileIdx, straws) := move
  let initialNimSum := nimSum gameState
  let newState := gameState.set pileIdx (gameState[pileIdx]! - straws)
  let newNimSum := nimSum newState
  initialNimSum > 0 → newNimSum < initialNimSum :=
sorry

theorem modify_nonempty_pile {gameState : List Nat} (h : gameState ≠ []) :
  let move := choose_move gameState
  let (pileIdx, straws) := move
  gameState[pileIdx]! > 0 :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded