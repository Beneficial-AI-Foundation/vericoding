-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minimum_moves (grid : Array (Array Nat)) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_moves_empty_grid_reaches {n : Nat} (h : n ≥ 3) :
  let grid := Array.mk (List.replicate n (Array.mk (List.replicate n (0:Nat))))
  minimum_moves grid > 0 :=
sorry

theorem min_moves_blocked_grid_unreachable {n : Nat} (h : n ≥ 3) :
  let blockedGrid := Array.mk (List.replicate n (Array.mk (List.replicate n (1:Nat))))
  let grid := blockedGrid.set! 0 (blockedGrid[0]!.set! 0 0) |>.set! 0 (blockedGrid[0]!.set! 1 0)
  minimum_moves grid = -1 :=
sorry

theorem min_moves_minimal_grid_reaches :
  let grid := Array.mk [Array.mk [(0:Nat),(0:Nat),(0:Nat)], Array.mk [(0:Nat),(0:Nat),(0:Nat)], Array.mk [(0:Nat),(0:Nat),(0:Nat)]]
  minimum_moves grid > 0 :=
sorry
-- </vc-theorems>