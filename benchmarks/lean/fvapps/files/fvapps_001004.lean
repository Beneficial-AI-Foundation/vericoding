-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_teleport_game (R C N Sx Sy : Nat) (tel_pairs : List (Nat × Nat)) (board : List (List Int)) : Int := sorry

theorem solve_teleport_game_includes_start_value (R C N Sx Sy : Nat) (tel_pairs : List (Nat × Nat)) (board : List (List Int)) 
  (h1 : Sx < board.length) (h2 : Sy < (board[Sx].length)) :
  solve_teleport_game R C N Sx Sy tel_pairs board ≥ board[Sx][Sy] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_teleport_game_empty_teleports (R C : Nat) (h1 : R > 0) (h2 : C > 0) :
  solve_teleport_game R C 0 0 0 [] (List.replicate R (List.replicate C 1)) = 1 := sorry

theorem solve_teleport_game_single_cell (val : Int) :
  solve_teleport_game 1 1 0 0 0 [] [[val]] = val := sorry

theorem solve_teleport_game_symmetric_teleport (val : Int) :
  let board := [[val, val], [val, val]]
  let tel_pairs := [(1, 1)]
  let results := [
    solve_teleport_game 2 2 1 0 0 tel_pairs board,
    solve_teleport_game 2 2 1 0 1 tel_pairs board,
    solve_teleport_game 2 2 1 1 0 tel_pairs board,
    solve_teleport_game 2 2 1 1 1 tel_pairs board
  ]
  ∀ x y, x ∈ results → y ∈ results → x = y := sorry
-- </vc-theorems>