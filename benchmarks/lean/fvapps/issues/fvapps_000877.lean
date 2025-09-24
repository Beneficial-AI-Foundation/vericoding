-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_binary_nim (n : Nat) (starting_player : Player) (stacks : List String) : Player :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_binary_nim_returns_valid_player
  (n : Nat)
  (starting_player : Player)
  (stacks : List String)
  : (solve_binary_nim n starting_player stacks = Player.Dee) ∨
    (solve_binary_nim n starting_player stacks = Player.Dum) := sorry

theorem solve_binary_nim_deterministic
  (n : Nat)
  (starting_player : Player)
  (stacks : List String)
  : solve_binary_nim n starting_player stacks = 
    solve_binary_nim n starting_player stacks := sorry

theorem solve_binary_nim_equal_zeros_ones_starting_player_loses
  (n : Nat)
  (starting_player : Player)
  (stacks : List String)
  (h : (stacks.foldl (fun acc s => acc + (s.toList.filter (· = '0')).length) 0) =
       (stacks.foldl (fun acc s => acc + (s.toList.filter (· = '1')).length) 0))
  : solve_binary_nim n starting_player stacks ≠ starting_player := sorry

/-
info: 'Dum'
-/
-- #guard_msgs in
-- #eval solve_binary_nim 2 "Dee" ["101", "010"]

/-
info: 'Dee'
-/
-- #guard_msgs in
-- #eval solve_binary_nim 2 "Dum" ["101", "010"]
-- </vc-theorems>