-- <vc-helpers>
-- </vc-helpers>

def solve_time_game (n : Nat) (d : Nat) (a : List Nat) (coords : List (Int × Int)) : Nat :=
  sorry

theorem solve_time_game_basic {n d : Nat} {a : List Nat} {coords : List (Int × Int)}
  (h1 : n ≥ 2)
  (h2 : d > 0) 
  (h3 : n ≤ 3)
  (h4 : d ≤ 100)
  (h5 : a = List.replicate n 0)
  (h6 : coords = List.map (fun i => (0, Int.ofNat i)) (List.range n)) :
  let result := solve_time_game n d a coords
  result ≥ 0 ∧ result = (n - 1) * d := sorry

/-
info: 2000
-/
-- #guard_msgs in
-- #eval solve_time_game 3 1000 [0, 1000, 0] [(0, 0), (0, 1), (0, 3)]

/-
info: 1000
-/
-- #guard_msgs in
-- #eval solve_time_game 3 1000 [0, 1000, 0] [(1, 0), (1, 1), (1, 2)]

/-
info: 169099
-/
-- #guard_msgs in
-- #eval solve_time_game 5 1421 [0, 896, 448, 727, 0] [(-19, -40), (-87, 40), (69, 51), (-55, 61), (-7, 67)]

-- Apps difficulty: competition
-- Assurance level: unguarded