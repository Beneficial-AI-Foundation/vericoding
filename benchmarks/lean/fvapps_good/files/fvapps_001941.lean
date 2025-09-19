-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_time_game (n : Nat) (d : Nat) (a : List Nat) (coords : List (Int × Int)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_time_game_basic {n d : Nat} {a : List Nat} {coords : List (Int × Int)}
  (h1 : n ≥ 2)
  (h2 : d > 0) 
  (h3 : n ≤ 3)
  (h4 : d ≤ 100)
  (h5 : a = List.replicate n 0)
  (h6 : coords = List.map (fun i => (0, Int.ofNat i)) (List.range n)) :
  let result := solve_time_game n d a coords
  result ≥ 0 ∧ result = (n - 1) * d := sorry
-- </vc-theorems>