-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_zombie_moves (h u d : Nat) : Int := sorry

theorem find_min_zombie_moves_non_negative 
  (h u d : Nat) (h_pos : h > 0) (u_pos : u > 0) (d_pos : d > 0) :
  let result := find_min_zombie_moves h u d
  result ≠ -1 → result ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_zombie_moves_height_reached 
  (h u d : Nat) (h_pos : h > 0) (u_pos : u > 0) (d_pos : d > 0) :
  let result := find_min_zombie_moves h u d
  result ≠ -1 → result * u - (result - result) * d ≥ h := sorry

theorem find_min_zombie_moves_no_solution
  (h u d : Nat) (h_pos : h > 0) (u_pos : u > 0) (d_pos : d > 0) :
  let result := find_min_zombie_moves h u d
  result = -1 → h % Nat.gcd u d ≠ 0 := sorry
-- </vc-theorems>