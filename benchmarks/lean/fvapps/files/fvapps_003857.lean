-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_candy_position (n r c candy : Nat) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem candy_position_returns_three_elements {n r c candy : Nat} :
  let result := get_candy_position n r c candy
  result.size = 3 := by sorry

theorem candy_beyond_n_returns_negative_ones {n r c candy : Nat} :
  candy > n →
  get_candy_position n r c candy = #[-1, -1, -1] := by sorry

theorem position_coordinates_within_bounds {n r c candy : Nat} :
  candy ≤ n →
  let result := get_candy_position n r c candy
  let level := result[0]!
  let row := result[1]!
  let col := result[2]!
  (level ≠ -1 →
   (1 ≤ level ∧ level ≤ (n / (r * c)) + 1) ∧
   (0 ≤ row ∧ row < r) ∧
   (0 ≤ col ∧ col < c)) := by sorry

theorem first_candy_at_bottom_right {r c : Nat} (hr : r > 0) (hc : c > 0) :
  get_candy_position 1 r c 1 = #[1, Int.ofNat (r-1), Int.ofNat (c-1)] := by sorry

theorem last_candy_level_one_if_fits {n r c : Nat} (hr : r > 0) (hc : c > 0) :
  n ≤ r * c →
  (get_candy_position n r c n)[0]! = 1 := by sorry
-- </vc-theorems>