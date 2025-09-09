-- <vc-helpers>
-- </vc-helpers>

def solve_digit_coloring (n : Nat) (digits : String) : String := sorry

theorem output_format (n : Nat) (digits : String) :
  let result := solve_digit_coloring n digits
  result = "-" ∨
  (result.length = n ∧ 
   result.data.all (fun c => c = '1' ∨ c = '2')) := sorry

theorem output_constraints (n : Nat) (digits : String) :
  let result := solve_digit_coloring n digits
  result ≠ "-" →
  let nums := digits.data.map (fun c => c.toNat - '0'.toNat)
  let colors := result.data.map (fun c => c.toNat - '0'.toNat)
  ∀ i j, i < j → j < nums.length →
  colors[i]! = colors[j]! → nums[i]! ≤ nums[j]! := sorry

/-
info: '121212211211'
-/
-- #guard_msgs in
-- #eval solve_digit_coloring 12 "040425524644"

/-
info: '1'
-/
-- #guard_msgs in
-- #eval solve_digit_coloring 1 "0"

/-
info: '-'
-/
-- #guard_msgs in
-- #eval solve_digit_coloring 3 "987"

-- Apps difficulty: competition
-- Assurance level: unguarded