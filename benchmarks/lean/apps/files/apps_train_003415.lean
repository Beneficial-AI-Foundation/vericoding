-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_nb (n : Int) : Int := sorry

def sum_cubes (n : Nat) : Nat := sorry

/- For small perfect cubes (n ≤ 10), find_nb correctly returns n when given sum of first n cubes -/
-- </vc-definitions>

-- <vc-theorems>
theorem find_nb_small_perfect_cubes (n : Nat) (h : n ≤ 10) :
  find_nb (sum_cubes n) = n := sorry

/- For any volume that isn't sum of consecutive cubes, find_nb returns -1 -/

theorem find_nb_invalid_volumes {n : Int} (h : n > 0) :
  find_nb n = -1 ∨ sum_cubes (find_nb n).toNat = n := sorry

/- find_nb returns -1 for non-positive inputs -/

theorem find_nb_nonpositive {n : Int} (h : n ≤ 0) :
  find_nb n = -1 := sorry

/- For valid inputs, find_nb returns a positive number that produces the input volume -/

theorem find_nb_valid_result (n : Nat) :
  let volume := sum_cubes n
  let result := find_nb volume
  result > 0 ∧ sum_cubes result.toNat = volume := sorry

/- Any positive result from find_nb produces the claimed volume -/

theorem find_nb_produces_volume {n : Int} (h : find_nb n > 0) :
  sum_cubes (find_nb n).toNat = n := sorry

/-
info: 45
-/
-- #guard_msgs in
-- #eval find_nb 1071225

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_nb 91716553919377

/-
info: 2022
-/
-- #guard_msgs in
-- #eval find_nb 4183059834009
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded