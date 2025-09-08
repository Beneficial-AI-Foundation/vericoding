/-
Your task is to construct a building which will be a pile of n cubes.
The cube at the bottom will have a volume of n^3, the cube above 
will have  volume of (n-1)^3 and so on until the top which will have a volume of 1^3.

You are given the total volume m of the building.
Being given m can you find the number n of cubes you will have to build?

The parameter of the function findNb `(find_nb, find-nb, findNb)` will be an integer m
and you have to return the integer n such as
n^3 + (n-1)^3 + ... + 1^3 = m
if such a n exists or -1 if there is no such n.

## Examples:
```
findNb(1071225) --> 45
findNb(91716553919377) --> -1
```
-/

-- <vc-helpers>
-- </vc-helpers>

def find_nb (n : Int) : Int := sorry

def sum_cubes (n : Nat) : Nat := sorry

/- For small perfect cubes (n ≤ 10), find_nb correctly returns n when given sum of first n cubes -/

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

-- Apps difficulty: introductory
-- Assurance level: guarded