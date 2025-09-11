-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_jumps (arr : List Int) : Int := sorry

theorem min_jumps_single_element (x : Int) :
  min_jumps [x] = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_jumps_non_negative (arr : List Int) : 
  min_jumps arr ≥ -1 := sorry

theorem min_jumps_bound_by_length (arr : List Int) :
  min_jumps arr ≤ arr.length := sorry

theorem min_jumps_all_same {arr : List Int} (h : arr.length > 1) 
  (h2 : ∀ x ∈ arr, x = arr.head!) :
  min_jumps arr = 1 := sorry

theorem min_jumps_same_ends {arr : List Int} (h : arr.length > 1)
  (h2 : arr.head! = arr.getLast!) :
  min_jumps arr = 1 := sorry

theorem min_jumps_identical_elements (n : Nat) (h : n ≥ 2) :
  min_jumps (List.replicate n 1) = 1 := sorry

theorem min_jumps_adjacent_reachable {arr : List Int} (h : arr.length ≥ 2)
  (h2 : ∀ i, i < arr.length - 1 → arr[i]! = arr[i+1]!) :
  min_jumps arr ≤ arr.length - 1 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_jumps [100, -23, -23, 404, 100, 23, 23, 23, 3, 404]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_jumps [7]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_jumps [7, 6, 9, 6, 9, 6, 9, 7]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded