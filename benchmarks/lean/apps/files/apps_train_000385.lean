-- <vc-helpers>
-- </vc-helpers>

def oddEvenJumps (arr : List Int) : Nat :=
  sorry

theorem oddEvenJumps_output_range (arr : List Int) (h : arr ≠ []) : 
  let result := oddEvenJumps arr
  1 ≤ result ∧ result ≤ arr.length := sorry

theorem oddEvenJumps_single_element (x : Int) :
  oddEvenJumps [x] = 1 := sorry

theorem oddEvenJumps_decreasing {arr : List Int} (h₁ : arr ≠ [])
  (h₂ : ∀ (i j : Fin arr.length), i.val < j.val → arr[i] > arr[j]) :
  oddEvenJumps arr ≥ 1 := sorry

theorem oddEvenJumps_all_equal (x : Int) (n : Nat) (h : n > 0) :
  oddEvenJumps (List.replicate n x) = n := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval oddEvenJumps [10, 13, 12, 14, 15]

/-
info: 3
-/
-- #guard_msgs in
-- #eval oddEvenJumps [2, 3, 1, 1, 4]

/-
info: 3
-/
-- #guard_msgs in
-- #eval oddEvenJumps [5, 1, 3, 4, 2]

-- Apps difficulty: interview
-- Assurance level: unguarded