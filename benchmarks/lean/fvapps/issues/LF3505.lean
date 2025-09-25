-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def median (lst: List Int) : Float := sorry

namespace MedianTheorems
-- </vc-definitions>

-- <vc-theorems>
theorem median_nonempty_returns_number (lst: List Int) (h: lst ≠ []) : 
  let result := median lst
  ∃ n: Float, result = n := sorry

theorem median_empty_is_nan : 
  let result := median []
  Float.isNaN result := sorry

theorem median_same_elements {lst: List Int} (h: lst ≠ []) 
  (head: lst.head? = some (lst.head!)) :
  (∀ x ∈ lst, x = lst.head!) → 
  median lst = Float.ofInt lst.head! := sorry

theorem median_sort_invariant {lst: List Int} (h: lst ≠ []) :
  median lst = median (List.mergeSort (· ≤ ·) lst) := sorry

end MedianTheorems

/-
info: 2.5
-/
-- #guard_msgs in
-- #eval median [1, 2, 3, 4]

/-
info: 3
-/
-- #guard_msgs in
-- #eval median [3, 4, 1, 2, 5]

/-
info: 1
-/
-- #guard_msgs in
-- #eval median [1]
-- </vc-theorems>