-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def removeNthElement (arr : List α) (n : Nat) : List α :=
  sorry

/- Length decreases by 1 after removing element -/
-- </vc-definitions>

-- <vc-theorems>
theorem removeNthElement_length_decreases {α : Type u} (arr : List α) (n : Nat) 
    (h : n < arr.length) :
    (removeNthElement α arr n).length = arr.length - 1 :=
  sorry

/- Elements before n stay unchanged -/

theorem removeNthElement_prefix_unchanged {α : Type u} (arr : List α) (n : Nat)
    (h : n < arr.length) :
    (removeNthElement α arr n).take n = arr.take n :=
  sorry

/- Elements after n are unchanged but shifted -/

theorem removeNthElement_suffix_shifted {α : Type u} (arr : List α) (n : Nat)
    (h : n < arr.length) :
    (removeNthElement α arr n).drop n = arr.drop (n + 1) :=
  sorry

/- Removing first element gives tail -/

theorem removeNthElement_zero_is_tail {α : Type u} (arr : List α)
    (h : arr ≠ []) :
    removeNthElement α arr 0 = arr.tail :=
  sorry

/-
info: [7, 6, 9]
-/
-- #guard_msgs in
-- #eval remove_nth_element [9, 7, 6, 9] 0

/-
info: [1, 3]
-/
-- #guard_msgs in
-- #eval remove_nth_element [1, 2, 3] 1

/-
info: ['a', 'b', 'c']
-/
-- #guard_msgs in
-- #eval remove_nth_element ["a", "b", "c", "d"] 3
-- </vc-theorems>