-- <vc-preamble>
def arrayToLinkedList : List Int → ListNode := sorry
def linkedListToArray : ListNode → List Int := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sortList : ListNode → ListNode := sorry

def isSorted : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => x ≤ y && isSorted (y :: rest)
-- </vc-definitions>

-- <vc-theorems>
theorem sort_maintains_elements (arr : List Int) :
  ∃ perm : List Int, linkedListToArray (sortList (arrayToLinkedList arr)) = perm := sorry

theorem sorted_result (arr : List Int) :
  let result := linkedListToArray (sortList (arrayToLinkedList arr))
  isSorted result := sorry

theorem length_preserved (arr : List Int) :
  (linkedListToArray (sortList (arrayToLinkedList arr))).length = arr.length := sorry

theorem max_min_preserved (arr : List Int) (h : arr ≠ []) :
  let result := linkedListToArray (sortList (arrayToLinkedList arr))
  let min := result[0]!
  let max := result[result.length - 1]!
  (∀ x ∈ arr, min ≤ x) ∧ (∀ x ∈ arr, x ≤ max) := sorry

theorem empty_list :
  sortList ListNode.nil = ListNode.nil := sorry

/-
info: [1, 2, 3, 4]
-/
-- #guard_msgs in
-- #eval linkedListToArray sortList(head1)

/-
info: [-1, 0, 3, 4, 5]
-/
-- #guard_msgs in
-- #eval linkedListToArray sortList(head2)
-- </vc-theorems>