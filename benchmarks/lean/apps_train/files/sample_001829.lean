/-
Given a linked list, reverse the nodes of a linked list k at a time and return its modified list.

k is a positive integer and is less than or equal to the length of the linked list. If the number of nodes is not a multiple of k then left-out nodes in the end should remain as it is.

Example:

Given this linked list: 1->2->3->4->5

For k = 2, you should return: 2->1->4->3->5

For k = 3, you should return: 3->2->1->4->5

Note:

       Only constant extra memory is allowed.
       You may not alter the values in the list's nodes, only nodes itself may be changed.
-/

def reverseKGroup (head: ListNode) (k: Nat) : ListNode :=
  sorry

def list_to_array (head: ListNode) : List Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def array_to_list (arr: List Int) : ListNode :=
  sorry

theorem reverseKGroup_length_preserved 
  (lst: List Int) (k: Nat) (h: k > 0): 
  List.length (list_to_array (reverseKGroup (array_to_list lst) k)) = List.length lst :=
  sorry

theorem reverseKGroup_elements_preserved
  (lst: List Int) (k: Nat) (h: k > 0):
  ∃ perm : List Int, 
    list_to_array (reverseKGroup (array_to_list lst) k) = perm ∧ 
    List.length perm = List.length lst ∧
    ∀ x, List.count x perm = List.count x lst :=
  sorry

theorem reverseKGroup_k_equals_one_is_identity
  (lst: List Int):
  list_to_array (reverseKGroup (array_to_list lst) 1) = lst :=
  sorry

theorem reverseKGroup_subsequence_reversal
  (lst: List Int) (k: Nat) (h: k > 0) (i: Nat) 
  (h₁: i + k ≤ List.length lst):
  let result := list_to_array (reverseKGroup (array_to_list lst) k)
  let sublist := List.take k (List.drop i lst)
  List.take k (List.drop i result) = List.reverse sublist :=
  sorry

/-
info: [2, 1, 4, 3, 5]
-/
-- #guard_msgs in
-- #eval list_to_array reverseKGroup(head1, 2)

/-
info: [3, 2, 1, 4, 5]
-/
-- #guard_msgs in
-- #eval list_to_array reverseKGroup(head2, 3)

/-
info: [1, 2, 3]
-/
-- #guard_msgs in
-- #eval list_to_array reverseKGroup(head3, 1)

-- Apps difficulty: interview
-- Assurance level: unguarded