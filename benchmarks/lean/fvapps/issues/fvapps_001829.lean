-- <vc-preamble>
def reverseKGroup (head: ListNode) (k: Nat) : ListNode :=
  sorry

def list_to_array (head: ListNode) : List Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def array_to_list (arr: List Int) : ListNode :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>