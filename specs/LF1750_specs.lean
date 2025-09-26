-- <vc-preamble>
def reorder_list : ListNode → ListNode :=
  sorry

def array_to_list : List Int → ListNode :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_to_array : ListNode → List Int := 
  sorry

-- Main properties
-- </vc-definitions>

-- <vc-theorems>
theorem reorder_list_preserves_length {l : List Int} :
  let list := array_to_list l
  List.length (list_to_array (reorder_list list)) = List.length l :=
  sorry

theorem reorder_list_preserves_first {l : List Int} (h : l ≠ []) :
  let list := array_to_list l
  let reordered_array := list_to_array (reorder_list list)
  List.head! reordered_array = List.head! l :=
  sorry

theorem reorder_list_alternates {l : List Int} (h : List.length l > 1) :
  let list := array_to_list l
  let reordered_array := list_to_array (reorder_list list)
  let n := List.length l
  let first_half := List.take ((n + 1)/2) l
  let second_half := List.reverse (List.drop ((n + 1)/2) l)
  ∀ i, i < List.length second_half →
    List.get! reordered_array (2*i) = List.get! first_half i ∧
    List.get! reordered_array (2*i + 1) = List.get! second_half i :=
  sorry

theorem reorder_list_empty :
  reorder_list ListNode.nil = ListNode.nil :=
  sorry

theorem reorder_list_odd_length_ends_first_half {l : List Int} 
  (h : List.length l % 2 = 1) :
  let list := array_to_list l
  let reordered_array := list_to_array (reorder_list list)
  let n := List.length l
  let first_half := List.take ((n + 1)/2) l
  List.get! reordered_array (List.length l - 1) = 
    List.get! first_half (List.length first_half - 1) :=
  sorry

/-
info: [1, 4, 2, 3]
-/
-- #guard_msgs in
-- #eval list_to_array reorder_list(head1)

/-
info: [1, 5, 2, 4, 3]
-/
-- #guard_msgs in
-- #eval list_to_array reorder_list(head2)
-- </vc-theorems>