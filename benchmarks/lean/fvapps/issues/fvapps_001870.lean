-- <vc-preamble>
def removeNthFromEnd (head : Node) (n : Nat) : Option Node :=
  sorry

def create_linked_list (arr : List Int) : Option Node :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def linked_list_to_array (head : Option Node) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem remove_nth_maintains_order {arr : List Int} {n : Nat} 
  (h1 : 0 < n) (h2 : n ≤ arr.length) :
  let head := create_linked_list arr
  let result := removeNthFromEnd (Option.get! head) n
  let result_arr := linked_list_to_array result
  (result_arr.length = arr.length - 1) ∧ 
  (result_arr = (arr.take (arr.length - n)) ++ (arr.drop (arr.length - n + 1))) :=
sorry

theorem remove_first_element {arr : List Int}
  (h : arr.length > 0) :
  let head := create_linked_list arr
  let result := removeNthFromEnd (Option.get! head) arr.length
  linked_list_to_array result = arr.tail :=
sorry

theorem remove_last_element {arr : List Int}
  (h : arr.length > 0) :
  let head := create_linked_list arr
  let result := removeNthFromEnd (Option.get! head) 1
  linked_list_to_array result = arr.dropLast :=
sorry

/-
info: [1, 2, 3, 5]
-/
-- #guard_msgs in
-- #eval linked_list_to_array removeNthFromEnd(head1, 2)

/-
info: []
-/
-- #guard_msgs in
-- #eval linked_list_to_array removeNthFromEnd(head2, 1)

/-
info: [1]
-/
-- #guard_msgs in
-- #eval linked_list_to_array removeNthFromEnd(head3, 1)
-- </vc-theorems>