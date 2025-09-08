/-
We are given head, the head node of a linked list containing unique integer values.
We are also given the list G, a subset of the values in the linked list.
Return the number of connected components in G, where two values are connected if they appear consecutively in the linked list.
Example 1:
Input: 
head: 0->1->2->3
G = [0, 1, 3]
Output: 2
Explanation: 
0 and 1 are connected, so [0, 1] and [3] are the two connected components.

Example 2:
Input: 
head: 0->1->2->3->4
G = [0, 3, 1, 4]
Output: 2
Explanation: 
0 and 1 are connected, 3 and 4 are connected, so [0, 1] and [3, 4] are the two connected components.

Note: 

If N is the length of the linked list given by head, 1 <= N <= 10000.
The value of each node in the linked list will be in the range [0, N - 1].
1 <= G.length <= 10000.
G is a subset of all values in the linked list.
-/

-- <vc-helpers>
-- </vc-helpers>

def create_linked_list (values : List Int) : ListNode := sorry

def numComponents (head : ListNode) (values : List Int) : Nat := sorry

theorem full_list_is_one_component (values : List Int) (h : values ≠ []) :
  numComponents (create_linked_list values) values = 1 := sorry

theorem disjoint_lists_return_zero {values g : List Int} (h1 : values ≠ [])
  (h2 : ∀ x, x ∈ values → x ∉ g) :
  numComponents (create_linked_list values) g = 0 := sorry

theorem single_value_gives_one_component {values : List Int} (h1 : values ≠ [])
  (h2 : ∀ x y, x ∈ values → y ∈ values → x ≠ y) :  
  numComponents (create_linked_list values) [values.head!] = 1 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval numComponents create_linked_list([0, 1, 2, 3]) [0, 1, 3]

/-
info: 2
-/
-- #guard_msgs in
-- #eval numComponents create_linked_list([0, 1, 2, 3, 4]) [0, 3, 1, 4]

/-
info: 2
-/
-- #guard_msgs in
-- #eval numComponents create_linked_list([0, 1, 2]) [0, 2]

-- Apps difficulty: interview
-- Assurance level: unguarded