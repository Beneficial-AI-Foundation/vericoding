/-
This kata is about singly 
linked list.  A linked list is an ordered set of data elements, each containing a link to its successor (and sometimes its predecessor, known as a double linked list).  You are you to implement an algorithm to find the kth to last element.

For example given a linked list of:
a -> b -> c -> d

if k is the number one then d should be returned
if k is the number two then c should be returned
if k is the number three then b should be returned
if k is the number four then a should be returned
if k exceeds the size of the list then None returned

Special Note --> Node classes contain two fields; data and next.
And to access the head of the list, use head. e.g. linked_list.head
-/

-- <vc-helpers>
-- </vc-helpers>

def search_k_from_end {α : Type} (l : LinkedList α) (k : Nat) : Option α :=
  sorry

theorem search_k_from_end_empty (α : Type) (k : Nat) :
  k > 0 → search_k_from_end (@LinkedList.mk α []) k = none := 
  sorry

theorem search_k_from_end_too_large (α : Type) (l : LinkedList α) (k len : Nat) (vals : List α) :
  k > len → l.vals = vals → len = vals.length → search_k_from_end l k = none :=
  sorry

theorem search_k_from_end_valid (α : Type) (l : LinkedList α) (k len : Nat) (vals : List α) :
  k ≤ len → k > 0 → l.vals = vals → len = vals.length → 
  ∃ (x : α), x ∈ vals ∧ search_k_from_end l k = some x :=
  sorry

theorem search_k_from_end_single_element (α : Type) (x : α) :
  search_k_from_end (@LinkedList.mk α [x]) 1 = some x :=
  sorry

theorem search_k_from_end_single_element_too_large (α : Type) (x : α) :
  search_k_from_end (@LinkedList.mk α [x]) 2 = none :=
  sorry

/-
info: 'd'
-/
-- #guard_msgs in
-- #eval search_k_from_end LinkedList() 1

/-
info: 'c'
-/
-- #guard_msgs in
-- #eval search_k_from_end ll 2

/-
info: 'b'
-/
-- #guard_msgs in
-- #eval search_k_from_end ll 3

/-
info: 'a'
-/
-- #guard_msgs in
-- #eval search_k_from_end ll 4

/-
info: None
-/
-- #guard_msgs in
-- #eval search_k_from_end ll 5

/-
info: None
-/
-- #guard_msgs in
-- #eval search_k_from_end LinkedList() 1

/-
info: 'x'
-/
-- #guard_msgs in
-- #eval search_k_from_end LinkedList() 1

/-
info: None
-/
-- #guard_msgs in
-- #eval search_k_from_end ll3 2

-- Apps difficulty: introductory
-- Assurance level: unguarded