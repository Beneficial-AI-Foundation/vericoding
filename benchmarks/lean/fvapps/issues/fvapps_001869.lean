-- <vc-preamble>
def arrayToLinkedList : List Int → Option ListNode := sorry
def linkedListToArray : Option ListNode → List Int := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseBetween : Option ListNode → Nat → Nat → Option ListNode := sorry

theorem reverse_single_element_unchanged 
    {arr : List Int} {i : Nat} 
    (h1 : arr ≠ []) 
    (h2 : i ≥ 1) 
    (h3 : i ≤ arr.length) :
    linkedListToArray (reverseBetween (arrayToLinkedList arr) i i) = arr := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_entire_list
    {arr : List Int}
    (h : arr ≠ []) :
    linkedListToArray (reverseBetween (arrayToLinkedList arr) 1 arr.length) = arr.reverse := sorry 

theorem reverse_between_properties
    {arr : List Int} {m n : Nat}
    (h1 : arr ≠ [])
    (h2 : m ≥ 1)
    (h3 : n ≥ 1)
    (h4 : m ≤ arr.length)
    (h5 : n ≤ arr.length)
    (h6 : m ≤ n) :
    let result := linkedListToArray (reverseBetween (arrayToLinkedList arr) m n)
    (result.length = arr.length) ∧
    (result.take (m-1) = arr.take (m-1)) ∧
    (result.drop n = arr.drop n) ∧
    ((result.drop (m-1)).take (n-m+1)) = ((arr.drop (m-1)).take (n-m+1)).reverse := sorry

theorem empty_list : 
    reverseBetween none 1 1 = none := sorry

/-
info: [1, 4, 3, 2, 5]
-/
-- #guard_msgs in
-- #eval linkedListToArray reverseBetween(test1, 2, 4)

/-
info: [1]
-/
-- #guard_msgs in
-- #eval linkedListToArray reverseBetween(test2, 1, 1)

/-
info: [3, 2, 1]
-/
-- #guard_msgs in
-- #eval linkedListToArray reverseBetween(test3, 1, 3)
-- </vc-theorems>