Write a function that takes a single array as an argument (containing multiple strings and/or positive numbers and/or arrays), and returns one of four possible string values, depending on the ordering of the lengths of the elements in the input array:

Your function should return...

- “Increasing” - if the lengths of the elements increase from left to right (although it is possible that some neighbouring elements may also be equal in length)
- “Decreasing” - if the lengths of the elements decrease from left to right (although it is possible that some neighbouring elements may also be equal in length)
- “Unsorted” - if the lengths of the elements fluctuate from left to right
- “Constant” - if all element's lengths are the same.

Numbers and Strings should be evaluated based on the number of characters or digits used to write them.

Arrays should be evaluated based on the number of elements counted directly in the parent array (but not the number of elements contained in any sub-arrays).

Happy coding! :)

def lengthOf (α : Type) : α → Nat
  | _ => sorry

def order_type {α : Type} (arr : List α) : String := sorry

def is_sorted_increasing (xs : List Nat) : Prop := 
  ∀ i j, i < j → j < xs.length → xs[i]! ≤ xs[j]!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded