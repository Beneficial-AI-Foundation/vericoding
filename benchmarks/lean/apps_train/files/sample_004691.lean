Linked Lists - Length & Count

Implement Length() to count the number of nodes in a linked list.
Implement Count() to count the occurrences of an integer in a linked list.

I've decided to bundle these two functions within the same Kata since they are both very similar.

The `push()`/`Push()` and `buildOneTwoThree()`/`BuildOneTwoThree()` functions do not need to be redefined.

def length {α : Type} : Node α → Nat
  | Node.nil => 0
  | Node.cons _ next => 1 + length next

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded