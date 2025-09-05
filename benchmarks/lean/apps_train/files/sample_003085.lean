Goal
Given a list of elements [a1, a2, ..., an], with each ai being a string, write a function **majority** that returns the value that appears the most in the list. 

If there's no winner, the function should return None, NULL, nil, etc, based on the programming language.

Example
majority(["A", "B", "A"]) returns "A"
majority(["A", "B", "B", "A"]) returns None

def count (xs : List α) (a : α) : Nat :=
  xs.foldl (fun acc x => if x = a then acc + 1 else acc) 0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded