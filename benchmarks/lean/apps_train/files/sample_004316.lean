Simple, given a string of words, return the length of the shortest word(s).

String will never be empty and you do not need to account for different data types.

def min_list : List Nat → Nat 
  | [] => 0
  | (x::xs) => min x (min_list xs)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
