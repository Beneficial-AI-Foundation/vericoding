Sam is an avid collector of numbers. Every time he finds a new number he throws it on the top of his number-pile. Help Sam organise his collection so he can take it to the International Number Collectors Conference in Cologne. 

Given an array of numbers, your function should return an array of arrays, where each subarray contains all the duplicates of a particular number. Subarrays should be in the same order as the first occurence of the number they contain:
Assume the input is always going to be an array of numbers. If the input is an empty array, an empty array should be returned.

def group (arr : List Int) : List (List Int) := sorry

def listSum (xs : List Nat) : Nat := 
  match xs with
  | [] => 0
  | h :: t => h + listSum t

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible