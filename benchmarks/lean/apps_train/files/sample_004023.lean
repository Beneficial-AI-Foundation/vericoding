You are given an initial 2-value array (x). You will use this to calculate a score.

If both values in (x) are numbers, the score is the sum of the two. If only one is a number, the score is that number. If neither is a number, return 'Void!'.

Once you have your score, you must return an array of arrays. Each sub array will be the same as (x) and the number of sub arrays should be equal to the score.

For example:

if (x) == ['a', 3]  you should return [['a', 3], ['a', 3], ['a', 3]].

def List.sum : List Nat → Nat 
  | [] => 0
  | (h::t) => h + sum t

def explode {α : Type} : List α → List (List α) := sorry

theorem explode_integers {arr : List Nat} 
  (h1 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 10) 
  (h2 : 1 ≤ arr.length ∧ arr.length ≤ 5) :
  let result := explode arr
  (result.length = arr.sum) ∧ 
  (∀ x ∈ result, x = arr) := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded