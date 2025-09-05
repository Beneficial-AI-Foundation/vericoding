Given an array of 2n integers, your task is to group these integers into n pairs of integer, say (a1, b1), (a2, b2), ..., (an, bn) which makes sum of min(ai, bi) for all i from 1 to n as large as possible.

Example 1:

Input: [1,4,3,2]

Output: 4
Explanation: n is 2, and the maximum sum of pairs is 4 = min(1, 2) + min(3, 4).

Note:

n is a positive integer, which is in the range of [1, 10000].
All the integers in the array will be in the range of [-10000, 10000].

def array_pair_sum (nums : List Int) : Int := sorry

def List.sorted (xs : List Int) : List Int := xs -- placeholder for sorting

def evenIndexSum (xs : List Int) : Int :=
  let rec loop : List Int → Int → Int → Int
    | [], _, acc => acc 
    | (x::xs), i, acc => loop xs (i+1) (if i % 2 = 0 then acc + x else acc)
  loop xs 0 0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
