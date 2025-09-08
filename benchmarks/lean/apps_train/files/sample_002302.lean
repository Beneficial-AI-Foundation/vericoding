/-
Given an array of integers arr, and three integers a, b and c. You need to find the number of good triplets.
A triplet (arr[i], arr[j], arr[k]) is good if the following conditions are true:

0 <= i < j < k < arr.length
|arr[i] - arr[j]| <= a
|arr[j] - arr[k]| <= b
|arr[i] - arr[k]| <= c

Where |x| denotes the absolute value of x.
Return the number of good triplets.

Example 1:
Input: arr = [3,0,1,1,9,7], a = 7, b = 2, c = 3
Output: 4
Explanation: There are 4 good triplets: [(3,0,1), (3,0,1), (3,1,1), (0,1,1)].

Example 2:
Input: arr = [1,1,2,2,3], a = 0, b = 0, c = 1
Output: 0
Explanation: No triplet satisfies all conditions.

Constraints:

3 <= arr.length <= 100
0 <= arr[i] <= 1000
0 <= a, b, c <= 1000
-/

def isValidTriplet (arr : List Int) (i j k a b c : Nat) : Bool :=
  sorry

def countTripletsBruteforce (arr : List Int) (a b c : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def countGoodTriplets (arr : List Int) (a b c : Nat) : Nat :=
  sorry

theorem countGoodTriplets_matches_bruteforce 
    (arr : List Int) (a b c : Nat) 
    (h : arr.length ≥ 3)
    (h2 : arr.length ≤ 20)
    (h3 : ∀ x ∈ arr, -100 ≤ x ∧ x ≤ 100)
    (h4 : a ≤ 50 ∧ b ≤ 50 ∧ c ≤ 50) :
    countGoodTriplets arr a b c = countTripletsBruteforce arr a b c :=
  sorry

theorem countGoodTriplets_nonnegative
    (arr : List Int) (a b c : Nat)
    (h : arr.length ≥ 3)
    (h2 : arr.length ≤ 20) :
    0 ≤ countGoodTriplets arr a b c :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_good_triplets [3, 0, 1, 1, 9, 7] 7 2 3

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_good_triplets [1, 1, 2, 2, 3] 0 0 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_good_triplets [1, 2, 3, 4, 5] 1 1 1

-- Apps difficulty: introductory
-- Assurance level: unguarded