-----
ARRAY AND DISTINCT ELEMENTS
-----

Chef is multitalented but he mistakenly took part in 2 contest which will take place
at the same time. So while chef is busy at one cooking contest, he wants you to
take part in coding contest. Chef wants u to solve this program for him.

You have been given an array of size n. You have to calculate a subarray of size k
with maximum sum having distinct elements same as original array.

-----Input Format-----

First line contains no. of test cases. Second line contains n and k. Third line
contains array of n integers.

-----Output-----

Print maximum possible sum as stated in question

-----Example Text Case-----
Input:

1
10 6
8 8 3 5 3 8 5 7 7 7

Output:
37

def sum (l : List Nat) : Nat :=
  l.foldl (· + ·) 0

def find_max_distinct_subarray_sum (n k : Nat) (arr : List Nat) : Int :=
  sorry

def allEqual (l : List Nat) : Prop :=
  ∀ x y, x ∈ l → y ∈ l → x = y

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded