/-
Binod is a youtuber and he is busy in the fame of social media so he asked you to help him solve a problem.
You have been given an array of $positive$ $integers$ $a_{1},a_{2},a_{3},...,a_{i},...,a_{n}$ of size n.You have to find the smallest length of the subarray such that the length of the subarray must be $strictly$ greater than k and it's sum also must be $strictly$ greater than s. 

-----Input Format :------
- The first line of input contains three space-separated integers n, k and s
- The second line contains n space-separated integers,describing the array a 

-----Output Format:-----
- Print a single integer :- The smallest length of subarray if exists, Otherwise print "-1" (without quotes) 

-----Constraints:------
- $1 \leq n, k \leq 10^{6}$
- $1 \leq  a_{1},a_{2},a_{3},...,a_{i},...,a_{n}\leq 10^{9}$ 
- $1 \leq s \leq 10^{15}$ Subtask #1 (30 points):
- $1 \leq n, k \leq 10^{3}$ Subtask #2 (70 points):
$Original$ $Constraints$ 

-----Sample Test Cases:------

-----Example 1:-----
5 1 5

1 2 3 4 5 

-----Output :-----
2 

-----Explanation-----
$\textbf{There are two possibles answers} :$ 
- Index starts at 3 and ends at 4 have a sum of 7 which is strictly greater than 5 and has a length of subarray greater than 1.  
- Index starts at 4 and ends at 5 have a sum of 9 which is strictly greater than 5 and has a length of subarray greater than 1.
Any of the possible scenarios gives the same answer.

-----Example 2:-----
3 2 1

9 9 1 

-----Output :-----
3

-----Explanation :-----
- Each value in array index satisfies the condition sum greater than 1 but to satisfy the condition of length greater than 2 choose the subarray of length 3
-/

def List.sum : List Int → Int 
  | [] => 0
  | x::xs => x + sum xs 

def find_subarray_length (n : Nat) (k : Nat) (s : Int) (arr : List Int) : Int :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def Int.abs (i : Int) : Int :=
  if i < 0 then -i else i

theorem subarray_length_n_leq_k {n k : Nat} {s : Int} {arr : List Int} 
  (h : n ≤ k) : 
  find_subarray_length n k s arr = -1 := 
sorry

theorem subarray_length_valid {n k : Nat} {s : Int} {arr : List Int}
  (h : find_subarray_length n k s arr ≠ -1) :
  find_subarray_length n k s arr > k := 
sorry

theorem exists_subarray_sum {n k : Nat} {s : Int} {arr : List Int}
  (h : find_subarray_length n k s arr ≠ -1) :
  ∃ i : Nat, i + find_subarray_length n k s arr ≤ n ∧ 
    (List.sum (List.take (find_subarray_length n k s arr).toNat (List.drop i arr)) > s) :=
sorry

theorem no_smaller_length {n k : Nat} {s : Int} {arr : List Int} 
  (h : find_subarray_length n k s arr ≠ -1)
  (len : Nat)
  (h1 : k < len)
  (h2 : len < (find_subarray_length n k s arr).toNat) :
  ∀ i : Nat, i + len ≤ n → 
    List.sum (List.take len (List.drop i arr)) ≤ s :=
sorry

theorem positive_arr_negative_s {n k : Nat} {s : Int} {arr : List Int}
  (h1 : ∀ x ∈ arr, 0 ≤ x)
  (h2 : s < 0)
  (h3 : n > k) :
  find_subarray_length n k s arr = k + 1 :=
sorry

theorem sum_too_high {n k : Nat} {s : Int} {arr : List Int}
  (h : s > List.sum (List.map Int.abs arr)) :
  find_subarray_length n k s arr = -1 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_subarray_length 5 1 5 [1, 2, 3, 4, 5]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_subarray_length 3 2 1 [9, 9, 1]

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_subarray_length 4 3 100 [1, 2, 3, 4]

-- Apps difficulty: interview
-- Assurance level: guarded