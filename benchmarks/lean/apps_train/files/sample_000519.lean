/-
The chef is playing a game of long distance. Chef has a number K and he wants to find the longest distance between the index of the first and the last occurrence of K in a given array of N numbers.

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Each test case contains two lines of input.
- Next line with Two integers in one line $K, N$.
- Next line with $N$ space-separated integers.

-----Output:-----
For each test case, output in a single line answer as the index of first and last occurrence of K in the given array.
Note: Here Indexing is from 1 not  0 based.

-----Constraints-----
- $1 \leq T \leq 100$
- $1 \leq k \leq 10^5$
- $1 \leq N \leq 10^5$

-----Sample Input:-----
2
2 6
2 3 4 2 1 6
4 6
2 3 4 2 1 6

-----Sample Output:-----
3
0

-----EXPLANATION:-----
For 1) Index of First and last occurrence of 2 in the given array is at 1 and 4, i.e. distance is 3. 
For 2) 4 occurs only once in the given array hence print 0.
-/

def find_longest_distance (k : Int) (arr : List Int) : Int := sorry

-- Value not in array gives 0 distance

-- <vc-helpers>
-- </vc-helpers>

def findLastIndex (p : α → Bool) (l : List α) : Option Nat :=
  let indexed := List.enumFrom 0 l
  (indexed.find? (fun (i, x) => p x)).map Prod.fst

-- Distance equals last occurrence minus first occurrence

theorem missing_value_distance 
  {k : Int} {arr : List Int} 
  (h : ¬ k ∈ arr) : 
  find_longest_distance k arr = 0 := sorry

-- Distance is always non-negative  

theorem distance_non_negative
  (k : Int) (arr : List Int) :
  find_longest_distance k arr ≥ 0 := sorry

-- Distance is bounded by array length minus 1

theorem distance_upper_bound 
  (k : Int) (arr : List Int) :
  find_longest_distance k arr ≤ max (arr.length - 1) 0 := sorry

-- Function to find last index

theorem distance_matches_occurrences 
  (k : Int) (arr : List Int) :
  find_longest_distance k arr = 
    let first := arr.findIdx? (· = k)
    let last := findLastIndex (· = k) arr
    match first, last with
    | some i, some j => j - i 
    | _, _ => 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_longest_distance 2 [2, 3, 4, 2, 1, 6]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_longest_distance 4 [2, 3, 4, 2, 1, 6]

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_longest_distance 1 [1, 2, 3, 1, 2, 3, 1]

-- Apps difficulty: interview
-- Assurance level: guarded