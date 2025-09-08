/-
Chef likes toys. His favourite toy is an array of length N. This array contains only integers. He plays with this array every day. His favourite game with this array is Segment Multiplication. In this game, the second player tells the left and right side of a segment and some modulo. The first player should find the multiplication of all the integers in this segment of the array modulo the given modulus. Chef is playing this game. Of course, he is the first player and wants to win all the games. To win any game he should write the correct answer for each segment. Although Chef is very clever, he has no time to play games. Hence he asks you to help him. Write the program that solves this problem.

-----Input-----
The first line of the input contains an integer N denoting the number of elements in the given array. Next line contains N integers Ai separated with spaces. The third line contains the number of games T. Each of the next T lines contain 3 integers Li, Ri and Mi, the left side of the segment, the right side of segment and the modulo.

-----Output-----
For each game, output a single line containing the answer for the respective segment.

-----Constrdaints-----
- 1 ≤ N ≤ 100,000
- 1 ≤ Ai ≤ 100
- 1 ≤ T ≤ 100,000
- 1 ≤ Li ≤ Ri ≤ N
- 1 ≤ Mi ≤ 109

-----Example-----
Input:
5
1 2 3 4 5
4
1 2 3
2 3 4
1 1 1
1 5 1000000000

Output:
2
2
0
120
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_segment_multiplication (arr : List Nat) (queries : List (Nat × Nat × Nat)) : List Nat :=
sorry

-- Results length matches queries length

theorem solve_length_matches {arr : List Nat} {queries : List (Nat × Nat × Nat)} :
  (solve_segment_multiplication arr queries).length = queries.length :=
sorry

-- All results are within modulo bounds

theorem solve_results_within_bounds {arr : List Nat} {queries : List (Nat × Nat × Nat)} :
  ∀ (i : Nat), i < (solve_segment_multiplication arr queries).length →
  ∀ (l r m : Nat), queries.get! i = (l, r, m) →
  ∃ (result : Nat), (solve_segment_multiplication arr queries).get! i = result ∧ result < m :=
sorry

-- m=1 case gives 0

theorem solve_mod_one {arr : List Nat} {queries : List (Nat × Nat × Nat)} :
  ∀ (i : Nat), i < (solve_segment_multiplication arr queries).length →
  ∀ (l r : Nat), queries.get! i = (l, r, 1) →
  (solve_segment_multiplication arr queries).get! i = 0 :=
sorry

-- Single element queries give correct modulo

theorem solve_single_elem {arr : List Nat} {queries : List (Nat × Nat × Nat)} :
  ∀ (i : Nat), i < (solve_segment_multiplication arr queries).length →
  ∀ (l m : Nat), queries.get! i = (l, l, m) →
  (solve_segment_multiplication arr queries).get! i = (arr.get! (l-1)) % m :=
sorry

-- Full array query equals product mod m

theorem solve_full_array {arr : List Nat} {m : Nat} :
  let queries := [(1, arr.length, m)]
  let result := (solve_segment_multiplication arr queries).get! 0
  let expected := arr.foldl (fun acc x => (acc * x) % m) 1
  result = expected :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded