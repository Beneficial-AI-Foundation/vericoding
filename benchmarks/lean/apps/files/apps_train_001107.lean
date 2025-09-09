/-
In a bizarre game of chess ,knight was so drunk, that instead of his usual move he started walking straight. In every move Knight jumps on 2n steps forward (n is number of block that he had travelled so far from starting) but after that he has to take either 1 step forward or backward.
Now the Knight needs to get to position X so King (i.e. You) needs to decide the order of his backward or forward step in such a way that he can reach its destination in minimum number of steps. Remember he always travels in a straight line and the length of the board is infinite.

-----Input-----
The first line of the input contains an integer T denoting the number of test cases, for each test case enter value X ( i.e. destination)
Note : initially knight is at n = 1.

-----Output-----
For each test case the output should be string of numbers 1 & 2 where 1 denotes backward step and 2 denote the forward step 
Note : for no solution print 0.

-----Constraints-----
- 1 ≤ T ≤ 100
- 1 ≤ X ≤ 10^10

-----Example-----
Input:
2
17
10
Output:
2111
0

-----Explanation-----
Case 1 : starting from  n = 1 , knight moves to n = 3 ('2') , 5 ('1') , 9 ('1') , 17 ('1') i.e. string printed is 2 1 1 1
Case 2 : no solution is possible
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_knight_steps (n : Nat) : String := sorry

theorem even_numbers_return_zero {n : Nat} (h : n > 0) (h2 : n % 2 = 0) :
  solve_knight_steps n = "0" := sorry

theorem output_contains_valid_moves {n : Nat} (h : n > 0) :
  ∀ (i : String.Pos), i.1 < (solve_knight_steps n).length →
    let c := (solve_knight_steps n).get i
    c = '0' ∨ c = '1' ∨ c = '2' ∨ c = '3' := sorry

theorem special_cases_one_and_three {n : Nat} :
  (n = 1 → solve_knight_steps n = "1") ∧
  (n = 3 → solve_knight_steps n = "3") := sorry

theorem path_length_matches_tree_depth {n : Nat} (h : n > 0) (h2 : n % 2 = 1) (h3 : n > 3) :
  String.length (solve_knight_steps n) = Nat.log2 n := sorry

theorem result_follows_binary_tree_pattern {n : Nat} (h : n > 0) (h2 : n % 2 = 1) (h3 : n > 3) :
  let result := solve_knight_steps n
  let final_pos := result.foldl 
    (fun pos c => 
      if c = '1' then 
        2 * pos - 1
      else if c = '2' then
        2 * pos + 1
      else 
        pos) 3
  final_pos = n := sorry

/-
info: '2111'
-/
-- #guard_msgs in
-- #eval solve_knight_steps 17

/-
info: '0'
-/
-- #guard_msgs in
-- #eval solve_knight_steps 10

/-
info: '3'
-/
-- #guard_msgs in
-- #eval solve_knight_steps 3

-- Apps difficulty: interview
-- Assurance level: unguarded