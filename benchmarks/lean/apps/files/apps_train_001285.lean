/-
Chef loves to play games. Now he plays very interesting game called "Segment". At the beginning Chef has segment [0, X] and no points on it. On each step Chef chooses the subsegment of maximal length possible such as it contains no points on it. If there are more than one such subsegment Chef chooses the one with the minimal left coordinate. Once Chef chosed the subsegment he put the point in it's middle and the step is over.
Help Chef to define the coordinate of the point he will put on the K-th step. 

-----Input-----
- The first line contains integer T - number of test cases. 
- Each of next T lines contains two integers X and K. 

-----Output-----
- For each test case in a single line print single double number - the coordinate of the K-th point Chef will put. Answer will be considered as correct if absolute difference between the answer and correct answer is less or equal 10^(-6). 

-----Constraints-----
- 1 ≤ T ≤ 10^5
- 1 ≤ X ≤ 10^9
- 1 ≤ K ≤ 10^12

-----Subtasks-----
- Subtask 1: T ≤ 10; X, K ≤ 20. Points: 15 
- Subtask 2: T ≤ 10; X ≤ 10^6, K ≤ 2*10^5. Points: 25
- Subtask 3: T ≤ 10^5; X ≤ 10^9, K ≤ 10^12. Points: 60

-----Example-----
Input:
4
10 1
10 2
10 3
1000000000 1234567
Output:
5.0000
2.5000
7.5000
177375316.6198730500000000

-----Explanation-----
You can see the points coordinates for the third sample from first two samples.
-/

-- <vc-helpers>
-- </vc-helpers>

def find_kth_point (n : Nat) (k : Nat) : Nat :=
  sorry

theorem result_bounded (n : Nat) (k : Nat) (h : k > 0) :
  let res := find_kth_point n k
  res ≤ n ∧ res ≥ 0 := by
  sorry

theorem first_point_divides_evenly (n : Nat) (h : n > 0) :
  find_kth_point n 1 = n / 2 := by 
  sorry

theorem second_point_divides_evenly (n : Nat) (h : n > 0) :
  find_kth_point n 2 = n / 4 := by
  sorry

theorem k_must_be_positive (n : Nat) :
  ∀ k : Nat, k = 0 → find_kth_point n k = find_kth_point n k → False := by
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded