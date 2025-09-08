/-
Alice's school is planning to take some students from her class on a field trip. Alice is really excited about it. There are a total of S students in her class. But due to budget constraints, the school is planning to take only N students for the trip. These students will be picked randomly. And each student has equal chance of being picked.
Alice's friend circle has M students including her. Though she is excited about the field trip, she will enjoy it only if there are atleast K of her friends with her on the trip. She is wondering what are the chances of that happening. She needs your help. Tell her the probability that she will enjoy given that she goes on the trip.

-----Input:-----
First line of input contains a single integer T, the number of test cases.

Each test starts with a single line having 4 space separated integers, S, N, M and K.

-----Output:-----
For each test case, output a line containing the required probability. The answer will be accepted if the relative error is not more than 10-6.

-----Constraints:-----
1 ≤ T ≤ 100
1 ≤ S ≤ 1000
1 ≤ N ≤ S
1 ≤ M ≤ S
0 ≤ K < M

-----Example:-----Input:
3
10 10 5 3
10 4 6 4
3 2 2 1

Output:
1.000000
0.000000
0.500000

-----Explanation:-----Case #1:
Every student will be taken to the trip. So all her 4 friends will accompany her to the trip no matter what. 
Case #2:
Alice wants 4 out of her 5 friends to come along with her which isn't possible because the school is willing to pick only 4 students for the trip.
-/

-- <vc-helpers>
-- </vc-helpers>

def calculate_probability (S N M K : Nat) : Float := sorry

theorem equal_sizes {S : Nat}
  (h1: S ≥ 1)
  (h2: S ≤ 20) :
  let p := calculate_probability S S S 0
  (p - 1).abs < 0.000001 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible