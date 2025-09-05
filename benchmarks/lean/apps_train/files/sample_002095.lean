There are n psychos standing in a line. Each psycho is assigned a unique integer from 1 to n. At each step every psycho who has an id greater than the psycho to his right (if exists) kills his right neighbor in the line. Note that a psycho might kill and get killed at the same step. 

You're given the initial arrangement of the psychos in the line. Calculate how many steps are needed to the moment of time such, that nobody kills his neighbor after that moment. Look notes to understand the statement more precise.

-----Input-----

The first line of input contains integer n denoting the number of psychos, (1 ≤ n ≤ 10^5). In the second line there will be a list of n space separated distinct integers each in range 1 to n, inclusive — ids of the psychos in the line from left to right.

-----Output-----

Print the number of steps, so that the line remains the same afterward.

-----Examples-----
Input
10
10 9 7 8 6 5 3 4 2 1

Output
2

Input
6
1 2 3 4 5 6

Output
0

-----Note-----

In the first sample line of the psychos transforms as follows: [10 9 7 8 6 5 3 4 2 1]  →  [10 8 4]  →  [10]. So, there are two steps.

def solve_psychos (n : Nat) (arr : List Nat) : Nat :=
  sorry

def is_sorted_desc (arr : List Nat) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible