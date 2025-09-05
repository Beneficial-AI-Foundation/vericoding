Chef has been working in a restaurant which has  N  floors. He wants to minimize the time it takes him to go from the N-th floor to ground floor. He can either take the elevator or the stairs. 
The stairs are at an angle of 45 degrees and Chef's velocity is V1 m/s when taking the stairs down. The elevator on the other hand moves with a velocity V2 m/s. Whenever an elevator is called, it always starts from ground floor and goes to N-th floor where it collects Chef (collecting takes no time), it then makes its way down to the ground floor with Chef in it.  

The elevator cross a total distance equal to N meters when going from N-th floor to ground floor or vice versa, while the length of the stairs is sqrt(2) * N because the stairs is at angle 45 degrees.

Chef has enlisted your help to decide whether he should use stairs or the elevator to minimize his travel time. Can you help him out?

-----Input-----
The first line contains a single integer T, the number of test cases. Each test case is described by a single line containing three space-separated integers N, V1, V2. 

-----Output-----
For each test case, output a single line with string Elevator or Stairs, denoting the answer to the problem.

-----Constraints-----
- 1 ≤ T ≤  1000 
- 1 ≤ N, V1, V2 ≤  100 

-----Example-----
Input:
3
5 10 15
2 10 14
7 14 10

Output:
Elevator
Stairs
Stairs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded