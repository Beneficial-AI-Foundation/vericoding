Problem Statement:Captain America and Iron Man are at WAR and the rage inside Iron Man is rising.

But Iron Man faces a problem to identify the location of Captain America.

There are N buildings situtaed adjacently to each other and Captain America can be at any building.

Iron Man has to arrange the Buildings from 1 to N is such a way that Value(i.e abs(Building Number -Position of Building))=K for every building.

Can You help Iron Man to Find The Arrangement of the Buildings?

P.S- If no arrangement exist, then print         
“CAPTAIN AMERICA EVADES”.

Input Format:
The first line of input contains a single integer,T, denoting the number of test cases.

Each of the T  subsequent lines contains 2 space-separated integers describing the respective N and K values for a test case.

Output Format:
On a new line for each test case, 

Print the lexicographically smallest arrangement; 

If no absolute arrangement exists, print “CAPTAIN AMERICA EVADES”.

Constraints:
SubTask#1
1<=T<=10

1<=N<=10^5

0<=K<=N

SubTask#2
Original Constraints..

SubTask#3
Original Constraints..

Sample Input:
3

2 1

3 0

3 2

Sample Output:

2 1

1 2 3

CAPTAIN AMERICA EVADES

Explanation:
Case 1:

N=2 and K=1

Therefore the arrangement is [2,1].

Case 2:

N=3 and K=0

Therefore arrangement is [1,2,3].

def find_building_arrangement (n k : Nat) : String := sorry

def nums_to_nat_list (s : String) : List Nat := sorry

def range_from_one (n : Nat) : List Nat :=
  List.range n |>.map (· + 1)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded