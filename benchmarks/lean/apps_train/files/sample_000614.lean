Well known investigative reporter Kim "Sherlock'' Bumjun needs your help! Today, his mission is to sabotage the operations of the evil JSA. If the JSA is allowed to succeed, they will use the combined power of the WQS binary search and the UFDS to take over the world!
But Kim doesn't know where the base is located. He knows that the base is on the highest peak of the Himalayan Mountains. He also knows the heights of each of the $N$ mountains. Can you help Kim find the height of the mountain where the base is located? 

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow.    
- The first line in each testcase contains one integer, $N$.    
- The following $N$ lines of each test case each contain one integer: the height of a new mountain.

-----Output:-----
For each testcase, output one line with one integer: the height of the tallest mountain for that test case.

-----Constraints-----
- $1 \leq T \leq 10$
- $1 \leq N \leq 100000$
- $0 \leq$ height of each mountain $\leq 10^9$

-----Subtasks:-----
- 100 points: No additional constraints.

-----Sample Input:-----
1
5
4
7
6
3
1

-----Sample Output:-----
7

def find_tallest_mountain (n : Nat) (heights : List Nat) : Nat :=
sorry

def list_max (l : List Nat) : Nat :=
match l with
| [] => 0
| h::t => List.foldl Nat.max h t

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
