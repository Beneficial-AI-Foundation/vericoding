There are $N$ friends in a group. Each of them have $A_{i}$ candies.
Can they share all of these candies among themselves such that each one of them have equal no. of candies.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- First line of each testcase contains of a single line of input, an integer $N$ denoting no. of friends in the group. 
- Next line contains $N$ space separated integers $A_{i}$  denoting the no. candies  $i^{th}$ friend has.

-----Output:-----
For each testcase, output $"Yes"$ if it is possible to share equally else $"No"$ (without " ").

-----Constraints-----
- $1 \leq T \leq 10$
- $1 \leq N \leq 100$
- $0 \leq A_{i} \leq 1000$

-----Sample Input:-----
1

3

1 2 3

-----Sample Output:-----
Yes

-----EXPLANATION:-----
Each of them have $2$ candies after sharing.

def List.sum : List Nat → Nat 
| [] => 0
| (h :: t) => h + sum t

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
