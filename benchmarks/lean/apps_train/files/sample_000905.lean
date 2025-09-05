One day, Delta, the dog, got very angry. He has $N$ items with different values, and he decided to destroy a few of them. However, Delta loves his hooman as well. So he only destroyed those items whose Least Significant Bit in binary representation is 0. 
Can you help Delta to find the total damage he did so he could make an equally sorry face?

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- First line of Each test case a single integer $N$.
- Next line contains $N$ integers denoting values of items.

-----Output:-----
For each testcase, output in a single line the total damage caused by Delta.

-----Constraints-----
- $1 \leq T \leq 10^3$
- $1 \leq N \leq 10^3$
- $1 \leq value \leq 10^3$

-----Sample Input:-----
1
5

1 2 3 4 5

-----Sample Output:-----
6

-----EXPLANATION:-----
Total Damage: $2  + 4 = 6$.

def sum_list : List Nat → Nat 
  | [] => 0
  | (h :: t) => h + sum_list t

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible