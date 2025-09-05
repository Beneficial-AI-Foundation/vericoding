You have found $M$ different types of jewels in a mine and each type of jewel is present in an infinite number.
There are $N$ different boxes located at position $(1 ,2 ,3 ,...N)$.
Each box can collect jewels up to a certain number ( box at position $i$ have $i$ different partitions and each partition can collect at most one jewel of any type).
Boxes at odd positions are already fully filled with jewels while boxes at even positions are completely empty.
Print the total number of different arrangements possible so that all boxes can be fully filled.
As the answer can be very large you can print it by doing modulo with 1000000007(10^9+7).

-----Input:-----
- First line will contain $T$, number of testcases. 
- Each testcase contains of a single line of input, two integers $N ,  M$. 

-----Output:-----
For each testcase, Print the total number of different arrangement.

-----Constraints-----
- $1 \leq T \leq 20000$
- $1 \leq N \leq 1e9$
- $1 \leq M \leq 1e14$

-----Sample Input:-----
2
1 10
5 2

-----Sample Output:-----
1
64

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded