Sunita has lots of tasks pending and she has no time to complete.  She needs your help and wants you complete the task.
You are given a list of integers and two values $N$ and $K$ $-$ the size of array of integers and the numbers of partitions to be made respectively.
You have to partition the list of integers without changing the order of elements ,into exactly $K$ parts. 
Calculate Greatest Common Divisor of all $K$ partition and sum up the gcd values for each partition.
Maximize the sum obtained. 
Can you help Sunita ? 

-----Input:-----
- First line will contain $T$, number of test cases. Then the test cases follow. 
- Each test case contains of a single line of input, two integers $N, K$. 
- Next line contains $N$ integers $-$ the list of integers.

-----Output:-----
For each test case, output in a single line integer $-$ the maximal result.

-----Constraints-----
- $1 \leq T \leq 100$
- $1 \leq N, K \leq 250$
- $1 \leq K \leq N$
- $1 \leq A[i] \leq 1e5$

-----Sample Input:-----
1
4 2
5 6 3 2

-----Sample Output:-----
6

-----EXPLANATION:-----
[5] [6 3 2] is the best partition [5 + GCD(6,3,2)] = 6

def List.sum : List Nat → Nat 
  | [] => 0
  | x :: xs => x + xs.sum

def gcd_multiple (nums : List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded