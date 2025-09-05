There are $N$ cells numbered 1,2,….., N, and every cell has some positive value. you will be given an array $A_1$,$A_2$,…,$A_N$ where $A_i$ is the value of $ith$ cell and an integer $K$.
There is a monkey who wants to reach the $right$ side of the last ($Nth$) cell, initially, the monkey was left side of the first ($1st$) cell. 
In the first step, he can jump into any cell numbered 1,2,….., K.Once he jumped into any cell $i$ next he can only jump to the cell $j$ such that-
- j>i
- j-i <= K  
- A[i]%2 == A[j]%2
You have to find out what is the minimum number of steps required to reach the right side of the cell or In case it's not possible to reach the right side of the cell your answer should be $-1$.NOTE: As soon as monkey reach any cell whose distance from the last cell is less than K, then in the last step, he will jump out to the right side of the ($Nth$) cell.

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- The first line of each test case contains two space-separated integers $N$ and $K$.
- The second line contains $N$ space-separated integers $A_1$,$A_2$,…,$A_N$

-----Output:-----
For each test case, output in a single line minimum steps or $-1$.

-----Constraints-----
- $1 \leq T \leq 100$
- $1 \leq N \leq 2*10^5$
- $1 \leq K \leq N$
- $0 \leq A_i \leq 10^6$
- $\text{the sum of N over all test cases does not exceed $5*10^{5}$}$

-----Sample Input:-----
1
2 2
3 4

-----Sample Output:-----
2 

-----EXPLANATION:-----
in the first step, you can jump into any cell 1 or 2 and then in the second step you will jump 
out to the right side of 2nd cell
remember we don't want to reach $Nth$ cell we want to reach the right side of the nth cell.

def find_min_steps (i j : Nat) (nums : List Nat) : Nat := sorry

def list_max : List Nat → Nat 
| [] => 0
| [x] => x
| (x::xs) => Nat.max x (list_max xs)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible