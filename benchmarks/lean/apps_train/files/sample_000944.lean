You are given an $array$ of size $N$ and an integer $K$ ( $N > 1 , K > 0$ ).
Each element in the array can be incremented by $K$ or decremented by $K$ $at$ $most$ $once$.
So there will be  $3^n$ possible combinations of final array. (As there are 3 options for every element).

Out of these combinations, you have to select a combination, in which the $absolute$ difference between the largest and the smallest element is $maximum$.
You have to print the $maximum$ $absolute$ $difference$.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a two lines of input
- First line contains two integers $N, K$. 
- Second line contains $N$ space separated integers.

-----Output:-----
For each testcase, output the maximum absolute difference that can be achieved on a new line.

-----Constraints-----
- $1 \leq T \leq 10$
- $2 \leq N \leq 1000$
- $1 \leq K , arr[i]  \leq 10000$
$NOTE$:  Large  input files, Use of fastio is recommended.

-----Sample Input:-----
2

4 3

4 2 5 1

3 5

2 5 3

-----Sample Output:-----
10

13

def find_max_diff (N : Nat) (K : Nat) (arr : List Int) : Int :=
sorry

def list_max (arr : List Int) : Int :=
sorry

def list_min (arr : List Int) : Int :=
sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
