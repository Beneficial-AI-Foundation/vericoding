Chef has a strip of length $N$ units and he wants to tile it using $4$ kind of tiles

-A Red tile of $2$ unit length

-A Red tile of $1$ unit length

-A Blue tile of $2$ unit length

-A Blue tile of $1$ unit length   
Chef is having an infinite supply of each of these tiles. He wants to find out the number of ways in which he can tile the strip. Help him find this number.
Since this number can be large, output your answer modulo 1000000007 ($10^9 + 7$).

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, an integer $N$. 

-----Output:-----
For each testcase, output in a single line your answer modulo 1000000007.

-----Constraints-----
- $1 \leq T \leq 1000$
- $2 \leq N \leq 10^{18}$

-----Sample Input:-----
1
2

-----Sample Output:-----
6

-----EXPLANATION:-----

It can be seen that for a strip of length $2$, there are $6$ possible configurations.     
$NOTE : $ 2 tiles of 1 unit length are different from 1 tile of 2 unit length.

def solve_tile_count (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
