Initially, you have the array $a$ consisting of one element $1$ ($a = [1]$).

In one move, you can do one of the following things:

  Increase some (single) element of $a$ by $1$ (choose some $i$ from $1$ to the current length of $a$ and increase $a_i$ by one);  Append the copy of some (single) element of $a$ to the end of the array (choose some $i$ from $1$ to the current length of $a$ and append $a_i$ to the end of the array). 

For example, consider the sequence of five moves:

  You take the first element $a_1$, append its copy to the end of the array and get $a = [1, 1]$.  You take the first element $a_1$, increase it by $1$ and get $a = [2, 1]$.  You take the second element $a_2$, append its copy to the end of the array and get $a = [2, 1, 1]$.  You take the first element $a_1$, append its copy to the end of the array and get $a = [2, 1, 1, 2]$.  You take the fourth element $a_4$, increase it by $1$ and get $a = [2, 1, 1, 3]$. 

Your task is to find the minimum number of moves required to obtain the array with the sum at least $n$.

You have to answer $t$ independent test cases.

-----Input-----

The first line of the input contains one integer $t$ ($1 \le t \le 1000$) — the number of test cases. Then $t$ test cases follow.

The only line of the test case contains one integer $n$ ($1 \le n \le 10^9$) — the lower bound on the sum of the array.

-----Output-----

For each test case, print the answer: the minimum number of moves required to obtain the array with the sum at least $n$.

-----Example-----
Input
5
1
5
42
1337
1000000000

Output
0
3
11
72
63244

def min_moves_required (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
