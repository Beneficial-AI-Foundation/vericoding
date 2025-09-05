Chef is given a sequence of prime numbers $A_1, A_2, \ldots, A_N$. This sequence has exactly $2^N$ subsequences. A subsequence of $A$ is good if it does not contain any two identical numbers; in particular, the empty sequence is good.
Chef has to find the number of good subsequences which contain at most $K$ numbers. Since he does not know much about subsequences, help him find the answer. This number could be very large, so compute it modulo $1,000,000,007$.

-----Input-----
- The first line of the input contains two space-separated integers $N$ and $K$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
Print a single line containing one integer ― the number of good subsequences with size at most $K$, modulo $1,000,000,007$.

-----Constraints-----
- $1 \le K \le N \le 10^5$
- $2 \le A_i \le 8,000$ for each valid $i$

-----Subtasks-----
Subtask #1 (40 points): $A_1, A_2, \ldots, A_N$ are pairwise distinct
Subtask #2 (60 points): original constraints

-----Example Input-----
5 3
2 2 3 3 5

-----Example Output-----
18

-----Explanation-----
There is $1$ good subsequence with length $0$, $5$ good subsequences with length $1$, $8$ good subsequences with length $2$ and $4$ good subsequences with length $3$.

def List.sum : List Nat → Nat
| [] => 0
| (h::t) => h + List.sum t

def solve (arr : List Nat) (n k : Nat) : Nat :=
  sorry

def windowSum (arr : List Nat) (start len : Nat) : Nat :=
  (arr.take (start + len)).drop start |>.sum

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded