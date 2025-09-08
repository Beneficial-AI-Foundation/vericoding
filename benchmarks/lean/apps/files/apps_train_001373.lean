/-
Little Praneet loves experimenting with algorithms and has devised a new algorithm. The algorithm is performed on an integer as follows:
- if the rearmost digit is $0$, he will erase it.
- else, he will replace the rearmost digit $d$ with $d-1$.
If a point comes when the integer becomes $0$, the algorithm stops.
You are given an integer $n$. Praneet will perform the algorithm on it $a$ times. You have to print the result after $a$ operations.

-----Input:-----
- The first and only line of input contains two integers $n$ — initial number, and $a$ —the number of operations.

-----Output:-----
- Print one integer — the result of performing the algorithm on $n$ $a$ times.

-----Constraints-----
- $2 \leq n \leq 10^9$
- $1 \leq a \leq 50$

-----Sample Input 1-----
1001 2

-----Sample Input 2-----
5 2

-----Sample Output 1-----
100

-----Sample Output 2-----
3

-----Explanation-----
- In the first example, the transformation is as follows: $1001->1000->100$.
- In the second example, the transformation is as follows: $5->4->3$.
-/

-- <vc-helpers>
-- </vc-helpers>

def praneet_algorithm (n : Nat) (a : Nat) : Nat :=
  sorry

theorem praneet_algorithm_non_negative (n : Nat) (a : Nat) :
  praneet_algorithm n a ≥ 0 := sorry

theorem praneet_algorithm_upper_bound (n : Nat) (a : Nat) :
  praneet_algorithm n a ≤ n := sorry

theorem praneet_algorithm_zero_iterations (n : Nat) :
  praneet_algorithm n 0 = n := sorry 

theorem praneet_algorithm_composable (n : Nat) :
  praneet_algorithm n 2 = praneet_algorithm (praneet_algorithm n 1) 1 := sorry

theorem praneet_algorithm_divisible_by_10 (n : Nat) :
  praneet_algorithm (n * 10) 1 = n := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible