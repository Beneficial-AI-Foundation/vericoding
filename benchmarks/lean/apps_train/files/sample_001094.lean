Chef has an array of N natural numbers most of them are repeated. Cheffina challenges chef to find all numbers(in ascending order) whose frequency is strictly more than K.

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Each test case contains two lines of input, two integers $N, K$.
- N space-separated natural numbers.

-----Output:-----
For each test case, output in a single line answer.

-----Constraints-----
- $1 \leq T \leq 10$
- $1 \leq N, K \leq 10^5$
- $1 \leq arr[i] \leq 10^5$

-----Sample Input:-----
1
5 1
5 2 1 2 5

-----Sample Output:-----
2 5

def find_frequent_numbers (n : Nat) (k : Nat) (arr : List Nat) : List Nat :=
  sorry

def count {α} [BEq α] (as : List α) (a : α) : Nat :=
  sorry

def isSorted (l : List Nat) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
