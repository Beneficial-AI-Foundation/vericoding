Chef is playing a game which contains a binary string. 
He can perform one operation only:
- Toggle the i_th bit of the string (0 to 1 or 1 to 0)
By performing operations on the string (can be zero times), you have to convert the string with no adjacent bit being the same.
Can you help chef ?

-----Input:-----
- First line will contain $T$, number of test cases. Then the test cases follow. 
- First line of each test case, contains the size of the  string $N$
- Seond line contains a single line of input, the binary string. 

-----Output:-----
For each testcase, output in a single line answer - the minimum operations.

-----Constraints-----
- $1 \leq T \leq 100$
- $2 \leq |S| \leq 10^3$

-----Sample Input:-----
1
4
1011

-----Sample Output:-----
1

def min_operations_to_alternating (n : Nat) (s : String) : Nat :=
  sorry

def is_alternating (s : String) : Bool := 
  sorry

def make_alternating_01 (n : Nat) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
