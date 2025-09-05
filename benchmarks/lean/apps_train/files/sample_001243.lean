You are given a string $s$. And you have a function $f(x)$ defined as:
f(x) = 1, if $x$ is a vowel
f(x) = 0, if $x$ is a constant

Your task is to apply the above function on all the characters in the string s and convert 
the obtained binary string in decimal number $M$.
Since the number $M$ can be very large, compute it modulo $10^9+7$. 

-----Input:-----
- The first line of the input contains a single integer $T$ i.e the no. of test cases. 
- Each test line contains one String $s$ composed of lowercase English alphabet letters. 

-----Output:-----
For each case, print a single line containing one integer $M$ modulo $10^9 + 7$.

-----Constraints-----
- $1 ≤ T ≤ 50$
- $|s|≤10^5$

-----Subtasks-----
- 20 points : $|s|≤30$
- 80 points : $ \text{original constraints}$

-----Sample Input:-----
1
hello

-----Sample Output:-----
9

def binaryStringToDecimal (s : String) : Nat := sorry

theorem result_in_valid_range (s : String) (h : s.length > 0) : 
  binaryStringToDecimal s < 10^9 + 7 ∧ binaryStringToDecimal s ≥ 0 := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded