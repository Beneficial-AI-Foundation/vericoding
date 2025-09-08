/-
The chef is very expert in coding, so to keep his password safe from the hackers. He always enters a decoded code of his password. You are a hacker and your work is to find the maximum number of possible ways to unlock his password in encoded form.

The encoded message containing only letters from A-Z is being encoded with numbers using the following mapping: 

'A' -> 1 

'B' -> 2 ... 

'Z' -> 26

You have given a non-empty string containing only digits, determine the total number of ways to encode it. 

If the total number of ways are even then you are able to unlock the password. 

Input: 
The first line has a single integer T, denoting the number of test cases. The first line of each test case contains string “S” decoded number.

Output:
For each test case, in a new line, print 'YES' if number of maximum ways are even, otherwise
'NO'. (without quotes)

Constraints:
1 ≤ T ≤ 50

1 ≤ S ≤ 30

Sample Input:
2

12

223

Sample Output:
YES

NO

Explanation:
For first test case, It could be encoded as "AB" (1 2) or "L" (12), hence the number of
maximum possible ways are 2 so output is “YES”.
-/

-- <vc-helpers>
-- </vc-helpers>

def count_decodings (s : String) : String := sorry

theorem single_valid_mapping_returns_yes_or_no (n : Nat) 
  (h : 1 ≤ n ∧ n ≤ 26) :
  let s := toString n
  count_decodings s = "YES" ∨ count_decodings s = "NO" := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible