Given two integers A and B, return any string S such that:

S has length A + B and contains exactly A 'a' letters, and exactly B 'b' letters;
The substring 'aaa' does not occur in S;
The substring 'bbb' does not occur in S.

Example 1:
Input: A = 1, B = 2
Output: "abb"
Explanation: "abb", "bab" and "bba" are all correct answers.

Example 2:
Input: A = 4, B = 1
Output: "aabaa"

Note:

0 <= A <= 100
0 <= B <= 100
It is guaranteed such an S exists for the given A and B.

def strWithout3a3b (a b : Nat) : String :=
  sorry

def count_char (s : String) (c : Char) : Nat :=
  sorry

def contains_substring (s main : String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded