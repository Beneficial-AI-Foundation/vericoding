You are given a string A. Find a string B, where B is a palindrome and A is a subsequence of B.

A subsequence of a string is a string that can be derived from it by deleting some (not necessarily consecutive) characters without changing the order of the remaining characters. For example, "cotst" is a subsequence of "contest".

A palindrome is a string that reads the same forward or backward.

The length of string B should be at most 10^4. It is guaranteed that there always exists such string.

You do not need to find the shortest answer, the only restriction is that the length of string B should not exceed 10^4.

-----Input-----

First line contains a string A (1 ≤ |A| ≤ 10^3) consisting of lowercase Latin letters, where |A| is a length of A.

-----Output-----

Output single line containing B consisting of only lowercase Latin letters. You do not need to find the shortest answer, the only restriction is that the length of string B should not exceed 10^4. If there are many possible B, print any of them.

-----Examples-----
Input
aba

Output
aba
Input
ab

Output
aabaa

-----Note-----

In the first example, "aba" is a subsequence of "aba" which is a palindrome.

In the second example, "ab" is a subsequence of "aabaa" which is a palindrome.

def isPalindrome (s : String) : Bool := sorry

def isSubsequence (sub orig : String) : Bool := sorry

def startsWithStr (s pre : String) : Bool := sorry

/-- Function that finds a palindrome supersequence of a given string -/

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
