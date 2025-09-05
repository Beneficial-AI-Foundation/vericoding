You are given a non-empty string s consisting of lowercase English letters. You have to pick exactly one non-empty substring of s and shift all its letters 'z' $\rightarrow$ 'y' $\rightarrow$ 'x' $\rightarrow \ldots \rightarrow$ 'b' $\rightarrow$ 'a' $\rightarrow$ 'z'. In other words, each character is replaced with the previous character of English alphabet and 'a' is replaced with 'z'.

What is the lexicographically minimum string that can be obtained from s by performing this shift exactly once?

-----Input-----

The only line of the input contains the string s (1 ≤ |s| ≤ 100 000) consisting of lowercase English letters.

-----Output-----

Print the lexicographically minimum string that can be obtained from s by shifting letters of exactly one non-empty substring.

-----Examples-----
Input
codeforces

Output
bncdenqbdr

Input
abacaba

Output
aaacaba

-----Note-----

String s is lexicographically smaller than some other string t of the same length if there exists some 1 ≤ i ≤ |s|, such that s_1 = t_1, s_2 = t_2, ..., s_{i} - 1 = t_{i} - 1, and s_{i} < t_{i}.

def isLower (c : Char) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
