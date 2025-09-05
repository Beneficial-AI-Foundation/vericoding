You are given a string S of length n with each character being one of the first m lowercase English letters. 

Calculate how many different strings T of length n composed from the first m lowercase English letters exist such that the length of LCS (longest common subsequence) between S and T is n - 1.

Recall that LCS of two strings S and T is the longest string C such that C both in S and T as a subsequence.

-----Input-----

The first line contains two numbers n and m denoting the length of string S and number of first English lowercase characters forming the character set for strings (1 ≤ n ≤ 100 000, 2 ≤ m ≤ 26).

The second line contains string S.

-----Output-----

Print the only line containing the answer.

-----Examples-----
Input
3 3
aaa

Output
6

Input
3 3
aab

Output
11

Input
1 2
a

Output
1

Input
10 9
abacadefgh

Output
789

-----Note-----

For the first sample, the 6 possible strings T are: aab, aac, aba, aca, baa, caa. 

For the second sample, the 11 possible strings T are: aaa, aac, aba, abb, abc, aca, acb, baa, bab, caa, cab.

For the third sample, the only possible string T is b.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded