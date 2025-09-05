Limak has a string S, that consists of N lowercase English letters.
Limak then created a new string by repeating S exactly K times.
For example, for S = "abcb" and K = 2, he would get "abcbabcb".
Your task is to count the number of subsequences "ab" (not necessarily consecutive) in the new string.
In other words, find the number pairs of indices i < j, such that the i-th and j-th characters in the new string are 'a' and 'b' respectively.

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.
The first line of each test case contains two integers N and K, denoting the length of the initial string S and the number of repetitions respectively.
The second line contains a string S.
Its length is exactly N, and each of its characters is a lowercase English letter.

-----Output-----
For each test case, output a single line containing one integer — the number of subsequences "ab" in the new string.
For the given constraints, it can be proved that the answer fits in the 64-bit signed type.

-----Constraints-----
- 1 ≤ T ≤ 10
- 1 ≤ N ≤ 105
- 1 ≤ N * K ≤ 109 (in other words, the new string has length up to 109)

-----Example-----
Input:
3
4 2
abcb
7 1
aayzbaa
12 80123123
abzbabzbazab

Output:
6
2
64197148392731290

-----Explanation-----
Test case 1. Limak repeated the string "abcb" 2 times, and so he got "abcbabcb". There are 6 occurrences of the subsequence "ab":
- ABcbabcb (the two letters marked uppercase)
- AbcBabcb
- AbcbaBcb
- AbcbabcB
- abcbABcb
- abcbAbcB
Test case 2. Since K = 1, the new string is equal to the given S ("aayzbaa"). There are 2 occurrences of the subsequence "ab" in this string: AayzBaa and aAyzBaa.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
