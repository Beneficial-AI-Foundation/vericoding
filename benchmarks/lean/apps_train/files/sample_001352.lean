Dhruvil has always been a studious person and will be completing his Engineering soon. He is always kneen about solving problems and is preparing hard for his next interview at Hackerrank. He has practiced lots of problems and now he came across this problem.
Given a message containing English letters(A-Z), it is being encoded to numbers using the following mapping:
'A' -> 1,'B' -> 2 ……………… 'Z' -> 26.
Now, given a non-empty string containing only digits, help Dhruvil determine the total number of ways to decode it.
While decoding you need to choose a substring of charachters and not a subsequence. Also a chosen substring should not contain any leading "0"s, but can contain trailing "0"s. Since the output can be very large print the answer as modulo 10^9 + 7 i.e 1000000007.

-----Input:-----
The first line of the input consists of single integer T, the number of test cases.
Each test case consists of a string.

-----Output:-----
For each test case print a single integer - the total number of ways to decode the digit string.

-----Constraints-----
- $1 \leq T \leq 1000$
- $2 \leq S \leq 10^9$

-----Sample Input:-----
2
12

226

-----Sample Output:-----
2

3

-----EXPLANATION:-----
There are 2 possible ways. It could be decoded as "AB" {1,2} or "L" {12}.
There are 3 possible ways. It could be decoded as "BZ" {2,26}, "VF" {22,6}, or "BBF" {2,2,6}.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible