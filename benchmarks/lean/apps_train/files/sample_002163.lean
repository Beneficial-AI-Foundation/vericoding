You are given a string S consisting of a,b and c. Find the number of strings that can be possibly obtained by repeatedly performing the following operation zero or more times, modulo 998244353:
 - Choose an integer i such that 1\leq i\leq |S|-1 and the i-th and (i+1)-th characters in S are different. Replace each of the i-th and (i+1)-th characters in S with the character that differs from both of them (among a, b and c).

-----Constraints-----
 - 2 \leq |S| \leq 2 × 10^5
 - S consists of a, b and c.

-----Input-----
Input is given from Standard Input in the following format:
S

-----Output-----
Print the number of strings that can be possibly obtained by repeatedly performing the operation, modulo 998244353.

-----Sample Input-----
abc

-----Sample Output-----
3

abc, aaa and ccc can be obtained.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded