Chef Tobby is playing a rapid fire with Bhuvan. He gives Bhuvan a string S and each time, Bhuvan has to guess whether there exists 2 equal subsequences in the string or not.
Bhuvan got a perfect score in the game with Chef Tobby. However, Chef Tobby has now asked Bhuvan to write a program that will do this automatically given a string S. Bhuvan is an intelligent man but he does not know how to write a code. Can you help him?
Find two different subsequences such that they are equal in their value, more formally, find two sequences of indices (a1, a2, ..., ak-1, ak) and (b1, b2, ..., bk-1, bk) such that:

- 1≤ ai, bi ≤ |S|
- ai < ai+1 for all valid i
- bi < bi+1 for all valid i
- Sai = Sbi for all valid i
- there exist at least one i such that ai is not equal to bi

-----Input section-----
The first line contains T, the number of test cases.
Each of the next T lines contain one string S each.
Input will only consist of lowercase english characters

-----Output section-----
For each test case, output "yes" or "no" (without quotes) as the solution to the problem.

-----Input constraints-----
1 ≤ T ≤ 1000
1 ≤ length of S ≤ 100

-----Sample Input-----
4
likecs
venivedivici
bhuvan
codechef

-----Sample Output-----
no
yes
no
yes

-----Explanation-----
In test case 2, one of the possible equal subsequence is "vi" and "vi". (one at position {0, 3} and other at {4, 7}, assuming 0-based indexing).
In test case 4, one of the possible equal subsequence is "ce" and "ce". (one at position {0, 3} and other at {4, 6}, assuming 0-based indexing).

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded