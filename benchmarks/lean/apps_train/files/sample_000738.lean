Saket loves to play with strings. One day , while he was having fun with Cyclic Permutations of available strings to him, he observed that despite being scarce in numbers Vowels were really clingy.Being clingy means for almost every given string, there was a Cyclic Permutation in which atleast two vowels were together.
So he decided to check this property for all the available strings to him. As the number of strings can be very large, help Saket determine whether the given string is clingy or not.

-----Input:-----
The first line of the input contains a single integer T$T$ denoting the number of test cases. The description of T$T$ test cases follows.
First line of every test case contains an integer N$N$ denoting the length of the string.
Second line contains a string S$S$ of length N$N$, consisting only of uppercase english alphabets.

-----Output:-----
For each test case, print a single line containing "Yes" if any of the cyclic permutations of the string is clingy else print "No".

-----Constraints-----
- 1≤T≤1000$1 \leq T \leq 1000$
- 1≤N≤1000$1 \leq N \leq 1000$
- String S$S$ consists of only upper case english alphabets.

-----Subtasks-----
- 20 points : 1≤N≤5$1 \leq N \leq 5$
- 80 points : Original$Original$ Constraints$Constraints$

-----Sample Input:-----
2
5
AUXFC
6
XBCDEF

-----Sample Output:-----
Yes

No

-----EXPLANATION:-----
Example$Example$ case1:$ case 1: $ One of the cyclic permutation is the original string itself, which has "A" and "U" together.
Example$Example$ case2:$ case 2: $     None of the cyclic permutation will have 2 vowels together.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
