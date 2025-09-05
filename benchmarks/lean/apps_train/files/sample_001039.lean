Problem description.
Winston and Royce love sharing memes with each other. They express the amount of seconds they laughed ar a meme as the number of ‘XD’ subsequences in their messages. Being optimization freaks, they wanted to find the string with minimum possible length and having exactly the given number of ‘XD’ subsequences.

-----Input-----
- The first line of the input contains an integer T denoting the number of test cases.
- Next T lines contains a single integer N, the no of seconds laughed.

-----Output-----
- 
For each input, print the corresponding string having minimum length. If there are multiple possible answers, print any.

-----Constraints-----
- 1 ≤ T ≤ 1000
- 1 ≤ N ≤ 109
- 1 ≤ Sum of length of output over all testcases ≤ 5*105

-----Example-----
Input:
1
9

Output:
XXXDDD

-----Explanation-----
Some of the possible strings are - XXDDDXD,XXXDDD,XDXXXDD,XDXDXDD etc. Of these, XXXDDD is the smallest.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded