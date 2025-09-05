You are teaching students to generate strings consisting of unique lowercase latin characters (a-z). You give an example reference string $s$ to the students.
You notice that your students just copy paste the reference string instead of creating their own string. So, you tweak the requirements for strings submitted by the students.
Let us define a function F(s, t) where s and t are strings as the number of characters that are same in both the strings. Note that the position doesn't matter. Here are a few examples of F(s, t):
F("abc", "def") = 0
F("abc", "acb") = 3
F("back", "abcd") = 3
Now you ask your students to output a string t with lowercase unique characters of the same length as $s$, such that F(s, t) $\leq k$ where you are also given the value of $k$. If there are multiple such strings, you ask them to output the lexicographically smallest possible string. If no such string is possible, output the string "NOPE" without quotes.

-----Input:-----
- The first line will contain $T$, the number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, which contains a string $s$ and an integer $k$.

-----Output:-----
For each testcase, output in a single line the lexicographically smallest string t such that F(s, t) <= k or "NOPE" without quotes if no such string exists.

-----Constraints-----
- $1 \leq T \leq 10000$
- $1 \leq $length of string s $(|s|) \leq 26$
- $s$ only consists of characters $a$ to $z$
- There are no repeating characters in s
- $0 \leq k \leq |s|$

-----Sample Input:-----
4
helowrd 0
background 0
abcdefghijklmnopqrstuvwxyz 0
b 1

-----Sample Output:-----
abcfgij
efhijlmpqs
NOPE
a

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
