For a string $S$ let the unique set of characters that occur in it one or more times be $C$. Consider a permutation of the elements of $C$ as $(c_1, c_2, c_3 ... )$. Let $f(c)$ be the number of times $c$ occurs in $S$.
If any such permutation of the elements of $C$ satisfies $f(c_i) = f(c_{i-1}) + f(c_{i-2})$ for all $i \ge 3$, the string is said to be a dynamic string.
Mr Bancroft is given the task to check if the string is dynamic, but he is busy playing with sandpaper. Would you help him in such a state?
Note that if the number of distinct characters in the string is less than 3, i.e. if $|C| < 3$, then the string is always dynamic.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, a string $S$.

-----Output:-----
For each testcase, output in a single line "Dynamic" if the given string is dynamic, otherwise print "Not". (Note that the judge is case sensitive)

-----Constraints-----
- $1 \leq T \leq 10$
- $1 \leq |S| \leq 10^5$
- $S$ contains only lower case alphabets: $a$, $b$, …, $z$

-----Sample Input:-----
3
aaaabccc
aabbcc
ppppmmnnoooopp

-----Sample Output:-----
Dynamic
Not
Dynamic

-----Explanation:-----
- Testase 1: For the given string, $C = \{a, b, c\}$ and $f(a)=4, f(b)=1, f(c)=3$. $f(a) = f(c) + f(b)$ so the permutation $(b, c, a)$ satisfies the requirement.
- Testcase 2: Here too $C = \{a, b, c\}$ but no permutation satisfies the requirement of a dynamic string.
- Testcase 3: Here $C = \{m, n, o, p\}$ and $(m, n, o, p)$ is a permutation that makes it a dynamic string.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
