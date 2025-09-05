Alice likes prime numbers. According to Alice, only those strings are nice whose sum of character values at a prime position is prime. She has a string $S$. Now, she has to count the number of nice strings which come before string $S$( including $S$) in the dictionary and are of the same length as $S$. 
Strings are zero-indexed from left to right.
To find the character value she uses the mapping {'a': 0, 'b':1, 'c':2 ……. 'y': 24, 'z':25} .
For example, for string $abcde$ Characters at prime positions are $'c'$ and $'d'$. c + d = 2 + 3 = 5. Since, 5 is a prime number, the string is $nice$.
Since there could be many nice strings print the answer modulo $10^{9}+7$.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, the string $S$. 

-----Output:-----
For each testcase, output in a single line number of nice strings modulo $10^{9}+7$.

-----Constraints-----
- $1 \leq T \leq 10$
- $2 \leq |S| \leq 10^2$
String $S$ contains only lowercase letters.

-----Sample Input:-----
1
abc

-----Sample Output:-----
10

def is_nice (s: List Char) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded