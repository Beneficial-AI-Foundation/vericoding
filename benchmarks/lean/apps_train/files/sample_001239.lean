Chef likes prime numbers. However, there is one thing he loves even more. Of course, it's semi-primes! A semi-prime number is an integer which can be expressed as a product of two distinct primes. For example, $15 = 3 \cdot 5$ is a semi-prime number, but $1$, $9 = 3 \cdot 3$ and $5$ are not.
Chef is wondering how to check if an integer can be expressed as a sum of two (not necessarily distinct) semi-primes. Help Chef with this tough task!

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains a single integer $N$.

-----Output-----
For each test case, print a single line containing the string "YES" if it is possible to express $N$ as a sum of two semi-primes or "NO" otherwise.

-----Constraints-----
- $1 \le T \le 200$
- $1 \le N \le 200$

-----Example Input-----
3
30
45
62

-----Example Output-----
YES
YES
NO

-----Explanation-----
Example case 1: $N=30$ can be expressed as $15 + 15 = (3 \cdot 5) + (3 \cdot 5)$.
Example case 2: $45$ can be expressed as $35 + 10 = (5 \cdot 7) + (2 \cdot 5)$.
Example case 3: $62$ cannot be expressed as a sum of two semi-primes.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded