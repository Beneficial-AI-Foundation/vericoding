An agent called Cypher is decrypting a message, that contains a composite number $n$. All divisors of $n$, which are greater than $1$, are placed in a circle. Cypher can choose the initial order of numbers in the circle.

In one move Cypher can choose two adjacent numbers in a circle and insert their least common multiple between them. He can do that move as many times as needed.

A message is decrypted, if every two adjacent numbers are not coprime. Note that for such constraints it's always possible to decrypt the message.

Find the minimal number of moves that Cypher should do to decrypt the message, and show the initial order of numbers in the circle for that.

-----Input-----

The first line contains an integer $t$ $(1 \le t \le 100)$ — the number of test cases. Next $t$ lines describe each test case.

In a single line of each test case description, there is a single composite number $n$ $(4 \le n \le 10^9)$ — the number from the message.

It's guaranteed that the total number of divisors of $n$ for all test cases does not exceed $2 \cdot 10^5$.

-----Output-----

For each test case in the first line output the initial order of divisors, which are greater than $1$, in the circle. In the second line output, the minimal number of moves needed to decrypt the message.

If there are different possible orders with a correct answer, print any of them.

-----Example-----
Input
3
6
4
30

Output
2 3 6 
1
2 4 
0
2 30 6 3 15 5 10 
0

-----Note-----

In the first test case $6$ has three divisors, which are greater than $1$: $2, 3, 6$. Regardless of the initial order, numbers $2$ and $3$ are adjacent, so it's needed to place their least common multiple between them. After that the circle becomes $2, 6, 3, 6$, and every two adjacent numbers are not coprime.

In the second test case $4$ has two divisors greater than $1$: $2, 4$, and they are not coprime, so any initial order is correct, and it's not needed to place any least common multiples.

In the third test case all divisors of $30$ greater than $1$ can be placed in some order so that there are no two adjacent numbers that are coprime.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded