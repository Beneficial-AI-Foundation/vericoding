Cengiz recently learned Fibonacci numbers and now he is studying different algorithms to find them. After getting bored of reading them, he came with his own new type of numbers that he named XORinacci numbers. He defined them as follows:   $f(0) = a$;  $f(1) = b$;  $f(n) = f(n-1) \oplus f(n-2)$ when $n > 1$, where $\oplus$ denotes the bitwise XOR operation. 

You are given three integers $a$, $b$, and $n$, calculate $f(n)$.

You have to answer for $T$ independent test cases.

-----Input-----

The input contains one or more independent test cases.

The first line of input contains a single integer $T$ ($1 \le T \le 10^3$), the number of test cases.

Each of the $T$ following lines contains three space-separated integers $a$, $b$, and $n$ ($0 \le a, b, n \le 10^9$) respectively.

-----Output-----

For each test case, output $f(n)$.

-----Example-----
Input
3
3 4 2
4 5 0
325 265 1231232

Output
7
4
76

-----Note-----

In the first example, $f(2) = f(0) \oplus f(1) = 3 \oplus 4 = 7$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible
