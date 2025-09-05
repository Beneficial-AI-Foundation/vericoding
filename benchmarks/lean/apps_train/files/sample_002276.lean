Mishka wants to buy some food in the nearby shop. Initially, he has $s$ burles on his card. 

Mishka can perform the following operation any number of times (possibly, zero): choose some positive integer number $1 \le x \le s$, buy food that costs exactly $x$ burles and obtain $\lfloor\frac{x}{10}\rfloor$ burles as a cashback (in other words, Mishka spends $x$ burles and obtains $\lfloor\frac{x}{10}\rfloor$ back). The operation $\lfloor\frac{a}{b}\rfloor$ means $a$ divided by $b$ rounded down.

It is guaranteed that you can always buy some food that costs $x$ for any possible value of $x$.

Your task is to say the maximum number of burles Mishka can spend if he buys food optimally.

For example, if Mishka has $s=19$ burles then the maximum number of burles he can spend is $21$. Firstly, he can spend $x=10$ burles, obtain $1$ burle as a cashback. Now he has $s=10$ burles, so can spend $x=10$ burles, obtain $1$ burle as a cashback and spend it too.

You have to answer $t$ independent test cases.

-----Input-----

The first line of the input contains one integer $t$ ($1 \le t \le 10^4$) — the number of test cases.

The next $t$ lines describe test cases. Each test case is given on a separate line and consists of one integer $s$ ($1 \le s \le 10^9$) — the number of burles Mishka initially has.

-----Output-----

For each test case print the answer on it — the maximum number of burles Mishka can spend if he buys food optimally.

-----Example-----
Input
6
1
10
19
9876
12345
1000000000

Output
1
11
21
10973
13716
1111111111

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
