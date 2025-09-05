Hooray! Polycarp turned $n$ years old! The Technocup Team sincerely congratulates Polycarp!

Polycarp celebrated all of his $n$ birthdays: from the $1$-th to the $n$-th. At the moment, he is wondering: how many times he turned beautiful number of years?

According to Polycarp, a positive integer is beautiful if it consists of only one digit repeated one or more times. For example, the following numbers are beautiful: $1$, $77$, $777$, $44$ and $999999$. The following numbers are not beautiful: $12$, $11110$, $6969$ and $987654321$.

Of course, Polycarpus uses the decimal numeral system (i.e. radix is 10).

Help Polycarpus to find the number of numbers from $1$ to $n$ (inclusive) that are beautiful.

-----Input-----

The first line contains an integer $t$ ($1 \le t \le 10^4$) — the number of test cases in the input. Then $t$ test cases follow.

Each test case consists of one line, which contains a positive integer $n$ ($1 \le n \le 10^9$) — how many years Polycarp has turned.

-----Output-----

Print $t$ integers — the answers to the given test cases in the order they are written in the test. Each answer is an integer: the number of beautiful years between $1$ and $n$, inclusive.

-----Example-----
Input
6
18
1
9
100500
33
1000000000

Output
10
1
9
45
12
81

-----Note-----

In the first test case of the example beautiful years are $1$, $2$, $3$, $4$, $5$, $6$, $7$, $8$, $9$ and $11$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible