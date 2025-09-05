Polycarp analyzes the prices of the new berPhone. At his disposal are the prices for $n$ last days: $a_1, a_2, \dots, a_n$, where $a_i$ is the price of berPhone on the day $i$.

Polycarp considers the price on the day $i$ to be bad if later (that is, a day with a greater number) berPhone was sold at a lower price. For example, if $n=6$ and $a=[3, 9, 4, 6, 7, 5]$, then the number of days with a bad price is $3$ — these are days $2$ ($a_2=9$), $4$ ($a_4=6$) and $5$ ($a_5=7$).

Print the number of days with a bad price.

You have to answer $t$ independent data sets.

-----Input-----

The first line contains an integer $t$ ($1 \le t \le 10000$) — the number of sets of input data in the test. Input data sets must be processed independently, one after another.

Each input data set consists of two lines. The first line contains an integer $n$ ($1 \le n \le 150000$) — the number of days. The second line contains $n$ integers $a_1, a_2, \dots, a_n$ ($1 \le a_i \le 10^6$), where $a_i$ is the price on the $i$-th day.

It is guaranteed that the sum of $n$ over all data sets in the test does not exceed $150000$.

-----Output-----

Print $t$ integers, the $j$-th of which should be equal to the number of days with a bad price in the $j$-th input data set.

-----Example-----
Input
5
6
3 9 4 6 7 5
1
1000000
2
2 1
10
31 41 59 26 53 58 97 93 23 84
7
3 2 1 2 3 4 5

Output
3
0
1
8
2

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible