This is one more story about our old friend, the Despotic King. Once every year, it was customary for the king to give audience to the rich merchants of his country in a large hall. On that day, the merchants were ushered in to meet the king one by one and after paying their respects to the king they were seated in the auditorium.
It was the job of the minister to introduce each merchant, as he arrived, to the others in the hall. He would announce his name and his wealth. However, our quirky king demanded that in addition, he should also announce the rank of the merchant among all those in the hall (at the time of his arrival) in terms of his wealth.
For example, let us suppose that the wealth of the 6 merchants who met the king (in the order in which they arrived) is given by the sequence
78246840398978246840398978 \quad 24 \quad 68 \quad 40 \quad 39 \quad 89
Then, clearly the first merchant is the richest in the hall when he enters it (since there are no others in the hall) and so his rank is $1$. Since $24 < 78$ the rank of the second merchant when he enters the hall is $2$. The rank of the third merchant is also $2$ since $24 < 68 < 78$. The rank of the fourth merchant is $3$ since $24 < 40 < 68 < 78$, the rank of the fifth merchant is $4$ since $24 < 39 < 40 < 68 < 78$ and finally the rank of the sixth merchant is $1$ since $24 < 39 < 40 < 68 < 78 < 89$. The sequence of ranks announced by the minister would thus be:
1223411223411 \quad 2 \quad 2 \quad 3 \quad 4 \quad 1
Your task is to write a program that takes as input a sequence of distinct positive integers indicating the wealth of the merchants in the order in which they visit the king and outputs the sequence of ranks announced by the minister.

-----Input:-----
The first line contains a single integer $N$ indicating the number of merchants. The next $N$ lines (line $2,...,N+1$) describe the wealth of these $N$ merchants. Line $i+1$ contains a single positive integer indicating the wealth of the $i^{th}$ merchant to enter the hall.

-----Output:-----
Your output should consist of $N$ lines. Line $i$ should be the rank announced when the $i^{th}$ minister enters the hall.

-----Constraints:-----
- $1 \leq N \leq 45000$.
- No two merchants have the same wealth.
- You may also assume that in $30 \%$ of of the inputs $1 \leq N \leq 8000$.

-----Sample Input-----
6
78
24
68
40
39
89

-----Sample Output-----
1
2
2
3
4
1

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
