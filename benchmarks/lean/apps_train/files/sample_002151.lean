Konrad is a Human Relations consultant working for VoltModder, a large electrical equipment producer. Today, he has been tasked with evaluating the level of happiness in the company.

There are $n$ people working for VoltModder, numbered from $1$ to $n$. Each employee earns a different amount of money in the company — initially, the $i$-th person earns $i$ rubles per day.

On each of $q$ following days, the salaries will be revised. At the end of the $i$-th day, employee $v_i$ will start earning $n+i$ rubles per day and will become the best-paid person in the company. The employee will keep his new salary until it gets revised again.

Some pairs of people don't like each other. This creates a great psychological danger in the company. Formally, if two people $a$ and $b$ dislike each other and $a$ earns more money than $b$, employee $a$ will brag about this to $b$. A dangerous triple is a triple of three employees $a$, $b$ and $c$, such that $a$ brags to $b$, who in turn brags to $c$. If $a$ dislikes $b$, then $b$ dislikes $a$.

At the beginning of each day, Konrad needs to evaluate the number of dangerous triples in the company. Can you help him do it?

-----Input-----

The first line contains two integers $n$ and $m$ ($1 \le n \le 100\,000$, $0 \le m \le 100\,000$) — the number of employees in the company and the number of pairs of people who don't like each other. Each of the following $m$ lines contains two integers $a_i$, $b_i$ ($1 \le a_i, b_i \le n$, $a_i \neq b_i$) denoting that employees $a_i$ and $b_i$ hate each other (that is, $a_i$ dislikes $b_i$ and $b_i$ dislikes $a_i$). Each such relationship will be mentioned exactly once.

The next line contains an integer $q$ ($0 \le q \le 100\,000$) — the number of salary revisions. The $i$-th of the following $q$ lines contains a single integer $v_i$ ($1 \le v_i \le n$) denoting that at the end of the $i$-th day, employee $v_i$ will earn the most.

-----Output-----

Output $q + 1$ integers. The $i$-th of them should contain the number of dangerous triples in the company at the beginning of the $i$-th day.

-----Examples-----
Input
4 5
1 2
2 4
1 3
3 4
2 3
2
2
3

Output
4
3
2

Input
3 3
1 2
2 3
1 3
5
1
2
2
1
3

Output
1
1
1
1
1
1

-----Note-----

Consider the first sample test. The $i$-th row in the following image shows the structure of the company at the beginning of the $i$-th day. A directed edge from $a$ to $b$ denotes that employee $a$ brags to employee $b$. The dangerous triples are marked by highlighted edges. [Image]

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible
