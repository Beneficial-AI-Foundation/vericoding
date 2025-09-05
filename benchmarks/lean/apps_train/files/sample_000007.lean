The only difference between easy and hard versions is constraints.

Now elections are held in Berland and you want to win them. More precisely, you want everyone to vote for you.

There are $n$ voters, and two ways to convince each of them to vote for you. The first way to convince the $i$-th voter is to pay him $p_i$ coins. The second way is to make $m_i$ other voters vote for you, and the $i$-th voter will vote for free.

Moreover, the process of such voting takes place in several steps. For example, if there are five voters with $m_1 = 1$, $m_2 = 2$, $m_3 = 2$, $m_4 = 4$, $m_5 = 5$, then you can buy the vote of the fifth voter, and eventually everyone will vote for you. Set of people voting for you will change as follows: ${5} \rightarrow {1, 5} \rightarrow {1, 2, 3, 5} \rightarrow {1, 2, 3, 4, 5}$.

Calculate the minimum number of coins you have to spend so that everyone votes for you.

-----Input-----

The first line contains one integer $t$ ($1 \le t \le 2 \cdot 10^5$) — the number of test cases.

The first line of each test case contains one integer $n$ ($1 \le n \le 2 \cdot 10^5$) — the number of voters.

The next $n$ lines contains the description of voters. $i$-th line contains two integers $m_i$ and $p_i$ ($1 \le p_i \le 10^9, 0 \le m_i < n$).

It is guaranteed that the sum of all $n$ over all test cases does not exceed $2 \cdot 10^5$.

-----Output-----

For each test case print one integer — the minimum number of coins you have to spend so that everyone votes for you.

-----Example-----
Input
3
3
1 5
2 10
2 8
7
0 1
3 1
1 1
6 1
1 1
4 1
4 1
6
2 6
2 3
2 8
2 7
4 4
5 5

Output
8
0
7

-----Note-----

In the first test case you have to buy vote of the third voter. Then the set of people voting for you will change as follows: ${3} \rightarrow {1, 3} \rightarrow {1, 2, 3}$.

In the second example you don't need to buy votes. The set of people voting for you will change as follows: ${1} \rightarrow {1, 3, 5} \rightarrow {1, 2, 3, 5} \rightarrow {1, 2, 3, 5, 6, 7} \rightarrow {1, 2, 3, 4, 5, 6, 7}$.

In the third test case you have to buy votes of the second and the fifth voters. Then the set of people voting for you will change as follows: ${2, 5} \rightarrow {1, 2, 3, 4, 5} \rightarrow {1, 2, 3, 4, 5, 6}$.

def Heap := List Int

def ins (l : Heap) (x : Int) : Heap := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
