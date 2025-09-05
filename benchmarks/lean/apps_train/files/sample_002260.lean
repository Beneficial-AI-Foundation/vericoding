This problem is a version of problem D from the same contest with some additional constraints and tasks.

There are $n$ candies in a candy box. The type of the $i$-th candy is $a_i$ ($1 \le a_i \le n$). 

You have to prepare a gift using some of these candies with the following restriction: the numbers of candies of each type presented in a gift should be all distinct (i. e. for example, a gift having two candies of type $1$ and two candies of type $2$ is bad).

It is possible that multiple types of candies are completely absent from the gift. It is also possible that not all candies of some types will be taken to a gift.

You really like some of the candies and don't want to include them into the gift, but you want to eat them yourself instead. For each candy, a number $f_i$ is given, which is equal to $0$ if you really want to keep $i$-th candy for yourself, or $1$ if you don't mind including it into your gift. It is possible that two candies of the same type have different values of $f_i$.

You want your gift to be as large as possible, but you don't want to include too many of the candies you want to eat into the gift. So, you want to calculate the maximum possible number of candies that can be included into a gift, and among all ways to choose maximum number of candies, you want to maximize the number of candies having $f_i = 1$ in your gift.

You have to answer $q$ independent queries.

If you are Python programmer, consider using PyPy instead of Python when you submit your code.

-----Input-----

The first line of the input contains one integer $q$ ($1 \le q \le 2 \cdot 10^5$) — the number of queries.

The first line of each query contains one integer $n$ ($1 \le n \le 2 \cdot 10^5$) — the number of candies.

Then $n$ lines follow, each containing two integers $a_i$ and $f_i$ ($1 \le a_i \le n$, $0 \le f_i \le 1$), where $a_i$ is the type of the $i$-th candy, and $f_i$ denotes whether you want to keep the $i$-th candy for yourself ($0$ if you want to keep it, $1$ if you don't mind giving it away).

It is guaranteed that the sum of $n$ over all queries does not exceed $2 \cdot 10^5$.

-----Output-----

For each query print two integers:

  the maximum number of candies in a gift you can compose, according to the constraints in the statement;  the maximum number of candies having $f_i = 1$ in a gift you can compose that contains the maximum possible number of candies.  

-----Example-----
Input
3
8
1 0
4 1
2 0
4 1
5 1
6 1
3 0
2 0
4
1 1
1 1
2 1
2 1
9
2 0
2 0
4 1
4 1
4 1
7 0
7 1
7 0
7 1

Output
3 3
3 3
9 5

-----Note-----

In the first query, you can include two candies of type $4$ and one candy of type $5$. All of them have $f_i = 1$ and you don't mind giving them away as part of the gift.

def List.sum : List Nat → Nat 
  | [] => 0
  | x :: xs => x + sum xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
