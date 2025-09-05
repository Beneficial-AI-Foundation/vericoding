Greg has an array a = a_1, a_2, ..., a_{n} and m operations. Each operation looks as: l_{i}, r_{i}, d_{i}, (1 ≤ l_{i} ≤ r_{i} ≤ n). To apply operation i to the array means to increase all array elements with numbers l_{i}, l_{i} + 1, ..., r_{i} by value d_{i}.

Greg wrote down k queries on a piece of paper. Each query has the following form: x_{i}, y_{i}, (1 ≤ x_{i} ≤ y_{i} ≤ m). That means that one should apply operations with numbers x_{i}, x_{i} + 1, ..., y_{i} to the array.

Now Greg is wondering, what the array a will be after all the queries are executed. Help Greg.

-----Input-----

The first line contains integers n, m, k (1 ≤ n, m, k ≤ 10^5). The second line contains n integers: a_1, a_2, ..., a_{n} (0 ≤ a_{i} ≤ 10^5) — the initial array.

Next m lines contain operations, the operation number i is written as three integers: l_{i}, r_{i}, d_{i}, (1 ≤ l_{i} ≤ r_{i} ≤ n), (0 ≤ d_{i} ≤ 10^5).

Next k lines contain the queries, the query number i is written as two integers: x_{i}, y_{i}, (1 ≤ x_{i} ≤ y_{i} ≤ m).

The numbers in the lines are separated by single spaces.

-----Output-----

On a single line print n integers a_1, a_2, ..., a_{n} — the array after executing all the queries. Separate the printed numbers by spaces.

Please, do not use the %lld specifier to read or write 64-bit integers in C++. It is preferred to use the cin, cout streams of the %I64d specifier.

-----Examples-----
Input
3 3 3
1 2 3
1 2 1
1 3 2
2 3 4
1 2
1 3
2 3

Output
9 18 17

Input
1 1 1
1
1 1 1
1 1

Output
2

Input
4 3 6
1 2 3 4
1 2 1
2 3 2
3 4 4
1 2
1 3
2 3
1 2
1 3
2 3

Output
5 18 31 20

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
