It's Christmas time and Santa is in town. There are N children each having a bag with a mission to fill in as many toffees as possible. They are accompanied by a teacher whose ulterior motive is to test their counting skills. The toffees are of different brands (denoted by lowercase letters a-z). Santa picks up a child numbered m and gives n toffees of brand p to the child.

The teacher wishes to ask the children to calculate the number of toffees there are of a particular brand amongst a given range of children. Formally, there are 2 queries:

Input:

First line consists of Q queries.

Each line follows and consists of four space separated values:

Type 1: It is of the form 1 m x p

1 is the type no,"m" is the child to which "x" toffees of a brand "p" are given

Type 2: It is of the form 2 m n p
where m - n is the range of children (inclusive) being queried for brand p

Output:

Report the sum of toffees of brand p within the given range m - n for each query of type 2

Constraints:

1 <= Q <= 10^5

1 <= N <= 10^6

1 <= m <= n <= 10^6

1 <= x <= 10^6

all brand of toffees are lowercase letters

Subtask 1: (30 points)

1 <= Q <= 10^3

1 <= m <= n <= 10^3

1 <= x <= 10^3

Subtask 2: (70 points)

Original Constraints

Sample Input:

5

1 3 4 a

1 5 8 a

1 1 7 x

2 1 6 a

2 3 6 y

Sample Output:

12

0

In first case, there are two children between 3 and 5 between 0 - 6  having sum (4 + 8)

There's no toffee for y in given range

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded