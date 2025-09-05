This is an easier version of the next problem. In this version, $q = 0$.

A sequence of integers is called nice if its elements are arranged in blocks like in $[3, 3, 3, 4, 1, 1]$. Formally, if two elements are equal, everything in between must also be equal.

Let's define difficulty of a sequence as a minimum possible number of elements to change to get a nice sequence. However, if you change at least one element of value $x$ to value $y$, you must also change all other elements of value $x$ into $y$ as well. For example, for $[3, 3, 1, 3, 2, 1, 2]$ it isn't allowed to change first $1$ to $3$ and second $1$ to $2$. You need to leave $1$'s untouched or change them to the same value.

You are given a sequence of integers $a_1, a_2, \ldots, a_n$ and $q$ updates.

Each update is of form "$i$ $x$" — change $a_i$ to $x$. Updates are not independent (the change stays for the future).

Print the difficulty of the initial sequence and of the sequence after every update.

-----Input-----

The first line contains integers $n$ and $q$ ($1 \le n \le 200\,000$, $q = 0$), the length of the sequence and the number of the updates.

The second line contains $n$ integers $a_1, a_2, \ldots, a_n$ ($1 \le a_i \le 200\,000$), the initial sequence.

Each of the following $q$ lines contains integers $i_t$ and $x_t$ ($1 \le i_t \le n$, $1 \le x_t \le 200\,000$), the position and the new value for this position.

-----Output-----

Print $q+1$ integers, the answer for the initial sequence and the answer after every update.

-----Examples-----
Input
5 0
3 7 3 7 3

Output
2

Input
10 0
1 2 1 2 3 1 1 1 50 1

Output
4

Input
6 0
6 6 3 3 4 4

Output
0

Input
7 0
3 3 1 3 2 1 2

Output
4

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
