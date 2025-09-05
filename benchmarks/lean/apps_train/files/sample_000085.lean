Alexandra has an even-length array $a$, consisting of $0$s and $1$s. The elements of the array are enumerated from $1$ to $n$. She wants to remove at most $\frac{n}{2}$ elements (where $n$ — length of array) in the way that alternating sum of the array will be equal $0$ (i.e. $a_1 - a_2 + a_3 - a_4 + \dotsc = 0$). In other words, Alexandra wants sum of all elements at the odd positions and sum of all elements at the even positions to become equal. The elements that you remove don't have to be consecutive.

For example, if she has $a = [1, 0, 1, 0, 0, 0]$ and she removes $2$nd and $4$th elements, $a$ will become equal $[1, 1, 0, 0]$ and its alternating sum is $1 - 1 + 0 - 0 = 0$.

Help her!

-----Input-----

Each test contains multiple test cases. The first line contains the number of test cases $t$ ($1 \le t \le 10^3$). Description of the test cases follows.

The first line of each test case contains a single integer $n$ ($2 \le n \le 10^3$, $n$ is even)  — length of the array.

The second line contains $n$ integers $a_1, a_2, \ldots, a_n$ ($0 \le a_i \le 1$)  — elements of the array.

It is guaranteed that the sum of $n$ over all test cases does not exceed $10^3$.

-----Output-----

For each test case, firstly, print $k$ ($\frac{n}{2} \leq k \leq n$) — number of elements that will remain after removing in the order they appear in $a$. Then, print this $k$ numbers. Note that you should print the numbers themselves, not their indices.

We can show that an answer always exists. If there are several answers, you can output any of them. 

-----Example-----
Input
4
2
1 0
2
0 0
4
0 1 1 1
4
1 1 0 0

Output
1
0
1
0
2
1 1
4
1 1 0 0

-----Note-----

In the first and second cases, alternating sum of the array, obviously, equals $0$.

In the third case, alternating sum of the array equals $1 - 1 = 0$.

In the fourth case, alternating sum already equals $1 - 1 + 0 - 0 = 0$, so we don't have to remove anything.

def List.sum : List Nat → Nat 
| [] => 0
| x::xs => x + (sum xs)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded