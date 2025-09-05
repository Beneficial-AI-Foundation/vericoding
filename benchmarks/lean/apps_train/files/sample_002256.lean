We guessed a permutation $p$ consisting of $n$ integers. The permutation of length $n$ is the array of length $n$ where each element from $1$ to $n$ appears exactly once. This permutation is a secret for you.

For each position $r$ from $2$ to $n$ we chose some other index $l$ ($l < r$) and gave you the segment $p_l, p_{l + 1}, \dots, p_r$ in sorted order (i.e. we rearranged the elements of this segment in a way that the elements of this segment are sorted). Thus, you are given exactly $n-1$ segments of the initial permutation but elements inside each segment are sorted. The segments are given to you in random order.

For example, if the secret permutation is $p=[3, 1, 4, 6, 2, 5]$ then the possible given set of segments can be:  $[2, 5, 6]$  $[4, 6]$  $[1, 3, 4]$  $[1, 3]$  $[1, 2, 4, 6]$ 

Your task is to find any suitable permutation (i.e. any permutation corresponding to the given input data). It is guaranteed that the input data corresponds to some permutation (i.e. such permutation exists).

You have to answer $t$ independent test cases.

-----Input-----

The first line of the input contains one integer $t$ ($1 \le t \le 100$) — the number of test cases. Then $t$ test cases follow.

The first line of the test case contains one integer $n$ ($2 \le n \le 200$) — the length of the permutation.

The next $n-1$ lines describe given segments.

The $i$-th line contains the description of the $i$-th segment. The line starts with the integer $k_i$ ($2 \le k_i \le n$) — the length of the $i$-th segment. Then $k_i$ integers follow. All integers in a line are distinct, sorted in ascending order, between $1$ and $n$, inclusive.

It is guaranteed that the required $p$ exists for each test case.

It is also guaranteed that the sum of $n$ over all test cases does not exceed $200$ ($\sum n \le 200$).

-----Output-----

For each test case, print the answer: $n$ integers $p_1, p_2, \dots, p_n$ ($1 \le p_i \le n$, all $p_i$ should be distinct) — any suitable permutation (i.e. any permutation corresponding to the test case input).

-----Example-----
Input
5
6
3 2 5 6
2 4 6
3 1 3 4
2 1 3
4 1 2 4 6
5
2 2 3
2 1 2
2 1 4
2 4 5
7
3 1 2 6
4 1 3 5 6
2 1 2
3 4 5 7
6 1 2 3 4 5 6
3 1 3 6
2
2 1 2
5
2 2 5
3 2 3 5
4 2 3 4 5
5 1 2 3 4 5

Output
3 1 4 6 2 5 
3 2 1 4 5 
2 1 6 3 5 4 7 
1 2 
2 5 3 4 1

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
