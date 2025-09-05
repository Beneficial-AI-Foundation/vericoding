A sequence of integers ($a_1, a_2, \ldots, a_k$) is said to be UpDown, if these inequalities hold true:
- $a_1 \le a_2$
- $a_2 \ge a_3$
- $a_3 \le a_4$
and so on.
That is, every even-indexed element should be at least as large as its adjacent elements. And every odd-indexed element should be at most as large as its adjacent elements. Formally, $a_{2i} \ge a_{2i+1}$ and $a_{2i+1} \le a_{2i+2}$, for all valid positions.
A subsegment is a consecutive portion of a sequence. That is, a subsegment of ($b_1, b_2, \ldots, b_k$)  will be of the form ($b_i, b_{i+1}, \ldots, b_j$), for some $i$ and $j$.
You are given a sequence ($s_1, s_2, \ldots, s_n$). You can insert at most one integer anywhere in this sequence. It could be any integer. After inserting an integer (or choosing not to), suppose you have the new sequence ($t_1, t_2, \ldots, t_m$). Note that $m$ will either be $n$+1 or $n$. You want to maximize the length of the longest subsegment of ($t_1, t_2, \ldots, t_m$) which is UpDown, and output the length of that.

-----Input-----
- The first line contains a single integer, $T$, which is the number of testcases. The description of each testcase follows.
- The first line of every testcase contains a single integer, $n$, which is the number of integers in the original sequence.
- The second line contains $n$ integers: $s_1, s_2, \ldots, s_n$, which forms the original sequence.

-----Output-----
For each testcase output a single line containing one integer, which should be the length of the longest UpDown subsegment that you can get after inserting at most one integer.

-----Constraints-----
- $1 \le T \le 2$
- $1 \le n \le 10^6$
- $1 \le s_i \le 10^9$

-----Subtasks-----
Subtask #1 (20 points): $1 \le n \le 100$
Subtask #2 (10 points): $1 \le n \le 10000$
Subtask #3 (70 points): Original constraints

-----Sample Input-----
2
7
100 1 10 3 20 25 24
5
3 3 2 4 1

-----Sample Output-----
7
6

-----Explanation-----
Testcase 1: The original sequence is (100, 1, 10, 3, 20, 25, 24). Suppose you insert the element 5 between the elements 20 and 25, you will get the new sequence (100, 1, 10, 3, 20, 5, 25, 24). The longest UpDown subsegment of this sequence is (1, 10, 3, 20, 5, 25, 24), whose length is 7. You can check that you cannot do any better, and hence the answer is 7.
Testcase 2: The original sequence is (3, 3, 2, 4, 1). Suppose you insert the element 4 at the end, you will get the new sequence (3, 3, 2, 4, 1, 4). This entire sequence is UpDown, and so the longest UpDown subsegment of this sequence is (3, 3, 2, 4, 1, 4), whose length is 6. You can check that you cannot do any better, and hence the answer is 6.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded