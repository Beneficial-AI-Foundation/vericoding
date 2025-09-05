You are given a string $s[1 \dots n]$ consisting of lowercase Latin letters. It is guaranteed that $n = 2^k$ for some integer $k \ge 0$.

The string $s[1 \dots n]$ is called $c$-good if at least one of the following three conditions is satisfied:  The length of $s$ is $1$, and it consists of the character $c$ (i.e. $s_1=c$); The length of $s$ is greater than $1$, the first half of the string consists of only the character $c$ (i.e. $s_1=s_2=\dots=s_{\frac{n}{2}}=c$) and the second half of the string (i.e. the string $s_{\frac{n}{2} + 1}s_{\frac{n}{2} + 2} \dots s_n$) is a $(c+1)$-good string;  The length of $s$ is greater than $1$, the second half of the string consists of only the character $c$ (i.e. $s_{\frac{n}{2} + 1}=s_{\frac{n}{2} + 2}=\dots=s_n=c$) and the first half of the string (i.e. the string $s_1s_2 \dots s_{\frac{n}{2}}$) is a $(c+1)$-good string. 

For example: "aabc" is 'a'-good, "ffgheeee" is 'e'-good.

In one move, you can choose one index $i$ from $1$ to $n$ and replace $s_i$ with any lowercase Latin letter (any character from 'a' to 'z').

Your task is to find the minimum number of moves required to obtain an 'a'-good string from $s$ (i.e. $c$-good string for $c=$ 'a'). It is guaranteed that the answer always exists.

You have to answer $t$ independent test cases.

Another example of an 'a'-good string is as follows. Consider the string $s = $"cdbbaaaa". It is an 'a'-good string, because:  the second half of the string ("aaaa") consists of only the character 'a';  the first half of the string ("cdbb") is 'b'-good string, because:   the second half of the string ("bb") consists of only the character 'b';  the first half of the string ("cd") is 'c'-good string, because:   the first half of the string ("c") consists of only the character 'c';  the second half of the string ("d") is 'd'-good string.   

-----Input-----

The first line of the input contains one integer $t$ ($1 \le t \le 2 \cdot 10^4$) — the number of test cases. Then $t$ test cases follow.

The first line of the test case contains one integer $n$ ($1 \le n \le 131~072$) — the length of $s$. It is guaranteed that $n = 2^k$ for some integer $k \ge 0$. The second line of the test case contains the string $s$ consisting of $n$ lowercase Latin letters.

It is guaranteed that the sum of $n$ does not exceed $2 \cdot 10^5$ ($\sum n \le 2 \cdot 10^5$).

-----Output-----

For each test case, print the answer — the minimum number of moves required to obtain an 'a'-good string from $s$ (i.e. $c$-good string with $c =$ 'a'). It is guaranteed that the answer exists.

-----Example-----
Input
6
8
bbdcaaaa
8
asdfghjk
8
ceaaaabb
8
bbaaddcc
1
z
2
ac

Output
0
7
4
5
1
1

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible