Consider the following process. You have a binary string (a string where each character is either 0 or 1) $w$ of length $n$ and an integer $x$. You build a new binary string $s$ consisting of $n$ characters. The $i$-th character of $s$ is chosen as follows:

  if the character $w_{i-x}$ exists and is equal to 1, then $s_i$ is 1 (formally, if $i > x$ and $w_{i-x} = $ 1, then $s_i = $ 1);  if the character $w_{i+x}$ exists and is equal to 1, then $s_i$ is 1 (formally, if $i + x \le n$ and $w_{i+x} = $ 1, then $s_i = $ 1);  if both of the aforementioned conditions are false, then $s_i$ is 0. 

You are given the integer $x$ and the resulting string $s$. Reconstruct the original string $w$.

-----Input-----

The first line contains one integer $t$ ($1 \le t \le 1000$) — the number of test cases.

Each test case consists of two lines. The first line contains the resulting string $s$ ($2 \le |s| \le 10^5$, each character of $s$ is either 0 or 1). The second line contains one integer $x$ ($1 \le x \le |s| - 1$).

The total length of all strings $s$ in the input does not exceed $10^5$.

-----Output-----

For each test case, print the answer on a separate line as follows:

  if no string $w$ can produce the string $s$ at the end of the process, print $-1$;  otherwise, print the binary string $w$ consisting of $|s|$ characters. If there are multiple answers, print any of them. 

-----Example-----
Input
3
101110
2
01
1
110
1

Output
111011
10
-1

def length_eq (s₁ s₂ : BinaryString) : Prop := sorry
def is_binary (s : BinaryString) : Prop := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded