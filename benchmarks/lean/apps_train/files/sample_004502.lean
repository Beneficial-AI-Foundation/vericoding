You are given four positive integers $n$, $m$, $a$, $b$ ($1 \le b \le n \le 50$; $1 \le a \le m \le 50$). Find any such rectangular matrix of size $n \times m$ that satisfies all of the following conditions:

  each row of the matrix contains exactly $a$ ones;  each column of the matrix contains exactly $b$ ones;  all other elements are zeros. 

If the desired matrix does not exist, indicate this.

For example, for $n=3$, $m=6$, $a=2$, $b=1$, there exists a matrix satisfying the conditions above:

$$ \begin{vmatrix} 0 & 1 & 0 & 0 & 0 & 1 \\ 1 & 0 & 0 & 1 & 0 & 0 \\ 0 & 0 & 1 & 0 & 1 & 0 \end{vmatrix} $$

-----Input-----

The first line contains an integer $t$ ($1 \le t \le 1000$) — the number of test cases. Then $t$ test cases follow.

Each test case is described by four positive integers $n$, $m$, $a$, $b$ ($1 \le b \le n \le 50$; $1 \le a \le m \le 50$), where $n$ and $m$ are the sizes of the matrix, and $a$ and $b$ are the number of ones for rows and columns, respectively.

-----Output-----

For each test case print:

  "YES" (without quotes) and the required matrix (if there are several answers, print any) if it exists, or  "NO" (without quotes) if it does not exist. 

To print the matrix $n \times m$, print $n$ rows, each of which consists of $m$ numbers $0$ or $1$ describing a row of the matrix. Numbers must be printed without spaces.

-----Example-----
Input
5
3 6 2 1
2 2 2 1
2 2 2 2
4 4 2 2
2 1 1 2

Output
YES
010001
100100
001010
NO
YES
11
11
YES
1100
1100
0011
0011
YES
1
1

def Matrix := List (List Bool)

def solveMatrix (m n a b : Nat) : Option Matrix :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
