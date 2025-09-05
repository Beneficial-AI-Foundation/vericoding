Alice and Bob play a game. They have a binary string $s$ (a string such that each character in it is either $0$ or $1$). Alice moves first, then Bob, then Alice again, and so on.

During their move, the player can choose any number (not less than one) of consecutive equal characters in $s$ and delete them.

For example, if the string is $10110$, there are $6$ possible moves (deleted characters are bold):  $\textbf{1}0110 \to 0110$;  $1\textbf{0}110 \to 1110$;  $10\textbf{1}10 \to 1010$;  $101\textbf{1}0 \to 1010$;  $10\textbf{11}0 \to 100$;  $1011\textbf{0} \to 1011$. 

After the characters are removed, the characters to the left and to the right of the removed block become adjacent. I. e. the following sequence of moves is valid: $10\textbf{11}0 \to 1\textbf{00} \to 1$.

The game ends when the string becomes empty, and the score of each player is the number of $1$-characters deleted by them.

Each player wants to maximize their score. Calculate the resulting score of Alice.

-----Input-----

The first line contains one integer $T$ ($1 \le T \le 500$) — the number of test cases.

Each test case contains exactly one line containing a binary string $s$ ($1 \le |s| \le 100$).

-----Output-----

For each test case, print one integer — the resulting score of Alice (the number of $1$-characters deleted by her).

-----Example-----
Input
5
01111001
0000
111111
101010101
011011110111

Output
4
0
6
3
6

-----Note-----

Questions about the optimal strategy will be ignored.

def count_alice_score (s : String) : Nat :=
  sorry

def countOnes (s : String) : Nat :=
  sorry

def sortByLengthDesc (ls : List String) : List String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible