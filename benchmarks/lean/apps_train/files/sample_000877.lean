Tweedle-Dee and Tweedle-Dum are playing a fierce match of binary Nim. This novel game is played with $N$ stacks, each of them containing only $1$-s and $0$-s.
Just like in normal Nim, Tweedle-Dee and Tweedle-Dum alternate turns; in their turn, a player must choose one non-empty stack and remove a positive number of elements from the top of this stack. However, Tweedle-Dee may only choose a stack with $0$ at the top (and remove elements from it afterwards), and similarly, Tweedle-Dum may only choose a stack with $1$ at the top. the player that cannot make a move loses
Suzumo does not want to wait for the end of the game, so given the starting player he asks you to determine the winner. Remember that Tweedle-Dee and Tweedle-Dum are legendary grandmasters of combinatorial games, so both always play optimally.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains an integer $N$, a string $S$ denoting the number of stacks, the player that starts the game, respectively.
- Each of the following $N$ lines contains a single binary string $B$ representing a stack; the first character of $B$ corresponds to the top element of the stack and the last character to the bottom element.

-----Output-----
For each test case, print a single line containing the string "Dee" if Tweedle-Dee wins the match or "Dum" if Tweedle-Dum wins.

-----Constraints-----
- $1 \le T \le 500$
- $1 \le N \le 50$
- $1 \le |B| \le 50$
- each character in $B$ is either '1' or '0'
- $S$ is either "Dee" or "Dum"

-----Example Input-----
2
2 Dee
101
010
2 Dum
101
010

-----Example Output-----
Dum
Dee

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
