Motu and Tomu are very good friends who are always looking for new games to play against each other and ways to win these games. One day, they decided to play a new type of game with the following rules:
- The game is played on a sequence $A_0, A_1, \dots, A_{N-1}$.
- The players alternate turns; Motu plays first, since he's earlier in lexicographical order.
- Each player has a score. The initial scores of both players are $0$.
- On his turn, the current player has to pick the element of $A$ with the lowest index, add its value to his score and delete that element from the sequence $A$.
- At the end of the game (when $A$ is empty), Tomu wins if he has strictly greater score than Motu. Otherwise, Motu wins the game.
In other words, Motu starts by selecting $A_0$, adding it to his score and then deleting it; then, Tomu selects $A_1$, adds its value to his score and deletes it, and so on.
Motu and Tomu already chose a sequence $A$ for this game. However, since Tomu plays second, he is given a different advantage: before the game, he is allowed to perform at most $K$ swaps in $A$; afterwards, the two friends are going to play the game on this modified sequence.
Now, Tomu wants you to determine if it is possible to perform up to $K$ swaps in such a way that he can win this game.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains two space-separated integers $N$ and $K$ denoting the number of elements in the sequence and the maximum number of swaps Tomu can perform.
- The second line contains $N$ space-separated integers $A_0, A_1, \dots, A_{N-1}$.

-----Output-----
For each test case, print a single line containing the string "YES" if Tomu can win the game or "NO" otherwise (without quotes).

-----Constraints-----
- $1 \le T \le 100$
- $1 \le N \le 10,000$
- $0 \le K \le 10,000$
- $1 \le A_i \le 10,000$ for each valid $i$

-----Subtasks-----
Subtask #1 (20 points): $1 \le N \le 100$
Subtask #2 (80 points): original constraints

-----Example Input-----
2
6 0
1 1 1 1 1 1
5 1
2 4 6 3 4

-----Example Output-----
NO
YES

-----Explanation-----
Example case 1: At the end of the game, both Motu and Tomu will have scores $1+1+1 = 3$. Tomu is unable to win that game, so the output is "NO".
Example case 2: If no swaps were performed, Motu's score would be $2+6+4 = 12$ and Tomu's score would be $4+3 = 7$. However, Tomu can swap the elements $A_2 = 6$ and $A_3 = 3$, which makes Motu's score at the end of the game equal to $2+3+4 = 9$ and Tomu's score equal to $4+6 = 10$. Tomu managed to score higher than Motu, so the output is "YES".

def can_tomu_win (n : Nat) (k : Nat) (arr : List Nat) : String := sorry

def getOddElements (l : List Nat) : List Nat :=
  l.zipWith (fun i x => if i % 2 = 1 then some x else none) (List.range l.length)
   |>.filterMap id

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
