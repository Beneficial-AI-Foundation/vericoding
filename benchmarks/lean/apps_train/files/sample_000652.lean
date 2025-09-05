Chef is going to start playing Fantasy Football League (FFL) this season. In FFL, each team consists of exactly $15$ players: $2$ goalkeepers, $5$ defenders, $5$ midfielders and $3$ forwards. Chef has already bought $13$ players; he is only missing one defender and one forward.
There are $N$ available players (numbered $1$ through $N$). For each valid $i$, the $i$-th player is either a defender or a forward and has a price $P_i$. The sum of prices of all players in a team must not exceed $100$ dollars and the players Chef bought already cost him $S$ dollars.
Can you help Chef determine if he can complete the team by buying one defender and one forward in such a way that he does not exceed the total price limit?

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains two space-separated integers $N$ and $S$.
- The second line contains $N$ space-separated integers $P_1, P_2, \ldots, P_N$.
- The last line contains $N$ space-separated integers. For each valid $i$, the $i$-th of these integers is $0$ if the $i$-th player is a defender or $1$ if the $i$-th player is a forward.

-----Output-----
For each test case, print a single line containing the string "yes" if it is possible to build a complete team or "no" otherwise (without quotes).

-----Constraints-----
- $1 \le T \le 100$
- $1 \le N \le 100$
- $13 \le S \le 100$
- $1 \le P_i \le 100$ for each valid $i$

-----Subtasks-----
Subtask #1 (100 points): original constraints

-----Example Input-----
2
4 90
3 8 6 5
0 1 1 0
4 90
5 7 6 5
0 1 1 0

-----Example Output-----
yes
no

-----Explanation-----
Example case 1: If Chef buys the $1$-st and $3$-rd player, the total price of his team is $90 + 9 = 99$, which is perfectly fine. There is no other valid way to pick two players.
Example case 2: Chef cannot buy two players in such a way that all conditions are satisfied.

def can_complete_team (N : Nat) (S : Nat) (prices : List Nat) (positions : List Nat) : String := sorry

theorem empty_lists :
  can_complete_team 0 0 [] [] = "no" := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
