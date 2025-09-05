There are players standing in a row each player has a digit written on their T-Shirt (multiple players can have the same number written on their T-Shirt).   
You have to select a group of players, note that players in this group should be standing in $\textbf{consecutive fashion}$. For example second player of chosen group next to first player of chosen group, third player next to second and similarly last player next to second last player of chosen group. Basically You've to choose a contiguous group of players.
After choosing a group, players can be paired if they have the same T-Shirt number (one player can be present in at most one pair), finally the chosen group is called “good” if at most one player is left unmatched. Your task is to find the size of the maximum “good” group.
Formally, you are given a string $S=s_{1}s_{2}s_{3}...s_{i}...s_{n}$ where $s_{i}$ can be any digit character between $'0'$ and $'9'$ and $s_{i}$ denotes the number written on the T-Shirt of $i^{th}$ player. Find a value $length$ such that there exist pair of indices $(i,j)$ which denotes $S[i...j]$ is a “good” group where $i\geq1$ and $j\leq S.length$ and $i\leq j$ and $(j-i+1)=length$ and there exist no other pair $(i’,j’)$ such that $(j’-i’+1)>length$ and $S[i'...j']$ is a "good" group.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- $i^{th}$ testcase consist of a single line of input, a string $S$. 

-----Output:-----
For each testcase, output in a single line maximum possible size of a "good" group.

-----Constraints-----
$\textbf{Subtask 1} (20 points)$
- $1 \leq T \leq 10$
- $S.length \leq 10^{3}$
$\textbf{Subtask 2} (80 points)$
- $1 \leq T \leq 10$
- $S.length \leq 10^{5}$

-----Sample Input:-----
1

123343

-----Sample Output:-----
3

-----EXPLANATION:-----
1$\textbf{$\underline{2 3 3}$}$43
Underlined group is a “good” group because the second player(number 2 on T-Shirt) is the only player who is left unmatched and third and fourth player can form a pair, no other group has length greater than 3 that are “good”. However note that we have other “good” group also 12$\textbf{$\underline{334}$}$3 but length is 3 which is same as our answer.

-----Sample Input:-----
1

95665

-----Sample Output:-----
5

-----EXPLANATION:-----
$\textbf{$\underline{95665}$}$ is “good” group because first player is the only player who is left unmatched second and fifth player can form pair and third and fourth player also form pair.

-----Sample Input:-----
2

2323

1234567

-----Sample Output:-----
4

1

-----EXPLANATION:-----
For first test case
$\textbf{$\underline{2323}$}$ is a “good” group because there are no players who are left unmatched first and third player form pair and second and fourth player form pair.

For second test

Only length one "good" group is possible.

def find_max_good_group (s : String) : Nat :=
  sorry

def is_good_group (s : String) : Bool :=
  sorry

def substring (s : String) (start len : Nat) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
