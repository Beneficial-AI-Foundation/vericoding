Uttu got to know about an interesting two-player mobile game recently and invites his friend Gangwar to try it out with him. Gangwar, however, has been playing this game since it was out 5 years ago and is a Legendary Grandmaster at it. Uttu immediately thought of somehow cheating in this game to beat Gangwar.
But the most he could do was choose if he wanted to go "First" or if he wanted to go "Second" in this alternative turn based game. Help Uttu choose so that he will always win regardless of Gangwar's moves.Description of the game
You are playing on a continent name Tamriel. This continent have $N$ towns numbered from $1$ to $N$ where town $1$ is the capital. These towns are connected to each other by $N-1$ roads. Any two towns are connected by some series of roads, i.e., You can go from any town to any other town using these roads.
Each town $i$ some initial amout of soldiers $S_i$ in it. At every move, a player can choose a town other than the capital $i$ and move some non-zero amount of its current soldiers to a town which is one step closer towards the capital. After the first move, the moves are alternated between the players. The player who cannot make a move loses.Input
- The first line contains a single integer $N$
- The second line contains a $N$ space seperated integers denoting $S_1,S_2,\dots,S_n$
- The $N-1$ subsequent lines contain two space seperated integers $u$ and $v$, denoting that the town $u$ and town $v$ are connected by a road.Output
- Print "First" or "Second" based on what Uttu should choose to win.Constraints
- $ 2 \leq N \leq {2}\times{10}^{5}$
- $ 1 \leq S_i \leq {10}^{9}$ for each valid $i$
- $ 1 \leq u,v \leq N$Sample Input 1
2
10 10
1 2
Sample Output 1
First
Explanation 1
Uttu will move the $10$ soldiers at town $2$ to the capital (town $1$). After this Gangwar cannot make a move, so he loses.Sample Input 2
3
1 1 1
1 2
1 3
Sample Output 2
Second
Explanation 2
Gangwar has options: either move the soldier at town $2$, or move the soldier at town $3$.
Whatever he choses, Uttu will chose the other town's soldier to move. And then Gangwar loses.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded