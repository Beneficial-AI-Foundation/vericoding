3R2 as DJ Mashiro - Happiness Breeze Ice - DJ Mashiro is dead or alive

NEKO#ΦωΦ has just got a new maze game on her PC!

The game's main puzzle is a maze, in the forms of a $2 \times n$ rectangle grid. NEKO's task is to lead a Nekomimi girl from cell $(1, 1)$ to the gate at $(2, n)$ and escape the maze. The girl can only move between cells sharing a common side.

However, at some moments during the game, some cells may change their state: either from normal ground to lava (which forbids movement into that cell), or vice versa (which makes that cell passable again). Initially all cells are of the ground type.

After hours of streaming, NEKO finally figured out there are only $q$ such moments: the $i$-th moment toggles the state of cell $(r_i, c_i)$ (either from ground to lava or vice versa).

Knowing this, NEKO wonders, after each of the $q$ moments, whether it is still possible to move from cell $(1, 1)$ to cell $(2, n)$ without going through any lava cells.

Although NEKO is a great streamer and gamer, she still can't get through quizzes and problems requiring large amount of Brain Power. Can you help her?

-----Input-----

The first line contains integers $n$, $q$ ($2 \le n \le 10^5$, $1 \le q \le 10^5$).

The $i$-th of $q$ following lines contains two integers $r_i$, $c_i$ ($1 \le r_i \le 2$, $1 \le c_i \le n$), denoting the coordinates of the cell to be flipped at the $i$-th moment.

It is guaranteed that cells $(1, 1)$ and $(2, n)$ never appear in the query list.

-----Output-----

For each moment, if it is possible to travel from cell $(1, 1)$ to cell $(2, n)$, print "Yes", otherwise print "No". There should be exactly $q$ answers, one after every update.

You can print the words in any case (either lowercase, uppercase or mixed).

-----Example-----
Input
5 5
2 3
1 4
2 4
2 3
1 4

Output
Yes
No
No
No
Yes

-----Note-----

We'll crack down the example test here:  After the first query, the girl still able to reach the goal. One of the shortest path ways should be: $(1,1) \to (1,2) \to (1,3) \to (1,4) \to (1,5) \to (2,5)$.  After the second query, it's impossible to move to the goal, since the farthest cell she could reach is $(1, 3)$.  After the fourth query, the $(2, 3)$ is not blocked, but now all the $4$-th column is blocked, so she still can't reach the goal.  After the fifth query, the column barrier has been lifted, thus she can go to the final goal again.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded
