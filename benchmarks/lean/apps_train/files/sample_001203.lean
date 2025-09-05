Walter White and Jesse Pinkman (a drug addict) both love to play with chemicals. One day they were playing with some chemicals to make an energy drink. Unknowingly they made a highly powerful drink. To test the drink on others also they called some of their friends and gave a drop of it to everyone. Now they all were feeling highly energetic and thought of an unique game to play with each other.
After pondering for a while, Jesse came up with an extraordinary idea of competing in a race around a circular globe with N checkpoints each of one unit. Walter and all their other friends agreed with it.They divided themselves in $2$ teams with $N$ teammates in each team.This race has two commencing points $A$ and $B$ strictly facing each other. Walter and his team commences from $A$ point and other team starts from $B$. Both the teams start running at the same time clockwise around the globe. Speed of every player is constant throughout the race. If a player has a speed $X$ then it means that he covers a distance of $X$ units in one second.The race ends when some member of one team overtakes all members of opposite team at any point of time. Now you have to tell if any team will win the race or not.They all are stubborn and can run forever just to win the race. Help them to know if it is possible in anyway that the race will come to an end. 
For Clarity, you can visualize the path as a circular paths where $A$ and $B$ are opposite ends of diameter. It can be proven that the actual circumference of circle do not affect the answer.
It is also possible that someone don't run at all.Keep in mind that the fastest one wins the race so does the code.

-----Input:------
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows. 
- The first line of each test case contains a single integer $N$ number of teammates in both team.
- The second line contains $N$ space-separated integers $A_1, A_2 \ldots A_N$ denoting speed of A's Team
- The third line contains $N$ space-separated integers  $B_1, B_2 \ldots B_N$ denoting speed of B's Team

-----Output:------
For each test case, print a single line denoting YES if the race ends at any point of time else NO

-----Constraints-----
- $1 \leq T \leq 10$
- $1 \leq N \leq 10^5$
- $0 \leq A_i \leq 2^{15}$
- $0 \leq B_i \leq 2^{15}$

-----Subtasks-----
Subtask #1 (30 points): 
- $1 \le N \le 20$
- $0 \le  A_i  \le 11$
- $0 \le  B_i  \le 11$
Subtask #2 (70 points): 
- Original constraints

-----Sample input:-----
1
5
1 2 3 4 5
2 7 8 9 9

-----Sample output-----
YES

-----Sample Explanation:------
Team B can overtake all members of Team A.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded