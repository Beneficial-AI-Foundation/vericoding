The mobile application store has a new game called "Subway Roller".

The protagonist of the game Philip is located in one end of the tunnel and wants to get out of the other one. The tunnel is a rectangular field consisting of three rows and n columns. At the beginning of the game the hero is in some cell of the leftmost column. Some number of trains rides towards the hero. Each train consists of two or more neighbouring cells in some row of the field.

All trains are moving from right to left at a speed of two cells per second, and the hero runs from left to right at the speed of one cell per second. For simplicity, the game is implemented so that the hero and the trains move in turns. First, the hero moves one cell to the right, then one square up or down, or stays idle. Then all the trains move twice simultaneously one cell to the left. Thus, in one move, Philip definitely makes a move to the right and can move up or down. If at any point, Philip is in the same cell with a train, he loses. If the train reaches the left column, it continues to move as before, leaving the tunnel.

Your task is to answer the question whether there is a sequence of movements of Philip, such that he would be able to get to the rightmost column.

 [Image] 

-----Input-----

Each test contains from one to ten sets of the input data. The first line of the test contains a single integer t (1 ≤ t ≤ 10 for pretests and tests or t = 1 for hacks; see the Notes section for details) — the number of sets.

Then follows the description of t sets of the input data. 

The first line of the description of each set contains two integers n, k (2 ≤ n ≤ 100, 1 ≤ k ≤ 26) — the number of columns on the field and the number of trains. Each of the following three lines contains the sequence of n character, representing the row of the field where the game is on. Philip's initial position is marked as 's', he is in the leftmost column. Each of the k trains is marked by some sequence of identical uppercase letters of the English alphabet, located in one line. Distinct trains are represented by distinct letters. Character '.' represents an empty cell, that is, the cell that doesn't contain either Philip or the trains.

-----Output-----

For each set of the input data print on a single line word YES, if it is possible to win the game and word NO otherwise.

-----Examples-----
Input
2
16 4
...AAAAA........
s.BBB......CCCCC
........DDDDD...
16 4
...AAAAA........
s.BBB....CCCCC..
.......DDDDD....

Output
YES
NO

Input
2
10 4
s.ZZ......
.....AAABB
.YYYYYY...
10 4
s.ZZ......
....AAAABB
.YYYYYY...

Output
YES
NO

-----Note-----

In the first set of the input of the first sample Philip must first go forward and go down to the third row of the field, then go only forward, then go forward and climb to the second row, go forward again and go up to the first row. After that way no train blocks Philip's path, so he can go straight to the end of the tunnel.

Note that in this problem the challenges are restricted to tests that contain only one testset.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded