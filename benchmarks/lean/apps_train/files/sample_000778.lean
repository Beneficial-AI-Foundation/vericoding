Zonal Computing Olympiad 2013, 10 Nov 2012

Little Red Riding Hood is carrying a basket with berries through the forest to her grandmother's house.  The forest is arranged in the form of a square N × N grid of cells.  The top left corner cell, where Little Red Riding Hood starts her journey, is numbered (1,1) and the bottom right corner cell, where her grandmother lives, is numbered (N,N).  In each step, she can move either one position right or one position down.

The forest is full of dangerous wolves and she is looking for a safe path to reach her destination.  Little Red Riding Hood's fairy godmother has placed some special anti-wolf magical charms in some of the cells in the grid.  Each charm has a strength.  If the charm in cell (i,j) has strength k then its zone of influence is all the cells within k steps of (i,j); that is, all cells (i',j') such that |i - i'| + |j - j'| ≤ k.  A cell within the zone of influence of a charm is safe from wolves.  A safe path from (1,1) to (N,N) is one in which every cell along the path is safe.

Little Red Riding Hood is carrying a basket with berries. In each cell, she drops some berries while pushing her way through the thick forest.  However, sometimes she is also able to pick up fresh berries.  Each cell is labelled with an integer that indicates the net change in the number of berries in her basket on passing through the cell; that is, the number of berries she picks up in that cell minus the number of berries she drops.  You can assume that there are enough berries in her basket to start with so that the basket never becomes empty.

Little Red Riding Hood knows the positions and strengths of all the magic charms and is looking for a safe path along which the number of berries she has in the basket when she reaches her grandmother's house is maximized.

As an example consider the following grid:

3  3  2  4  3 
2  1 -1 -2  2  
-1  2  4  3 -3  
-2  2  3  2  1  
3 -1  2 -1  2  

Suppose there are 3 magic charms, at position (1,2) with strength 2, at position (4,5) with strength 2 and one at position (4,2) with strength 1.  The positions within the zone of influence of these three charms are indicated in the three grids below using X's.  

X  X  X  X  .         .  .  .  .  .         .  .  .  .  .
X  X  X  .  .         .  .  .  .  X         .  .  .  .  .
.  X  .  .  .         .  .  .  X  X         .  X  .  .  .
.  .  .  .  .         .  .  X  X  X         X  X  X  .  .
.  .  .  .  .         .  .  .  X  X         .  X  .  .  .

Putting these together, the cells that are under the zone of influence of at least one charm are marked with X below.

X  X  X  X  .
X  X  X  .  X
.  X  .  X  X
X  X  X  X  X
.  X  .  X  X

Here are two examples of safe paths in this grid, marked using Y's.  

Y  Y  X  X  .          Y  X  X  X  .
X  Y  X  .  X          Y  Y  X  .  X
.  Y  .  X  X          .  Y  .  X  X
X  Y  Y  Y  Y          X  Y  Y  Y  X
.  X  .  X  Y          .  X  .  Y  Y

Along the first path, she accumulates 19 berries while on the second path she collects 16 berries.  You can verify that among all safe paths, the maximum number of berries she can collect is 19. 

Your task is to help Little Red Riding Hood find out if there is at least one safe path and, if so, compute the maximum number of berries she can collect among all safe paths (which may be a negative number, in which case it is the minimum number of berries she will lose among all safe paths).

-----Input format-----
Line 1: Two space separated integers N and M, giving the dimension of the grid and the number of magic charms, respectively

Lines 2 to N+1: These N lines desribe the grid.  Line i+1 contains N space separated integers, describing the net change in berries in the N cells along row i of the grid.

Lines N+2 to N+M+1: These M lines describe the magic charms.  Each of these lines has 3 integers: the first two integers describe the position of the charm in the grid and the third integer describes its strength.

-----Output format-----
The first line of output must either consist of the word YES, if there are safe paths, or the word NO, if there are no safe paths. If the output on the first line is YES then the second line should contain a single integer giving the maximum number of berries Little Red Riding Hood can collect among all safe paths.  

-----Sample Input-----
5 3
3 3 2 4 3 
2 1 -1 -2 2  
-1 2 4 3 -3  
-2 2 3 2 1  
3 -1 2 -1 2  
1 2 2
4 5 2
4 2 1

-----Sample Output-----
YES
19

-----Test data-----
In all subtasks, you may assume that 2 ≤ N ≤ 500.  Each value on the grid is guaranteed to have absolute value not more than 1000. 
Let K denote the maximum strength among all the magic charms.
- Subtask 1 (30 marks) : 1 ≤ M ≤ 10, 1 ≤ K ≤ 1,000.
- Subtask 2 (70 marks) : 1 ≤ M ≤ 10,000, 1 ≤ K ≤ 10.

-----Live evaluation data-----
- Subtask 1: Testcases 0,1,2,3,4.
- Subtask 2: Testcases 5,6,7,8.

def Matrix := List (List Int)

def hasValidPath (matrix : Matrix) (charms : List Charm) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
