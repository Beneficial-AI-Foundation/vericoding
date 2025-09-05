Galileo's latest project involves determining the density of stars in certain regions of the sky. For this purpose he started looking for datasets online, and discovered a dataset on Newton's blog. Newton had decomposed the night sky into a Voronoi tessellation with the generators arranged in a grid. He has stored the number of stars in a Voronoi cell at a position in a matrix that corresponds to the position of the generator in the grid.
This dataset does not directly help Galileo, because he needs to be able to query the number of stars in a rectangular portion of the sky. Galileo tried to write a program that does this on his own, but it turned out to be too slow. Can you help him?

-----Input Format-----
The first line contains two integers n and m that denote the height and width of the matrix respectively. This is followed by  n lines each containing m integers each.
The line following this would contain a single integer t, the number of queries to be run. Each query line consists of 4 integers px, py, qx, qy. The first two integers denote the row and column numbers of the upper left corner of the rectangular region, and the second pair of numbers correspond to the lower right corner.

-----Output Format-----
For each query output a single line containing the number of stars in that rectangular region.

-----Example-----
Input:

3 3
10 10 10
10 10 10
10 10 10
4
1 1 1 1
1 1 3 3
2 1 3 3
3 1 3 3

Output:

10
90
60
30

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded