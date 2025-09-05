Today is the planned day tor Thik and Ayvak's wedding. Kark is infatuated with Ayvak. He offers to play a game with Thik. Whosoever wins, will get to marry Ayvak. Ayvak, who values games of chance over all the other things in life, agrees to this.

Kark sets up an N by M grid (N rows, M columns), labelled from left to right and top to bottom consecutively with numbers from 1 to M*N, with 1 at the top left corner and M*N at the bottom right corner. For example, a labelled 3 by 6 grid looks as follows:

Kark has already painted K unit squares of the grid with a heart each. Next, Thik randomly picks a rectangle with sides on the grid lines, and having a positive area, with each valid rectangle having an equal probability of being chosen. Three distinct possibilities for Thik's rectangle in the 3 by 6 grid are shown below: 

The nine different rectangles in a 2 by 2 grid are shown below:

If Thik's rectangle contains at least half of the hearts, Thik gets to marry Ayvak. Otherwise, Kark will marry Ayvak. Kark wants to know whether or not he has an advantage here, so he wants to know the expected value of the number of hearts a randomly chosen rectangle will cover. I'm sure that you have a good heart, so please, cover this job for him. 

-----Input-----
The first line of input contains one integer T, the number of test cases.
For each test case, the first line contains 3 space-separated integers N, M, K, as described in the problem statement. The next line contains K space-separated integers, each a single number from 1 to M*N, representing a square that is painted with a heart. It is guaranteed that all K integers are distinct.

-----Output-----
Output T lines, each containing a single real number, containing the expected number of hearts that a randomly chosen rectangle will contain. The answer will be considered correct if its relative or absolute error does not exceed 10-6.

-----Constraints-----
- 1 ≤ T ≤ 5  
- 1 ≤ N, M ≤ 107  
- 1 ≤ K ≤ 105 
- Each of the K integers representing a heart are between 1 and N*M, inclusive. All K integers are distinct. 

-----Subtasks-----Subtask 1 (15 points) : 

- 1 ≤ N, M ≤ 10
- 1 ≤ K ≤ N * M  
Subtask 2 (85 points) : no additional constraints 

-----Example-----
Input:
1
2 2 2
1 2

Output:
0.8888888888888888

-----Explanation-----
There are a total of 9 possible rectangles Thik could draw, shown in the figure above, and grid squares 1 and 2 are painted with a heart. The top row of possible selections (shown in the figure) contain 1, 0, 1, 2, and 2 hearts (from left to right), and the bottom row of possible selections (in the figure) contain 1, 0, 1, and 0 hearts. Therefore, 3/9 of the time 0 hearts are contained in the rectangle, 4/9 of the times 1 heart is contained in the rectangle, and 2/9 of the time 2 hearts are contained in the rectangle. The expected value is then 0 * 3/9 + 1 * 4/9 + 2 * 2/9 = 8/9.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
