It's the annual military parade, and all the soldier snakes have arrived at the parade arena, But they aren't standing properly. The entire parade must be visible from the main podium, and all the snakes must be in a line. But the soldiers are lazy, and hence you must tell the soldiers to move to their new positions in such a manner that the total movement is minimized.
Formally, the entire parade strip can be thought of as the integer line. There are N snakes, where each snake is a line segment of length L. The i-th snake is initially at the segment [Si, Si + L]. The initial positions of the snakes can overlap. The only segment of the strip visible from the podium is [A, B], and hence all the snakes should be moved so that all of them are visible from the podium. They should also all be in a line without gaps and every consecutive pair touching each other. In other words, they should occupy the segments [X, X + L], [X + L, X + 2*L], ... , [X + (N-1)*L, X + N*L], for some X, such that A ≤ X ≤ X + N*L ≤ B. You are guaranteed that the visible strip is long enough to fit all the snakes.

If a snake was initially at the position [X1, X1 + L] and finally is at the position [X2, X2 + L], then the snake is said to have moved a distance of |X2 - X1|. The total distance moved by the snakes is just the summation of this value over all the snakes. You need to move the snakes in such a manner that it satisfies all the conditions mentioned above, as well as minimize the total distance. You should output the minimum total distance achievable.

-----Input-----
- The first line contains a single integer, T, the number of testcases. The description of each testcase follows.
- The first line of each testcase contains four integers, N, L, A and B, where N denotes the number of snakes, L denotes the length of each snake, and [A, B] is the segment visible from the podium.
- The next line contains N integers, the i-th of which is Si. This denotes that the i-th snake is initially in the segment [Si, Si + L].

-----Output-----
- For each testcase, output a single integer in a new line: the minimum total distance achievable.

-----Constraints-----
- 1 ≤ T ≤ 10
- 1 ≤ N ≤ 105
- 1 ≤ Si ≤ 109
- 1 ≤ L ≤ 109
- 1 ≤ A ≤ B ≤ 109
- N * L ≤ B - A

-----Example-----
Input:
2
3 4 11 23
10 11 30
3 4 11 40
10 11 30

Output:
16
16

-----Explanation-----
In the first testcase, the three snakes are initially at segments [10, 14], [11, 15], and [30, 34]. One optimal solution is to move the first snake which was at [10, 14] to [15, 19] and the third snake which was at [30, 34] to [19, 23]. After this, the snakes would form a valid parade because they will be from [11, 15], [15, 19] and [19, 23]. Hence they are all in a line without any gaps in between them, and they are all visible, because they all lie in the visible segment, which is [11, 23].
The distance traveled by the first snake is |15 - 10| = 5, by the second snake is |11 - 11| = 0 and by the third snake is |19 - 30| = 11. Hence the total distance traveled is 5 + 0 + 11 = 16. This is the best that you can do, and hence the answer is 16.
In the second testcase, only the visible segment has increased. But you can check that the same final configuration as in the first subtask is still optimal here. Hence the answer is 16.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded