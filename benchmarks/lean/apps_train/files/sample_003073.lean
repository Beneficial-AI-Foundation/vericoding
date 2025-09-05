# Task
 We have a N×N `matrix` (N<10) and a robot. 

 We wrote in each point of matrix x and y coordinates of a point of matrix. 

 When robot goes to a point of matrix, reads x and y and transfer to point with x and y coordinates.

 For each point in the matrix we want to know if robot returns back to it after `EXACTLY k` moves. So your task is to count points to which Robot returns in `EXACTLY k` moves. 

 You should stop counting moves as soon as the robot returns to the starting point. That is, if the robot returns to the starting point in fewer than k moves, that point should not count as a valid point.

# example

 For:
 ```
 matrix=[
 ["0,1","0,0","1,2"], 
 ["1,1","1,0","0,2"], 
 ["2,1","2,0","0,0"]]
 k= 2
 ```
 The result should be `8`
```
Robot start at (0,0) --> (0,1) --> (0,0), total 2 moves
Robot start at (0,1) --> (0,0) --> (0,1), total 2 moves
Robot start at (0,2) --> (1,2) --> (0,2), total 2 moves
Robot start at (1,2) --> (0,2) --> (1,2), total 2 moves
Robot start at (1,0) --> (1,1) --> (1,0), total 2 moves
Robot start at (1,1) --> (1,0) --> (1,1), total 2 moves
Robot start at (2,0) --> (2,1) --> (2,0), total 2 moves
Robot start at (2,1) --> (2,0) --> (2,1), total 2 moves
Robot start at (2,2) --> (0,0) --> (0,1) --> (0,0) --> (0,1) ....
(Robot can not transfer back to 2,2)
```
So the result is 8.

# Input/Output

 - `[input]` 2D integer array matrix

 n x n matrix. 3 <= n <=9

 - `[input]` integer `k`

 `2 <= k <= 5`

 - `[output]` an integer

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
