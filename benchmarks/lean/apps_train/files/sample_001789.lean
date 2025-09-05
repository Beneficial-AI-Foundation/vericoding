Storekeeper is a game in which the player pushes boxes around in a warehouse trying to get them to target locations.
The game is represented by a grid of size m x n, where each element is a wall, floor, or a box.
Your task is move the box 'B' to the target position 'T' under the following rules:

Player is represented by character 'S' and can move up, down, left, right in the grid if it is a floor (empy cell).
Floor is represented by character '.' that means free cell to walk.
Wall is represented by character '#' that means obstacle  (impossible to walk there). 
There is only one box 'B' and one target cell 'T' in the grid.
The box can be moved to an adjacent free cell by standing next to the box and then moving in the direction of the box. This is a push.
The player cannot walk through the box.

Return the minimum number of pushes to move the box to the target. If there is no way to reach the target, return -1.

Example 1:

Input: grid = [["#","#","#","#","#","#"],
               ["#","T","#","#","#","#"],
               ["#",".",".","B",".","#"],
               ["#",".","#","#",".","#"],
               ["#",".",".",".","S","#"],
               ["#","#","#","#","#","#"]]
Output: 3
Explanation: We return only the number of times the box is pushed.
Example 2:
Input: grid = [["#","#","#","#","#","#"],
               ["#","T","#","#","#","#"],
               ["#",".",".","B",".","#"],
               ["#","#","#","#",".","#"],
               ["#",".",".",".","S","#"],
               ["#","#","#","#","#","#"]]
Output: -1

Example 3:
Input: grid = [["#","#","#","#","#","#"],
               ["#","T",".",".","#","#"],
               ["#",".","#","B",".","#"],
               ["#",".",".",".",".","#"],
               ["#",".",".",".","S","#"],
               ["#","#","#","#","#","#"]]
Output: 5
Explanation:  push the box down, left, left, up and up.

Example 4:
Input: grid = [["#","#","#","#","#","#","#"],
               ["#","S","#",".","B","T","#"],
               ["#","#","#","#","#","#","#"]]
Output: -1

Constraints:

m == grid.length
n == grid[i].length
1 <= m <= 20
1 <= n <= 20
grid contains only characters '.', '#',  'S' , 'T', or 'B'.
There is only one character 'S', 'B' and 'T' in the grid.

def min_push_box (grid: Grid) : Int := sorry

def charEq (c1 c2 : Char) : Bool := c1.val = c2.val

def isValidCharProp (c: Char) : Prop := 
  c = '#' ∨ c = '.' ∨ c = 'S' ∨ c = 'B' ∨ c = 'T'

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded