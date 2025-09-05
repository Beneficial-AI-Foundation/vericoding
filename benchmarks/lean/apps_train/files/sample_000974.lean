A group of rebels travelling on a square hoverboard is ambushed by Imperial Stormtroopers.Their big hoverboard is an easy target, so they decide to split the board into smaller square hoverboards so that they can bolt away easily.But they should also make sure they don't get too spread out.Help the rebels split the craft into minimum number of smaller crafts possible.

-----Input-----
A single integer N denoting the side length of the big hoverboard.

-----Output-----
In the first line, output the integer 'k' which is the minimum number of square boards into which the bigger board can be split up.

In the second line, output k space separated integers which denote the sizes of the smaller square hoverboards.This must be in increasing order of sizes.

-----Constraints-----
N ranges from 2 to 50.

-----Example-----
Input:
3

Output:
6
1 1 1 1 1 2

-----Explanation-----
A square of side length 3 can be split into smaller squares in two ways: Either into 9 squares of side1 or 5 squares of side 1 and 1 square of size 2.The second case is the favourable one.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible