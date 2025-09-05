# Task
 Alireza and Ali have a `3×3 table` and playing on that. they have 4 table(2×2) A,B,C and D in this table.

 At beginning all of 9 numbers in 3×3 table is zero.

 Alireza in each move choose a 2×2 table from A, B, C and D and increase all of 4 numbers in that by one.

 He asks Ali, how much he increase table A, B, C and D. (if he cheats you should return `[-1]`)

 Your task is to help Ali.

# Example

 For 
 ```
 table=
[[1,2,1],
[2,4,2],
[1,2,1]]```
The result should be `[1,1,1,1]`

 For:
 ```
Table=
[[3,7,4],
[5,16,11],
[2,9,7]]```
The result should be `[3,4,2,7]`

# Input/Output

 - `[input]` 2D integer array `table`

 `3×3` table.

 - `[output]` an integer array

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible