# Task
 You are given n rectangular boxes, the ith box has the length lengthi, the width widthi and the height heighti. 

 Your task is to check if it is possible to pack all boxes into one so that inside each box there is no more than one another box (which, in turn, can contain at most one another box, and so on). 

 More formally, your task is to check whether there is such sequence of n different numbers pi (1 ≤ pi ≤ n) that for each 1 ≤ i < n the box number pi can be put into the box number pi+1.

 A box can be put into another box if all sides of the first one are less than the respective ones of the second one. You can rotate each box as you wish, i.e. you can `swap` its length, width and height if necessary.

# Example

 For `length = [1, 3, 2], width = [1, 3, 2] and height = [1, 3, 2]`, the output should be `true`;

 For `length = [1, 1], width = [1, 1] and height = [1, 1],` the output should be `false`;

 For `length = [3, 1, 2], width = [3, 1, 2] and height = [3, 2, 1]`, the output should be `false`.

# Input/Output

 - `[input]` integer array `length`

    Array of positive integers.

    Constraints:

    `1 ≤ length.length ≤ 100,`

    `1 ≤ length[i] ≤ 2000.`

 - `[input]` integer array `width`

    Array of positive integers.

    Constraints:

    `width.length = length.length,`

    `1 ≤ width[i] ≤ 2000.`

 - `[input]` integer array `height`

    Array of positive integers.

    Constraints:

    `height.length = length.length,`

    `1 ≤ height[i] ≤ 2000.`

 - `[output]` a boolean value

    `true` if it is possible to put all boxes into one, `false` otherwise.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
