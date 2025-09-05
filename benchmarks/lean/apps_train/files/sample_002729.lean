# Task
 You are given an array of integers. Your task is to determine the minimum number of its elements that need to be changed so that elements of the array will form an arithmetic progression. Note that if you swap two elements, you're changing both of them, for the purpose of this kata.

 Here an arithmetic progression is defined as a sequence of integers such that the difference between consecutive terms is constant. For example, `6 4 2 0 -2` and `3 3 3 3 3` are arithmetic progressions, but `0 0.5 1 1.5` and `1 -1 1 -1 1` are not.

# Examples

  For `arr = [1, 3, 0, 7, 9]` the answer is `1` 

  Because only one element has to be changed in order to create an arithmetic progression.

  For `arr = [1, 10, 2, 12, 3, 14, 4, 16, 5]` the answer is `5` 

  The array will be changed into `[9, 10, 11, 12, 13, 14, 15, 16, 17]`.

# Input/Output

 - `[input]` integer array `arr`

  An array of N integers.

  `2 ≤ arr.length ≤ 100`

  `-1000 ≤ arr[i] ≤ 1000`

  Note for Java users: you'll have a batch of 100 bigger random arrays, with lengths as `150 ≤ arr.length ≤ 300`.

 - `[output]` an integer

  The minimum number of elements to change.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded