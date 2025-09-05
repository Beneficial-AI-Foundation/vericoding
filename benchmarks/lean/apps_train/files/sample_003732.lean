# Story&Task
 The capital of Berland has n multifloor buildings. The architect who built up the capital was very creative, so all houses in the city were built in one row.

 Let's enumerate all the houses from left to right, starting with 0. A house is considered to be luxurious if the number of floors in it is strictly greater than in each house with larger number. In other words, a house is luxurious if the number of floors in it is strictly greater than in all houses, located to the right from it.

 The new architect is interested in n questions, the ith of them is the following: "how many floors should be added to the ith house to make it luxurious?" (For each i from 1 to n, inclusive). You need to help him cope with this task.

 Note that all these questions are independent from each other — the answer to the question for house i does not affect other answers (i.e., the floors to the houses are not actually added).

# Input/Output

 - `[input]` integer array `houses`

  Array of positive integers, representing the number of floors in each house.

  The ith element is the number of houses in the ith house.

  `1 ≤ houses.length ≤ 1000`

 - `[output]` an integer array

  An array has the same length as input array, the ith element represents the number of floors that should be added to the ith house to make it luxurious.

# Example

 For `houses = [1,2,3,1,2]`, the output should be `[3,2,0,2,0]`.
 ```
 For houses[0], 3 floors should be added, 
 then its floors is strictly greater than all houses of right side.

 For houses[1], 2 floors should be added.

 For houses[2], no need to add floor
 because it's already the luxurious.

 For houses[3], 2 floors need to added

 For houses[4], no house on the right, 
 so no need to add any floor.
 ```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded