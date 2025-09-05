# Task
 You are given a regular array `arr`. Let's call a `step` the difference between two adjacent elements. 

 Your task is to sum the elements which belong to the sequence of consecutive elements of length `at least 3 (but as long as possible)`, such that the steps between the elements in this sequence are the same.

 Note that some elements belong to two sequences and have to be counted twice.

# Example

 For `arr = [54, 70, 86, 1, -2, -5, 0, 5, 78, 145, 212, 15]`, the output should be `639`.
```
There are 4 sequences of equal steps in the given array:
{54, 70, 86} => step +16
{1, -2, -5} => step -3
{-5, 0, 5} => step +5
{78, 145, 212} => step +67
So the answer is 
(54 + 70 + 86) + 
(1 - 2 - 5) + 
(-5 + 0 + 5) + 
(78 + 145 + 212) = 639.
The last element 15 was not be counted.
```

 For `arr = [7, 2, 3, 2, -2, 400, 802]`, the output should be `1200`.
 ```
 There is only 1 sequence in arr:
 {-2, 400, 802} => step +402
 So the answer is: -2 + 400 + 802 = 1200
 ```

 For `arr = [1, 2, 3, 4, 5]`, the output should be `15`.

 Note that we should only count {1, 2, 3, 4, 5} as a whole, any other small subset such as {1, 2, 3},{2, 3, 4},{3, 4, 5} are belong to {1, 2, 3, 4, 5}.

# Input/Output

 - `[input]` array.integer `arr`

 `3 ≤ arr.length ≤ 100`

 - `[output]` an integer

 The sum of sequences.

def isArithmeticSequence (arr : List Int) : Bool :=
  sorry

def sumOfRegularNumbers (arr : List Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded