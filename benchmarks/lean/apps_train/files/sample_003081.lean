# Task
Given an integer array `arr`. Your task is to remove one element, maximize the product of elements. 

The result is the element which should be removed. If more than one valid results exist, return the smallest one.

# Input/Output

`[input]` integer array `arr`

non-empty unsorted integer array. It contains positive integer, negative integer or zero.

`3 ≤ arr.length ≤ 15`

`-10 ≤ arr[i] ≤ 10`

`[output]` an integer

The element that should be removed.

# Example

For `arr = [1, 2, 3]`, the output should be `1`.

For `arr = [-1, 2, -3]`, the output should be `2`.

For `arr = [-1, -2, -3]`, the output should be `-1`.

For `arr = [-1, -2, -3, -4]`, the output should be `-4`.

def minimum (l : List Int) : Option Int := sorry
def maximum (l : List Int) : Option Int := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
