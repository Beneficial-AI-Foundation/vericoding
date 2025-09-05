# Task
 Define crossover operation over two equal-length strings A and B as follows:

 the result of that operation is a string of the same length as the input strings result[i] is chosen at random between A[i] and B[i]. 

 Given array of strings `arr` and a string result, find for how many pairs of strings from `arr` the result of the crossover operation over them may be equal to result.

 Note that (A, B) and (B, A) are the same pair. Also note that the pair cannot include the same element of the array twice (however, if there are two equal elements in the array, they can form a pair).

# Example

 For `arr = ["abc", "aaa", "aba", "bab"]` and `result = "bbb"`, the output should be `2`.

 ```
"abc" and "bab" can crossover to "bbb"
"aba" and "bab" can crossover to "bbb"
```
# Input/Output

 - `[input]` string array `arr`

   A non-empty array of equal-length strings.

   Constraints: `2 ≤ arr.length ≤ 10, 1 ≤ arr[i].length ≤ 10.`

 - `[input]` string `result`

   A string of the same length as each of the arr elements.

   Constraints: `result.length = arr[i].length.`

 - `[output]` an integer

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
