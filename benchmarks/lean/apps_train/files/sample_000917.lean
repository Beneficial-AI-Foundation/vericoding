Given an array $A$ of length $N$.
We have to find the $maximum$ sum of elements of the subarray between $two$ nearest occurrences of $same$ elements (excluding both).
If both the elements are $even$ then the total number of $even$ elements in that subarray should be $even$ then and then only we consider that subarray and if both the elements are $odd$ then the total number of $odd$ element in that subarray should be $odd$ then and then only we consider that subarray.
If the condition never matches print $0$.

-----Input:-----
- First line contains $T$, number of test cases. Then the test cases follow.
- Each testcase consists of two lines: 
The first line has $N$ : number of elements in the array and second-line has $N$ space separated integers: elements of the array.

-----Output:-----
- For each test case, output in a single line $maximum$ sum.

-----Constraints-----
- $1 \leq T \leq 10$
- $3 \leq N \leq 2*10^5$
- $1 \leq A[i] \leq 10^8$
$NOTE $: Use of Fast Input Output is recommended.

-----Sample Input:-----
1
10
1 2 3 2 1 5 1 2 8 2

-----Sample Output:-----
7

-----EXPLANATION:-----
The maximum sum is 7, between 1 at  1st position and 1 at 5th position i.e sum of 2,3,2

def find_max_subarray_sum (arr : List Int) : Int := sorry

def list_max : List Int → Int
  | [] => 0
  | (x::xs) => max x (list_max xs)

def list_min : List Int → Int
  | [] => 0
  | (x::xs) => min x (list_min xs)

def list_sum : List Int → Int
  | [] => 0
  | (x::xs) => x + list_sum xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
