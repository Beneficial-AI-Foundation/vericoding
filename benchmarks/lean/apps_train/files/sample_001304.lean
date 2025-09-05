The chef is having one array of N natural numbers(numbers may be repeated). i.e. All natural numbers must be less than N. Chef wants to rearrange the array and try to place a natural number on its index of the array, i.e array[i]=i. If multiple natural numbers are found for given index place one natural number to its index and ignore others.i.e. arr[i]=i and multiple i found in array ignore all remaining i's If any index in the array is empty place 0 at that place. i.e. if for arr[i], i is not present do arr[i]=0.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains two lines of input.
- First-line has $N$ denoting the size of an array.
- Second-line has $N$ space-separated natural numbers.

-----Output:-----
For each test case, output in a single line with the new rearranged array.

-----Constraints-----
- $1 \leq T \leq 10^3$
- $2 \leq N \leq 10^3$
- $arr[i] \leq N-1$

-----Sample Input:-----
2
2
1 1
4
1 1 2 1

-----Sample Output:-----
0 1
0 1 2 0

-----EXPLANATION:-----
For 1) $1$ occurs twice in the array hence print 0 at 0th index and 1 at 1st index
For 2) $1$ occurs thrice and 2 once in the array hence print 0 at 0th index and 1 at 1st index, 2 at 2nd index and 0 at 3rd index.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
