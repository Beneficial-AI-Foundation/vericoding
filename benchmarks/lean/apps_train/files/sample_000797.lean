Amit is going on a date and he wants to gift his date an array of positive numbers. But he is running short on money. He already has an array of numbers in design. Cost of an array of numbers is the sum of elements in it. But he wants to minimize the cost of making it. 
So he does the following number of operations one by one for any number of times:
He chooses two adjacent elements ,replace them by one element with value = XOR of the two numbers. This operation reduces length of array (and elements are re-numerated accordingly)
Find the minimum amount of money that Amit needs to spend to gift his date.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of $2$ lines of input, first line contains a single integer $N$ and the second line contains $N$ elements - $A1,A2,A3,.....,AN$ 

-----Output:-----
For each testcase, output in a single line answer denoting the minimum cost

-----Constraints-----
- $1 \leq T \leq 10$
- $1 \leq N \leq 10^5$
- $0 \leq Ai \leq 10^9$ for $1\leq i \leq N$

-----Sample Input:-----
3
5
8 4 1 5 0
5
1 2 4 0 8
2
10 10

-----Sample Output:-----
8
15
0

-----EXPLANATION:-----
For first case,
This array is :
$[8,4,1,5,0] -> [8,4,4,0] -> [8,0,0]$. Sum=$8$ So the answer is 8.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
