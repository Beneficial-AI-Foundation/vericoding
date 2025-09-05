Chandler has a list of non zero positive integers with him. He made a very interesting observation about the list. He noticed that the number of unique integers in an array of size $N$ is in the range $L$ to $R$ (both inclusive) and every element was either 1 or an even number x, in which case x/2 was also definitely present in the array. 
Chandler has misplaced the list of integers but he wants to impress Monica with his problem solving skills by finding out the minimum and maximum possible sum of all elements of the list of integers.
Can you also help him solve the problem so that he can win over Monica?

-----Input:-----
- First line will contain $T$, the number of testcases. 
- The first line of each test case contains integers $N$, $L$, and $R$. 

-----Output:-----
For each test case print 2 space-separated integers, the minimum and the maximum possible sum of N elements based on the above facts.

-----Constraints-----
- $1 \leq T \leq 100$
- $1 \leq N \leq 1000$
- $1 \leq L \leq R \leq min(N,20)$

-----Sample Input:-----
2

4 2 2

5 1 5

-----Sample Output:-----
5 7

5 31

-----EXPLANATION:-----
- 
Example 1: For an array of size 4, with minimum 2 unique integers and maximum 2 unique integers, the possible arrays are (1,1,1,2), (1,1,2,2), (1,2,2,2)
Out of these, the minimum possible sum of elements is 5(1+1+1+2) and maximum possible sum is 7(1+2+2+2)
- 
Example 2: For an array of size 5, with minimum 1 unique integer and maximum 5 unique integers, minimum possible sum of elements is 5(1+1+1+1+1) and maximum possible sum is 31(1+2+4+8+16)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible