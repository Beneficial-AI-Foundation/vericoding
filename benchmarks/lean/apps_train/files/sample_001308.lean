Chef likes to play with array elements. His teacher has given him an array problem. But now he is busy as Christmas is coming. So, he needs your help. Can you help him to solve this problem.
You are given an array $(A1,A2,A3……AN)$ of length $N$. You have to create an another array using the given array in the following ways:

For each valid i, the ith element of the output array will be the sum of the ith element and (A[i])th element if $A[i]$ is less equal $N$.

Other wise for each valid i following the step below

i) Divide the value of $A[i]$ by 2 untill it will be less than$N$.

ii) then find the difference ($D$) between $N$ and $A[i]$.

iii) the ith element of the output array will be $Dth$ element.  

-----Input:-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of T test cases follows.  
- The first line of each test case contains a single integer $N$.  
- The second line contains $N$ space-separated integers $A1,A2,…,AN$.   

-----Output:-----
- For each testcase, print new array in each line.

-----Constraints-----
- $1 \leq T \leq 1000$
- $1 \leq N \leq 10^5$
- $1\leq A1,A2.....AN \leq 10^7$

-----Sample Input:-----
2

5

2 4 5 7 9

4

5 4 2 3

-----Sample Output:-----
6 11 14 4 2

4 7 6 5

-----EXPLANATION:-----
For 1st test case: A1 = 2+4 =6, A2 = 4+7 =11 , A3 = 5+9 =14 , A4 > N (5) ,So A4/2 = 3 then A4 = A[5 -3] , A4=A[2]=4, And A5 =A[1]=2. Then array becomes 6,11,14,4,2.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded