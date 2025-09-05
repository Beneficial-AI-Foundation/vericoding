Tired of the overpopulated world, Miu - The introverted cat visits a new continent in search for a new house.  
There are $N$ houses lying on the X-axis.

Their positions are given by $X$$i$ , where $i$ refers to the $i$th house. ( $1 <= i <= N$ )

Each of these positions are pairwise distinct 
Miu is supposed to choose one of these houses for herself.

Miu defines a term - The Distance of Peace,  as the minimum distance from her house to any other house.  
Miu wonders what is maximum Distance of Peace she can obtain. Can you help her?

-----Input:-----
- The first line of the input consists of a single integer $T$, denoting the number of test cases  
- The first line of each test case consists of a single integer $N$ 
- The second line of each test case consists of $N$ space-separated integers
$X$$1$ $X$$2$ $X$$3$ … $X$$N$

-----Output:-----
- For each test case print the answer in a single line, the maximum Distance of Peace Miu can obtain

-----Constraints-----
- 1 <= $T$ <= 100  
- 2 <= $N$ <= 105 
- -109 <= $X$$i$ <= 109 
- Sum of $N$ over all test cases does not exceed 106 

-----Subtasks-----
Subtask #1 (30 points): 
- $N$ <= 103 
Subtask #2 (70 points): 
- Original Constraints

-----Sample Input:-----
2

6

7 -1 2 13 -5 15

4

6 10 3 12  

-----Sample Output:-----
5

3  

-----EXPLANATION:-----
Test Case 1:

The $1$st house has the maximum Distance of Peace, which is from the $3$rd house:
$| 7 - 2 | = 5$

Hence, the answer is $5$

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
