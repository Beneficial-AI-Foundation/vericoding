There are $X$ people participating in a quiz competition and their IDs have been numbered from $1$ to $X$ (both inclusive). Beth needs to form a team among these $X$ participants. She has been given an integer $Y$. She can choose participants whose ID numbers are divisible by $Y$. 
Now that the team is formed, Beth wants to know the strength of her team. The strength of a team is the sum of all the last digits of the team members’ ID numbers.
Can you help Beth in finding the strength of her team?

-----Input:-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. $T$ lines follow 
- The first line of each test case contains $X$ and $Y$. 

-----Output:-----
- For each test case print the strength of Beth's team

-----Constraints-----
- $1 \leq T \leq 1000$
- $1 \leq X,Y \leq 10^{20}$

-----Sample Input:-----
2
10 3

15 5

-----Sample Output:-----
18 

10

-----EXPLANATION:-----
- Example case 1: ID numbers divisible by 3 are 3,6,9 and the sum of the last digits are 3+6+9=18

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded