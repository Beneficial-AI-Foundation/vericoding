For Diwali, Chef arranges all $K$ laddus in a row in his sweet shop. Whenever a customer comes to buy laddus, chef follows a rule that each customer must buy all laddus on odd position. After the selection of the laddu, a new row is formed, and again out of these only laddus on odd position are selected. This continues until the chef left with the last laddu. Find out the position of that last laddu in the original row.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, one integer $K$. 

-----Output:-----
For each testcase, print the position of that laddu who is left, in the original row.

-----Constraints-----
- $1 \leq T \leq 10^5$
- $1 \leq K \leq 10^5$

-----Sample Input:-----
3
1
5
8

-----Sample Output:-----
1
4
8

-----EXPLANATION:-----
For 1) Only one laddu which is last so print 1.
For 2) Customer 1: [1, 3, 5]
New row = [2, 4]

Customer 2: [2]

Last laddu = 4

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
