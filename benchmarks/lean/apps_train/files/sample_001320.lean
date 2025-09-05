The students of Codechef Middle School are visiting an amusement park. The children want to go on a ride, however, there is a minimum height requirement of $X$ cm. Determine if the children are eligible to go on the ride. 
Print "Yes" if they are eligible, "No" otherwise.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, two integers $H$ which is a child's height in cm and $X$ which is the minimum permissible height. 

-----Output:-----
For each testcase, output in a single line $"Yes"$ or $"No"$. You cannot give your answer as "YeS", "YES", "yes" or any other variation.

-----Constraints-----
- $1 \leq T \leq 10^4$
- $50 \leq H \leq 200$
- $50 \leq X \leq 200$

-----Sample Input:-----
2
120 100
90 100

-----Sample Output:-----
Yes
No

-----EXPLANATION:-----
The first child has height more than minimum permissible height, so he can go on the ride while the other person cannot!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded