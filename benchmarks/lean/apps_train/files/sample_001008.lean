“I am not in danger, Skyler. I am the danger. A guy opens his door and gets shot, and you think that of me? No! I am the one who knocks!”
Skyler fears Walter and ponders escaping to Colorado. Walter wants to clean his lab as soon as possible and then go back home to his wife. 
In order clean his lab, he has to achieve cleaning level of lab as $Y$. The current cleaning level of the lab is $X$. 
He must choose one positive odd integer $a$ and one positive even integer $b$. Note that, he cannot change $a$ or $b$ once he starts cleaning.
He can perform any one of the following operations for one round of cleaning:  
- Replace $X$ with $X+a$.  
- Replace $X$ with $X-b$.
Find minimum number of rounds (possibly zero) to make lab clean.

-----Input:-----
- First line will contain $T$, number of test cases. $T$ testcases follow :  
- Each test case contains two space separated integers $X, Y$. 

-----Output:-----
For each test case, output an integer denoting minimum number of rounds to clean the lab.

-----Constraints-----
- $1 \leq T \leq 10^5$
- $ |X|,|Y| \leq 10^9$

-----Sample Input:-----
3
0 5
4 -5
0 10000001

-----Sample Output:-----
1
2
1

-----EXPLANATION:-----
- 
For the first testcase, you can convert $X$ to $Y$  by choosing $a=5$ and $b=2$.

It will cost minimum of $1$ cleaning round. You can select any other combination of $a, b$ satisfying above condition but will take minimum of $1$ cleaning round in any case.
- 
For the second testcase, you can convert $X$ to $Y$ by choosing $a=1$ and $b=10$. In first round they will replace $X$ to $X+a$ and then in second round replace to $X-b$. You can perform only one operation in one round.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded