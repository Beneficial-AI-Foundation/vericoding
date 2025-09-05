Mia is working as a waitress at a breakfast diner. She can take up only one shift from 6 shifts a day i.e. from 10 am to 4 pm. She needs to save 300$ after completion of the month. She works only for $D$ days in the month. She estimates that she gets her highest tip in the first shift and the tip starts decreasing by 2% every hour as the day prolongs. She gets a minimum wage of $X$ $ for every shift. And her highest tip in the first shift is $Y$ $. Determine whether Mia will be able to save 300$ from her wages and tips after working $D$ days of the month. If she can, print YES, else print NO.

-----Constraints-----
- 8 <= D <=30
- 7 <= X <=30
- 4 <= Y <= 20

-----Input:-----
- First line has three parameters $D$, $X$ and $Y$ i.e. number of days worked, minimum wage and highest tip.
- Second line contains D integers indicating her shifts every $i$-th day she has worked.

-----Output:-----
- Print YES, if Mia has saved 300$, NO otherwise.

-----Sample Input:-----
9 17 5
1 3 2 4 5 6 1 2 2

-----Sample Output:-----
NO

-----Explanation:-----
No. of days Mia worked (D) is 9, so minimum wage she earns (X) is 17 dollars. Highest tip at first hour (Y) = 5 dollars, 1st day she took 1st shift and 2nd day she took 3rd shift and so on. Upon calculation we will find that Mia was not able to save 300 dollars.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded