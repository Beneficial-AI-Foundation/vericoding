The land of Programmers Army is surrounded by many islands. A unique number is associated with each island. The king of the islands is a very generous person, he donates a certain amount of gold coins to travelers for visiting each island that they visited to.
Now, you are appointed as a traveler, who will travel to all these(or some) islands as many times as the Army wants, and you will collect gold coins from the king of the island.
In each trip, you will be asked to give the total sum of gold coins you have collected.

-----Input:-----
- The first line of the input contains a single integer $T$. $T$ denoting the number of test cases. The description of $T$ test cases is as follows.
- The next line of the input contains a single integer $N$. $N$ denotes the total number of Islands.
- The next line of the input contains $N$ space-separated integers $A1, A2, A3...An$ where $ith$ number denotes the maximum number of coins that the king of $ith$ island can donate.
- Next line contains a single integer $Q$. $Q$ denotes the total number of times traveler have to go for the trip.
- Next $Q$ lines contains, two space-separated integers $Q1,Q2$ denoting the start and end number of islands, i.e. traveler will start the trip from $Q1th$ island and will go till $Q2th$ island, in each trip.
Note: islands are numbered from $1$ to $N$.

-----Output:-----
- For each trip print the total number of gold coins, traveler will collect(each on a new line).

-----Constraints:-----
- $1 \leq T \leq 100$
- $1 \leq N \leq 10^4$
- $1 \leq A1, A2, A3...An \leq 10^5$
- $1 \leq Q \leq 10^3$
- $1 \leq Q1,Q2 \leq N$

-----Sample Input:-----
1
4
10 2 5 50
2
1 3
2 4

-----Sample Output:-----
17
57

-----Explanation:-----
- 
In 1st Trip, traveler will go from 1st Island to 3rd Island, hence the total number of coins traveler can collect is 10+2+5 = 17
- 
In 2 d Trip, traveler will go from 2nd Island to 4th Island, hence the total number of coins traveler can collect is 2+5+50 = 57

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded