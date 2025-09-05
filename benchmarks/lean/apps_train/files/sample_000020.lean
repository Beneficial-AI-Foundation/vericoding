Gildong owns a bulgogi restaurant. The restaurant has a lot of customers, so many of them like to make a reservation before visiting it.

Gildong tries so hard to satisfy the customers that he even memorized all customers' preferred temperature ranges! Looking through the reservation list, he wants to satisfy all customers by controlling the temperature of the restaurant.

The restaurant has an air conditioner that has 3 states: off, heating, and cooling. When it's off, the restaurant's temperature remains the same. When it's heating, the temperature increases by 1 in one minute. Lastly, when it's cooling, the temperature decreases by 1 in one minute. Gildong can change the state as many times as he wants, at any integer minutes. The air conditioner is off initially.

Each customer is characterized by three values: $t_i$ — the time (in minutes) when the $i$-th customer visits the restaurant, $l_i$ — the lower bound of their preferred temperature range, and $h_i$ — the upper bound of their preferred temperature range.

A customer is satisfied if the temperature is within the preferred range at the instant they visit the restaurant. Formally, the $i$-th customer is satisfied if and only if the temperature is between $l_i$ and $h_i$ (inclusive) in the $t_i$-th minute.

Given the initial temperature, the list of reserved customers' visit times and their preferred temperature ranges, you're going to help him find if it's possible to satisfy all customers.

-----Input-----

Each test contains one or more test cases. The first line contains the number of test cases $q$ ($1 \le q \le 500$). Description of the test cases follows.

The first line of each test case contains two integers $n$ and $m$ ($1 \le n \le 100$, $-10^9 \le m \le 10^9$), where $n$ is the number of reserved customers and $m$ is the initial temperature of the restaurant.

Next, $n$ lines follow. The $i$-th line of them contains three integers $t_i$, $l_i$, and $h_i$ ($1 \le t_i \le 10^9$, $-10^9 \le l_i \le h_i \le 10^9$), where $t_i$ is the time when the $i$-th customer visits, $l_i$ is the lower bound of their preferred temperature range, and $h_i$ is the upper bound of their preferred temperature range. The preferred temperature ranges are inclusive.

The customers are given in non-decreasing order of their visit time, and the current time is $0$.

-----Output-----

For each test case, print "YES" if it is possible to satisfy all customers. Otherwise, print "NO".

You can print each letter in any case (upper or lower).

-----Example-----
Input
4
3 0
5 1 2
7 3 5
10 -1 0
2 12
5 7 10
10 16 20
3 -100
100 0 0
100 -50 50
200 100 100
1 100
99 -100 0

Output
YES
NO
YES
NO

-----Note-----

In the first case, Gildong can control the air conditioner to satisfy all customers in the following way:  At $0$-th minute, change the state to heating (the temperature is 0).  At $2$-nd minute, change the state to off (the temperature is 2).  At $5$-th minute, change the state to heating (the temperature is 2, the $1$-st customer is satisfied).  At $6$-th minute, change the state to off (the temperature is 3).  At $7$-th minute, change the state to cooling (the temperature is 3, the $2$-nd customer is satisfied).  At $10$-th minute, the temperature will be 0, which satisfies the last customer. 

In the third case, Gildong can change the state to heating at $0$-th minute and leave it be. Then all customers will be satisfied. Note that the $1$-st customer's visit time equals the $2$-nd customer's visit time.

In the second and the fourth case, Gildong has to make at least one customer unsatisfied.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded