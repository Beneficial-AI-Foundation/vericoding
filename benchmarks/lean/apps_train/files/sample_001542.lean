Shivam owns a gambling house, which has a special wheel called The Wheel of Fortune. 
This wheel is meant for giving free coins to people coming in the house. 

The wheel of fortune is a game of chance. It uses a spinning wheel with exactly N numbered pockets and a coin is placed in between every consecutive pocket. The wheel is spun in either of the two ways.
Before the wheel is turned, all the coins are restored and players bet on a number K.
Then a needle is made to point to any one of the pocket which has number K written on it.
Wheel is then spun till the needle encounters number K again and the player gets all the coins the needle has encountered.

Shivam being the owner of the gambling house, has the authority to place the needle on any of the K numbered pockets and also he could rotate the wheel in either of the two ways.
Shivam has to figure out a way to minimize number of coins that he has to spend on every given bet.
You are given a wheel having N elements and Q players. Each player bets on a number K from the wheel. For each player you have to print minimum number of coins Shivam has to spend.

-----Input-----
- The first line of the input contains an integer T denoting the number of test cases . The description of T testcases follow.

- The first line of each test case contains single integer N .

- The second line of each test case contains N space seperated integers denoting the numbers on the wheel.

- The third line of each test case contains a single integer Q denoting the number of players.
- Then, Q lines follow a single integer K from the N numbers of the wheel 

-----Output-----
For each player, output the minimum number of coins Shivam has to spend.

-----Constraints-----

- 1 ≤ T ≤ 10
- 1 ≤ N ≤ 100000
- 1 ≤ Number written on the Wheel ≤ 1000
- 1 ≤ Q ≤ 10000
- 1 ≤ K ≤ 1000
-  It is guaranteed that K belongs to the N numbers written on the wheel.

-----Example-----
Input:

2

3

1 2 3

3

1

2

3

6

2 1 5 3 2 1

4

1

2

3

5
Output:

3

3

3

2

2

6

6

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded