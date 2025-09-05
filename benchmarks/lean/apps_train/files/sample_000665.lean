Congratulations !!! You have successfully completed the heist by looting all the gifts in Santa's locker. Now it's time to decide who gets to take all the gifts, you or the Grinch, there will be no splitting. So you and Grinch decide to play a game.
To start the game, an Integer N will be given. The game is played in turns and for each turn, the player can make any one of the following moves:
- Divide N by any of it's odd divisors greater than 1.
- Subtract 1 from N if N is greater than 1.
Divisor of a number includes the number itself.
The player who is unable to make a move loses the game.
Since you are the mastermind of the heist, you get to play the first move.

-----Input-----
The first line contains a single integer T (1 ≤ T ≤ 100) — the number of test cases. The description of the test cases follows.
The only line of each test case contains a single integer — N (1 ≤ N ≤ 109).

-----Output-----
For each test case, print " Me" if you win, and " Grinch" if otherwise (without quotes).

-----Sample Input-----
7
1
2
3
4
5
6
12

-----Sample Output-----
Grinch
Me
Me
Grinch
Me
Grinch
Me

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
