Oliver and Nova are true lovers. Inspite of knowing that Nova will die Oliver married her at the lake where they met. But they had a conflict about even and odd numbers. Nova likes the odd numbers and Oliver prefers even. One day they went to a fair where Oliver bought some square shaped marshmallows and Nova bought some round shaped. Then they decided to play a game. They will pick a natural number N . Nova will sum up the odd numbers from 1 to N and and she will notedown LCM of R(R is defined in the picture) and the sum she calculated before. And Oliver will sum up the even numbers from 1 to N and and he will notedown LCM of S(S is defined in the picture) and the sum he calculated before. You must use the ceil value of R and S.

Now  whose LCM is strictly greater than the other will win.If both of their LCM is equal Nova will win because Oliver is afraid of Nova.
$N.B.$ define the value of pi with $acos(-1)$.
$N.B.$ Sum of all odd number and sum of all even number will not exceed 10^18. 

-----Input:-----
The first line contains an integer $T$  — the number of test cases in the input. Next, T test cases are given, one per line.
Each test case is a positive integer $N$  . 

-----Output:-----
Print T answers to the test cases.
In each test cases,
If Oliver wins the game, print "Nova's gonna kill me" (without quotes) .
If Nova wins the game, print "YESS(sunglass emo)" (without quotes) .

-----Constraints-----
- $1 \leq T \leq 2000$
- $1 \leq N \leq 1845271$

-----Sample Input:-----
1
111

-----Sample Output:-----
YESS(sunglass emo)

def lcm (a b : Nat) : Nat := sorry
def gcd (a b : Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded