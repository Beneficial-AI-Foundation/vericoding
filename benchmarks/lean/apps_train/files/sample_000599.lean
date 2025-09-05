There are $M$ levels for a building numbered from $1$ to $M$ from top to bottom, each level having $N$ parking spots numbered from $1$ to $N$ from left to right. Some spots might have a car while other may be empty, the information of which is given in form of two dimensional character array $C$ ($C_{i, j}$ denote parking spot at $j$-th position on $i$-th level).
There is a thief who wants to unlock all the cars. Now, he is skilled such that for the first time, he can directly reach in any parking spot in no time. Basically he can reach the first car to be stolen in 0 time.
Now, he can move within the parking lot only in following manner, each taking 1 unit of time:
- Move down a level. That is, if current position is $(i, j)$, then he reaches $(i+1, j)$
- If current position is $(i, j)$ and if
- $i$ is odd, then he can move from $(i, j)$ to $(i, j+1)$
- $i$ is even, then he can move from $(i, j)$ to $(i, j-1)$
Note that he wants to unlock the cars in minimum time and the car is unlocked as soon as the thief reaches that parking spot.If the parking lot is empty, then the time taken is considered to be 0.  
Find the minimum time when all the cars would be unlocked. Note that once all cars are unlocked, the thief can escape instantly, so this time does not count.

-----Input :-----
- The first line of input contains a single integer $T$ (number of test cases).
- First liine of each test case contains $M$ and $N$(number of levels and spots per each level)  
- Next $M$ line contains $N$ space separated characters $C_{i, 1}, C_{i, 2} \ldots C_{i, N}$  where $(1\leq i\leq M)$ and $C_{i, j}$ is either $'P'$ or $'N'$ (without quotes).
If the spot contains $'P'$, then a car is parked there. else, it’s not parked.

-----Output :-----
For each test case print a single integer, the minimum time in which thief can unlock all cars.

-----Constraints :-----
- $1\leq T \leq100.$ 
- $1\leq M,N \leq300$ 

-----Subtasks :-----
- 
Subtask 1 (20 points): $1\leq M \leq2.$ 
- 
Subtask 2 (80 points): Original Constraints

-----Sample Input :-----
2
4 5
N P N N P
N N P N N
N P N N N
P N N N N
3 3
N P P
P P P 
P P N

-----Sample Output :-----
10
6

-----Explanation:-----
In the first case, He will select the spot $(1,2)$ and the path he takes will be $(1,2)→(1,3)→(1,4)→(1,5)→(2,5)→(2,4)→(2,3)→(2,2)→(3,2)→(4,2)→(4,1)$

So, he takes 10 steps to unlock all the cars.
In the second case, He will select the spot $(1,2)$ and the path he takes will be $(1,2)→(1,3)→(2,3)→(2,2)→(2,1)→(3,1)→(3,2)$.
So, he takes 6 steps.

def solve_parking_thief (m n : Nat) (grid : List (List Char)) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
