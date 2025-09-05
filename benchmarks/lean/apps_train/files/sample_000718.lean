Rodriguez is a happy and content farmer. He has got a square field of side length $x$. Miguel, his son has himself grown into a man and his father wants to gift him something out of which he can make a living. So he gift's his son a square piece of land cut out from a corner of his field of side length $ y (y < x) $ leaving him with a L-shaped land.
But in Spanish tradition, it is considered inauspicious to own something which is prime in number. This worries Rodriguez as he doesn't want his left out area to be a prime number leading to bad luck. Find whether the spilt will be in terms with the tradition leaving Rodriguez happy.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains two integers $x, y$. 

-----Output:-----
Print YES if Rodriguez will be happy. Otherwise print NO.

-----Constraints-----
- $1 \leq T \leq 5$
- $1 \leq y < x \leq 100000000000$

-----Sample Input:-----
2
7 5
6 5

-----Sample Output:-----
YES
NO

-----EXPLANATION:-----
In case 1 :
Left out area is 24, which is not prime.
In case 2:
Left out area is 11, which is prime.

def is_prime (n : Nat) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded