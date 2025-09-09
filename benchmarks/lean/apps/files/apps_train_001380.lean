/-
After the hundred years of war started by the Fire Nation, its time for the Water Tribes to bring it to an end. Avatar asked Sokka to go to the Southern WarZone from The Northern WarZone and gave him some money in a bag for his journey. Sokka has the World Map to guide him during his journey . The World Map is described as a $N$x$N$ grid where the Northern WarZone is denoted by $(0,0)$ and the Southern WarZone is denoted by $(N-1,N-1)$. Each location on the world map is denoted in a similar way by two integers r and c. For each location having:  
- $r = c$ denotes neutral land ( $(0,0)$ and $(N-1,N-1)$ also come under this category)       
- $r < c$ denotes the land under the rule of Water Tribes     
- $r > c$ denotes the land under the rule of Fire Kingdom   
Being wise Sokka travels only from one location to any other valid location (by valid location we mean a location which exists on the world map grid i.e. for that location $0 \leq r < N$ and $0 \leq c < N$ ) just to the right $(r,c+1)$ or below $(r+1,c)$ the current location randomly. Due to the times of war , Sokka has to pay one coin  each time he transitions from one nation to another. Here a transition is counted when Sokka is in Water Tribe land and moves to Fire Nation Land crossing the neutral land or vice versa .The first move is obviously never counted as a transition. Moreover , the coin is to be payed exactly once for one such transition (eg. if he makes this transition k times he has to pay k coins).  
The initial number of coins Sokka has is $2*N$. The probability that the coins he has when he reaches his destination is lesser than the number of coins he started his journey with can be expressed as a fraction $P/Q$, where P and Q are integers $(P \geq 0, Q > 0)$  and Q is co-prime with $(10^9)+7$. You should compute $P/Q$ modulo $(10^9)+7$ for $T$ values of $N$.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, one integer $N$, the size of the world map grid. 

-----Output:-----
For each testcase, output in a single line , the Probability modulo (10^9)+7.

-----Constraints-----
- $1 \leq T \leq 100000$
- $2 \leq N \leq 10^9$

-----Sample Input:-----
2    

5

2    

-----Sample Output:-----
200000002     

0  

-----EXPLANATION:-----
For N=2, there is no possible path in which Sokka has to spend money, so the final number of coins in the bag is not lesser than the initial amount.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_sokka_journey (n: Nat) : Nat :=
  sorry

theorem solve_sokka_journey_non_negative (n: Nat) (h: n ≥ 2) : 
  solve_sokka_journey n ≥ 0 := sorry

theorem solve_sokka_journey_less_than_modulo (n: Nat) (h: n ≥ 2) :
  solve_sokka_journey n < 1000000007 := sorry

theorem solve_sokka_journey_minimum_input :
  solve_sokka_journey 2 = 0 := sorry

theorem solve_sokka_journey_three_input :
  solve_sokka_journey 3 = 333333336 := sorry

/-
info: 200000002
-/
-- #guard_msgs in
-- #eval solve_sokka_journey 5

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_sokka_journey 2

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible