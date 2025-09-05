You have a laser with P amount of energy in it. You are playing a game where you have to use the laser to destroy some crystals, each with some health of their own. Initially, you have 0 points.
Each crystal has an associated health. The health of the ith crystal is given by health[i]. You can perform one of the two actions:
- 
At the cost of health[i] energy, you can destroy the ith crystal and gain 1 point. You can only perform this action if your laser has atleast health[i] energy in it.
- 
At the cost of 1 point, you can destroy the ith crystal and refuel the laser's energy by an amount equal to health[i]. This action can only be performed if you have atleast one point.
Note: Each crystal can only be destroyed once.
Determine the maximum number of points you can obtain by destroying any number of crystals and performing either action as you wish.

-----Input:-----
- First line will contain n, number of crystals. 
- Second line will contain space separated integers, health of each crystal.
- Third line will contain an integer P, initial energy of the laser.

-----Output:-----
Print the largest number of points we can have after destroying any number of crystals.

-----Constraints-----
- health.length <= 1000
- 0 <= health[i] < 10000
- 0 <= P < 10000

-----Subtasks-----
- 40 points : 1 <= health.length <= 100
- 60 points : health.length > 100

-----Sample Input 1:-----
1
200
100

-----Sample Output 1:-----
0

-----Explanation:-----
The laser initially has only 100 energy. Since the only crystal requires 200 energy to destroy, we cannot perform any action here, and the game ends. The number of points is zero.

-----Sample Input 2:-----
2
100 200
150

-----Sample Output 2:-----
1

-----Explanation:-----
The laser has 150 energy. We can consume 100 energy and destroy the first crystal and gain 1 point. The remaining energy is 50, which is not enough to destroy the other crystal. We end the game here as we have the maximum possible points attainable.

def game (n : Nat) (health : List Nat) (laser_energy : Nat) : Nat :=
  sorry

def listMin (l : List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded