/-
Lumpy is a bus driver. Today, the conductor is absent so Lumpy has to do the conductor's job as well. There are N creatures in the bus. Sometimes the creatures don't carry change and can't pay the exact amount of the fare. Each creature in the bus today has paid an amount
greater than his/her fare. You are given information about the extra amount paid by each creature, by an array A of size N, where Ai denotes the extra amount paid by the i-th creature, in rupees.
After the end of the trip, Lumpy noticed that he had P one rupee coins and Q two rupee coins. He wants to pay back the creatures using this money. Being a kind hearted moose, Lumpy wants to pay back as many creatures as he can. Note that Lumpy will 
not pay back the i-th creature if he can't pay the exact amount that the i-th creature requires with the coins that he possesses. 
Lumpy is busy driving the bus and doesn't want to calculate the maximum number of creatures he can satisfy - He will surely cause an accident if he tries to do so. Can you help him out with this task? 

-----Input-----
- The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.
- For each test case, first line consists of three space separated integers N, P and Q.
- Second line consists of N space separated integers A containing N space integers, where i-th integer denotes Ai.

-----Output-----
- For each test case, output a single line containing an integer corresponding to maximum number of creatures that Lumpy can pay back.

-----Constraints-----
- 1 ≤ T ≤ 106
- 1 ≤ N ≤ 105
- 1 ≤ Ai ≤ 109
- 0 ≤ P, Q ≤ 1014
- Sum of N over all the cases does not exceed 106

-----Subtasks-----
- Subtask #1 (15 points): P = 0
- Subtask #2 (15 points): Q = 0
- Subtask #3 (70 points): Original constraints

-----Example-----
Input:3
3 3 0
1 2 2
3 2 1
1 2 1
4 5 4
2 3 4 5

Output:2
3
3

-----Explanation-----
Example 1. Lumpy has just 3 one rupee coins. 

He can pay creatures numbered {1, 2} or creatures numbered {1, 3} with these coins. Thus, answer is 2. 
Example 2. Lumpy has 2 one rupee coins and 1 two rupee coin. 

In the optimal solution, Lumpy can give the two rupee coin to creature 2 and the one rupee coins to creatures 1 and 3. Thus, answer is 3.
-/

def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + sum xs

-- <vc-helpers>
-- </vc-helpers>

def List.sort : List Nat → List Nat := sorry

def solve_bus_payback (n p q : Nat) (amounts : List Nat) : Nat := sorry

theorem output_bounds (n p q : Nat) (amounts : List Nat) 
  (h : amounts.length = n) :
  let result := solve_bus_payback n p q amounts
  0 ≤ result ∧ result ≤ n := sorry

theorem zero_money_zero_creatures (n : Nat) (amounts : List Nat)
  (h : amounts.length = n) :
  solve_bus_payback n 0 0 amounts = 0 := sorry

theorem enough_money_even_amounts (n p q : Nat) (amounts : List Nat)
  (h1 : amounts.length = n)
  (h2 : ∀ i < n, amounts.get ⟨i, sorry⟩ = 2 * (i + 1))
  (h3 : p + 2*q ≥ List.sum amounts) :
  solve_bus_payback n p q amounts = n := sorry

theorem sorting_invariant (n p q : Nat) (amounts : List Nat)
  (h : amounts.length = n) :
  solve_bus_payback n p q amounts = 
  solve_bus_payback n p q (List.sort amounts) := sorry

-- Apps difficulty: interview
-- Assurance level: guarded