/-
There are N gas stations along a circular route, where the amount of gas at station i is gas[i].

You have a car with an unlimited gas tank and it costs cost[i] of gas to travel from station i to its next station (i+1). You begin the journey with an empty tank at one of the gas stations.

Return the starting gas station's index if you can travel around the circuit once in the clockwise direction, otherwise return -1.

Note:

       If there exists a solution, it is guaranteed to be unique.
       Both input arrays are non-empty and have the same length.
       Each element in the input arrays is a non-negative integer.

Example 1:

Input: 
gas  = [1,2,3,4,5]
cost = [3,4,5,1,2]

Output: 3

Explanation:
Start at station 3 (index 3) and fill up with 4 unit of gas. Your tank = 0 + 4 = 4
Travel to station 4. Your tank = 4 - 1 + 5 = 8
Travel to station 0. Your tank = 8 - 2 + 1 = 7
Travel to station 1. Your tank = 7 - 3 + 2 = 6
Travel to station 2. Your tank = 6 - 4 + 3 = 5
Travel to station 3. The cost is 5. Your gas is just enough to travel back to station 3.
Therefore, return 3 as the starting index.

Example 2:

Input: 
gas  = [2,3,4]
cost = [3,4,3]

Output: -1

Explanation:
You can't start at station 0 or 1, as there is not enough gas to travel to the next station.
Let's start at station 2 and fill up with 4 unit of gas. Your tank = 0 + 4 = 4
Travel to station 0. Your tank = 4 - 3 + 2 = 3
Travel to station 1. Your tank = 3 - 3 + 3 = 3
You cannot travel back to station 2, as it requires 4 unit of gas but you only have 3.
Therefore, you can't travel around the circuit once no matter where you start.
-/

-- <vc-helpers>
-- </vc-helpers>

def can_complete_circuit (gas : List Nat) (cost : List Nat) : Int := sorry

theorem can_complete_circuit_valid_result {gas cost : List Nat} (h: gas.length > 0) (h2: cost.length > 0) :
  let result := can_complete_circuit gas cost
  result = -1 ∨ (0 ≤ result ∧ result < gas.length) := sorry

theorem insufficient_gas_implies_no_solution {gas cost : List Nat} (h: gas.length > 0) (h2: cost.length > 0) :
  (gas.foldl (· + ·) 0 < cost.foldl (· + ·) 0) →
  can_complete_circuit gas cost = -1 := sorry

theorem valid_result_implies_complete_circuit {gas cost : List Nat} (h: gas.length > 0) (h2: cost.length > 0) :
  let result := can_complete_circuit gas cost
  result ≠ -1 →
  ∀ i : Nat, i < gas.length →
  let tank := List.range i |>.foldl (fun acc j => 
    acc + gas[(result.toNat + j) % gas.length]! - cost[(result.toNat + j) % gas.length]!) 0
  tank ≥ 0 := sorry

theorem identical_gas_cost {values : List Nat} (h: values.length > 0) :
  can_complete_circuit values values = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval can_complete_circuit [1, 2, 3, 4, 5] [3, 4, 5, 1, 2]

/-
info: -1
-/
-- #guard_msgs in
-- #eval can_complete_circuit [2, 3, 4] [3, 4, 3]

/-
info: 4
-/
-- #guard_msgs in
-- #eval can_complete_circuit [5, 1, 2, 3, 4] [4, 4, 1, 5, 1]

-- Apps difficulty: interview
-- Assurance level: unguarded