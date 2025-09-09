/-
The country has n cities and n - 1 bidirectional roads, it is possible to get from every city to any other one if you move only along the roads. The cities are numbered with integers from 1 to n inclusive.

All the roads are initially bad, but the government wants to improve the state of some roads. We will assume that the citizens are happy about road improvement if the path from the capital located in city x to any other city contains at most one bad road.

Your task is — for every possible x determine the number of ways of improving the quality of some roads in order to meet the citizens' condition. As those values can be rather large, you need to print each value modulo 1 000 000 007 (10^9 + 7).

-----Input-----

The first line of the input contains a single integer n (2 ≤ n ≤ 2·10^5) — the number of cities in the country. Next line contains n - 1 positive integers p_2, p_3, p_4, ..., p_{n} (1 ≤ p_{i} ≤ i - 1) — the description of the roads in the country. Number p_{i} means that the country has a road connecting city p_{i} and city i. 

-----Output-----

Print n integers a_1, a_2, ..., a_{n}, where a_{i} is the sought number of ways to improve the quality of the roads modulo 1 000 000 007 (10^9 + 7), if the capital of the country is at city number i.

-----Examples-----
Input
3
1 1

Output
4 3 3
Input
5
1 2 3 4

Output
5 8 9 8 5
-/

-- <vc-helpers>
-- </vc-helpers>

def solve (n : Nat) (parents : List Nat) : List Nat := sorry

theorem solve_chain_properties (n : Nat) (parents : List Nat) 
    (h1 : n ≥ 2)
    (h2 : parents = List.range (n-1)) : 
    let result := solve n parents
    -- Result length equals input size
    List.length result = n ∧ 
    -- First element equals last element (symmetry)
    List.get! result 0 = List.get! result (n-1) ∧
    -- All values are non-negative
    ∀ x ∈ result, x ≥ 0 := sorry

theorem solve_star_properties (n : Nat) (parents : List Nat)
    (h1 : n ≥ 2) 
    (h2 : parents = List.replicate (n-1) 1) :
    let result := solve n parents
    -- Result length equals input size
    List.length result = n ∧
    -- All elements are natural numbers
    ∀ x ∈ result, x ≥ 0 := sorry

/-
info: [4, 3, 3]
-/
-- #guard_msgs in
-- #eval solve 3 [1, 1]

/-
info: [5, 8, 9, 8, 5]
-/
-- #guard_msgs in
-- #eval solve 5 [1, 2, 3, 4]

/-
info: [2, 2]
-/
-- #guard_msgs in
-- #eval solve 2 [1]

-- Apps difficulty: competition
-- Assurance level: unguarded