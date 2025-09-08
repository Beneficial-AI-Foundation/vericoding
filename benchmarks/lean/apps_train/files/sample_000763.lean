/-
Naman owns a very famous Ice Cream parlour in Pune. He has a wide range of flavours with different pricing. 

Every flavour costs ₹ X per gram and quantity of each flavour in the parlour is indefinite. Now, Naman has 

received an order for a party wherein he is asked to prepare each Ice Cream with N number of flavours. 

He needs to prepare each Ice Cream of W grams and at the same time has to keep the cost minimum. 

Can you help him out?

Note: If it is not possible to prepare such an Ice Cream, print “Not Possible”.

-----Input:-----

First line contains an integer T denoting the number of test cases.

First line of every test case contains an integer N denoting the number of flavours.

The second line of every test case by N space separated integers denoting the cost per gram of each flavour. 

Second line of every test case contains two space separated integers W and Y denoting the weight 

of Ice Cream in grams and the number of flavours to be used respectively. 

-----Output:-----

For each test case, print the total cost of the Ice Cream in a single line.

-----Constraints:-----
1 ≤ T ≤ 100
1 ≤ N,W,Y ≤ 40000

-----Example:-----Input:
2
5 
4 6 8 1 10
10 3
2
1 2
1 2Output:

18

Not Possible

-----Explanation:-----

In the first test case to achieve the minimum cost, the Ice Cream will consist of 8 grams 

of flavour costing ₹1, 1 gram of flavour costing ₹4 and 1 gram of flavour costing ₹6.

In the second test case it is not possible to make an ice-cream weighing 1 gram using 2 flavours.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_ice_cream (num_flavors : Nat) (costs : List Nat) (weight num_required : Nat) : Option Nat :=
  sorry

theorem result_validity {num_flavors : Nat} {costs : List Nat} {weight num_required : Nat}
  (h1 : num_flavors > 0)
  (h2 : ∀ c ∈ costs, c > 0)
  (h3 : weight > 0)
  (h4 : num_required > 0) :
  match solve_ice_cream num_flavors costs weight num_required with
  | none => weight < num_required ∨ num_flavors < num_required
  | some result => result ≥ 0 ∧ weight ≥ num_required ∧ num_flavors ≥ num_required
  := sorry

theorem solution_monotonicity {costs : List Nat} {weight num_required : Nat}
  (h1 : List.length costs ≥ num_required) 
  (h2 : ∀ c ∈ costs, c > 0)
  (h3 : weight ≥ num_required)
  (h4 : num_required > 0) :
  let num_flavors := List.length costs
  let result1 := solve_ice_cream num_flavors costs weight num_required
  let result2 := solve_ice_cream num_flavors costs (weight + 1) num_required
  match result1, result2 with
  | some r1, some r2 => r2 ≥ r1
  | _, _ => True
  := sorry

theorem edge_cases {num_flavors : Nat} {costs : List Nat} {weight num_required : Nat}
  (h1 : num_flavors = 0 ∨ List.length costs = 0)
  (h2 : weight > 0)
  (h3 : num_required > 0) :
  solve_ice_cream num_flavors costs weight num_required = none
  := sorry

-- Apps difficulty: interview
-- Assurance level: guarded