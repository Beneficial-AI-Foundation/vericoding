/-
Our chef has recently opened a new restaurant with a unique style. The restaurant is divided into K compartments (numbered from 1 to K) and each compartment can be occupied by at most one customer. 
Each customer that visits the restaurant has a strongly preferred compartment p (1 ≤ p ≤ K), and if that compartment is already occupied, then the customer simply leaves. Now obviously, the chef wants to maximize the total number of customers that dine at his restaurant and so he allows (or disallows) certain customers so as to achieve this task. You are to help him with this. 
Given a list of N customers with their arrival time, departure time and the preferred compartment, you need to calculate the maximum number of customers that can dine at the restaurant. 

-----Input-----
The first line contains an integer T denoting the number of test cases. Each of the next T lines contains two integers N and  K , the number of customers that plan to visit the chef's restaurant and the number of compartments the restaurant is divided into respectively. Each of the next N lines contains three integers si, fi and pi , the arrival time, departure time and the strongly preferred compartment of the ith customer respectively.  

Note that the ith customer wants to occupy the pith compartment from [si, fi)  i.e the ith customer leaves just before   fi  so that another customer can occupy that compartment from   fi  onwards.

-----Output-----
For every test case, print in a single line the maximum number of customers that dine at the restaurant.

-----Constraints-----
-  1 ≤  T ≤   30 
-  0  ≤ N  ≤  105 
-  1  ≤  K  ≤  109 
-  0  ≤  si < fi ≤   109 
-  1  ≤  pi  ≤  K  

-----Example-----
Input:
2
3 3
1 3 1
4 6 2
7 10 3
4 2
10 100 1
100 200 2
150 500 2
200 300 2

Output:
3
3

-----Explanation-----
Example case 1.

All three customers want different compartments and hence all 3 can be accommodated.

Example case 2.

If we serve the 1st, 2nd and 4th customers, then we can get a maximum of 3.
-/

-- <vc-helpers>
-- </vc-helpers>

def maxRestaurantCustomers (testCases : List (List Cell)) : List Nat :=
  sorry

theorem max_customers_single_case
  (n k : Nat)
  (cells : List Cell)
  (h1 : n ≥ 1)
  (h2 : k ≥ 1) 
  (h3 : cells.length ≥ 1)
  (h4 : ∀ c ∈ cells, c.start < c.finish)
  (h5 : ∀ c ∈ cells, c.capacity ≤ k) :
  let result := maxRestaurantCustomers [cells]
  result.head! ≤ cells.length ∧ 
  result.head! ≤ k * n :=
sorry

theorem max_customers_multiple_cases
  (testCases : List (List Cell))
  (h1 : testCases.length ≥ 1)
  (h2 : ∀ case ∈ testCases, case.length ≥ 1)
  (h3 : ∀ case ∈ testCases, ∀ c ∈ case, c.start < c.finish)
  (h4 : ∀ case ∈ testCases, ∀ c ∈ case, c.capacity ≤ k) :
  let results := maxRestaurantCustomers testCases
  results.length = testCases.length ∧
  ∀ i < results.length, 
    results[i]! ≤ testCases[i]!.length ∧
    results[i]! ≤ k * n :=
sorry

/-
info: [3]
-/
-- #guard_msgs in
-- #eval max_restaurant_customers [test1]

/-
info: [3]
-/
-- #guard_msgs in
-- #eval max_restaurant_customers [test2]

/-
info: [3, 3]
-/
-- #guard_msgs in
-- #eval max_restaurant_customers [test1, test2]

-- Apps difficulty: interview
-- Assurance level: unguarded