Maxim always goes to the supermarket on Sundays. Today the supermarket has a special offer of discount systems.

There are m types of discounts. We assume that the discounts are indexed from 1 to m. To use the discount number i, the customer takes a special basket, where he puts exactly q_{i} items he buys. Under the terms of the discount system, in addition to the items in the cart the customer can receive at most two items from the supermarket for free. The number of the "free items" (0, 1 or 2) to give is selected by the customer. The only condition imposed on the selected "free items" is as follows: each of them mustn't be more expensive than the cheapest item out of the q_{i} items in the cart.

Maxim now needs to buy n items in the shop. Count the minimum sum of money that Maxim needs to buy them, if he use the discount system optimally well.

Please assume that the supermarket has enough carts for any actions. Maxim can use the same discount multiple times. Of course, Maxim can buy items without any discounts.

-----Input-----

The first line contains integer m (1 ≤ m ≤ 10^5) — the number of discount types. The second line contains m integers: q_1, q_2, ..., q_{m} (1 ≤ q_{i} ≤ 10^5). 

The third line contains integer n (1 ≤ n ≤ 10^5) — the number of items Maxim needs. The fourth line contains n integers: a_1, a_2, ..., a_{n} (1 ≤ a_{i} ≤ 10^4) — the items' prices.

The numbers in the lines are separated by single spaces.

-----Output-----

In a single line print a single integer — the answer to the problem.

-----Examples-----
Input
1
2
4
50 50 100 100

Output
200

Input
2
2 3
5
50 50 50 50 50

Output
150

Input
1
1
7
1 1 1 1 1 1 1

Output
3

-----Note-----

In the first sample Maxim needs to buy two items that cost 100 and get a discount for two free items that cost 50. In that case, Maxim is going to pay 200.

In the second sample the best strategy for Maxim is to buy 3 items and get 2 items for free using the discount. In that case, Maxim is going to pay 150.

def solve_discount_shopping (n_discounts : Nat) (discount_values : List Nat) (n_items : Nat) (item_values : List Nat) : Nat :=
  sorry

def list_sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h :: t => h + list_sum t

def list_sort (l : List Nat) : List Nat :=
  sorry

def list_take (n : Nat) (l : List Nat) : List Nat :=
  match n, l with
  | 0, _ => []
  | _, [] => []
  | n+1, h :: t => h :: list_take n t

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded
