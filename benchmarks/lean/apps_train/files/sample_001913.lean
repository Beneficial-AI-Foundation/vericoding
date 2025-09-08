/-
There are n cities connected by m flights. Each fight starts from city u and arrives at v with a price w.

Now given all the cities and fights, together with starting city src and the destination dst, your task is to find the cheapest price from src to dst with up to k stops. If there is no such route, output -1.

Example 1:
Input: 
n = 3, edges = [[0,1,100],[1,2,100],[0,2,500]]
src = 0, dst = 2, k = 1
Output: 200
Explanation: 
The graph looks like this:

The cheapest price from city 0 to city 2 with at most 1 stop costs 200, as marked red in the picture.

Example 2:
Input: 
n = 3, edges = [[0,1,100],[1,2,100],[0,2,500]]
src = 0, dst = 2, k = 0
Output: 500
Explanation: 
The graph looks like this:

The cheapest price from city 0 to city 2 with at most 0 stop costs 500, as marked blue in the picture.

Note:

       The number of nodes n will be in range [1, 100], with nodes labeled from 0 to n - 1.
       The size of flights will be in range [0, n * (n - 1) / 2].
       The format of each flight will be (src, dst, price).
       The price of each flight will be in the range [1, 10000].
       k is in the range of [0, n - 1].
       There will not be any duplicated flights or self cycles.
-/

-- <vc-helpers>
-- </vc-helpers>

def find_cheapest_price (n: Nat) (flights: List Flight) (src: Nat) (dst: Nat) (k: Nat) : Int :=
sorry

theorem price_non_negative
  (n: Nat) (flights: List Flight) (src dst k: Nat)
  (h1: src < n) (h2: dst < n) (h3: src ≠ dst) :
  let price := find_cheapest_price n flights src dst k
  price = -1 ∨ price ≥ 0 :=
sorry

theorem increasing_stops_never_increases_price 
  (n: Nat) (flights: List Flight) (src dst k1 k2: Nat)
  (h1: src < n) (h2: dst < n) (h3: src ≠ dst) (h4: k1 < k2) :
  let price1 := find_cheapest_price n flights src dst k1
  let price2 := find_cheapest_price n flights src dst k2
  price1 ≠ -1 → price2 ≠ -1 → price2 ≤ price1 :=
sorry

theorem direct_flights_independent_of_k
  (n: Nat) (flights: List Flight) (src dst: Nat)
  (h1: src < n) (h2: dst < n) (h3: src ≠ dst)
  (h4: ∃ f ∈ flights, f.src = src ∧ f.dst = dst) :
  let direct_price := find_cheapest_price n flights src dst 0
  let min_direct := List.foldl (fun acc f => 
    if f.src = src ∧ f.dst = dst 
    then min acc f.price
    else acc) 0 flights
  direct_price ≠ -1 → direct_price = min_direct :=
sorry

theorem triangular_path_property
  (n: Nat) (flights: List Flight) (src dst k: Nat)
  (h1: src < n) (h2: dst < n) (h3: src ≠ dst) (h4: k > 0)
  (h5: ∃ f ∈ flights, f.src = src ∨ f.dst = dst) :
  let price := find_cheapest_price n flights src dst k
  let min_edge := List.foldl (fun acc f =>
    if f.src = src ∨ f.dst = dst
    then min acc f.price 
    else acc) 0 flights
  price ≠ -1 ∧ min_edge > 0 → price ≥ min_edge :=
sorry

/-
info: 200
-/
-- #guard_msgs in
-- #eval find_cheapest_price 3 [[0, 1, 100], [1, 2, 100], [0, 2, 500]] 0 2 1

/-
info: 500
-/
-- #guard_msgs in
-- #eval find_cheapest_price n flights src dst 0

/-
info: 500
-/
-- #guard_msgs in
-- #eval find_cheapest_price 4 [[0, 1, 100], [1, 2, 100], [2, 3, 100], [0, 3, 500]] 0 3 1

-- Apps difficulty: interview
-- Assurance level: unguarded