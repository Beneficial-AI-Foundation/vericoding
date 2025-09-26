-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_cheapest_price (n: Nat) (flights: List Flight) (src: Nat) (dst: Nat) (k: Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>