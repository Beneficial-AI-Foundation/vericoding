-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (x : Int) : Int :=
sorry

def min_travel_time (n a b c d p q y : Nat) (cities : List Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_travel_time_non_negative (n a b c d p q y : Nat) (cities : List Int)
  (h1 : n ≥ 4) (h2 : n ≤ 100)
  (h3 : p ≥ 1) (h4 : p ≤ 100)
  (h5 : q ≥ 1) (h6 : q ≤ 100)
  (h7 : y ≤ 100000)
  (h8 : cities.length ≥ 4) (h9 : cities.length ≤ 100)
  (h10 : ∀ x ∈ cities, -100000 ≤ x ∧ x ≤ 100000)
  (h11 : a = 1) (h12 : b = 3)
  (h13 : c = 2) (h14 : d = 4) :
  min_travel_time n a b c d p q y cities ≥ 0 :=
sorry

theorem min_travel_time_upper_bound (n a b c d p q y : Nat) (cities : List Int)
  (h1 : n ≥ 4) (h2 : n ≤ 100)
  (h3 : p ≥ 1) (h4 : p ≤ 100)
  (h5 : q ≥ 1) (h6 : q ≤ 100)
  (h7 : y ≤ 100000)
  (h8 : cities.length ≥ 4) (h9 : cities.length ≤ 100)
  (h10 : ∀ x ∈ cities, -100000 ≤ x ∧ x ≤ 100000)
  (h11 : a = 1) (h12 : b = 3)
  (h13 : c = 2) (h14 : d = 4) :
  min_travel_time n a b c d p q y cities ≤ (abs (cities[b-1] - cities[a-1])) * p :=
sorry

theorem min_travel_time_identical_cities (n a b c d p q y : Nat) (cities : List Int)
  (h1 : n ≥ 4) (h2 : n ≤ 100)
  (h3 : p ≥ 1) (h4 : p ≤ 100)
  (h5 : q ≥ 1) (h6 : q ≤ 100)
  (h7 : y ≤ 100000)
  (h8 : cities.length ≥ 4) (h9 : cities.length ≤ 100)
  (h10 : ∀ x ∈ cities, -100000 ≤ x ∧ x ≤ 100000)
  (h11 : a = 1) (h12 : b = 3)
  (h13 : c = 2) (h14 : d = 4)
  (h15 : cities[a-1] = cities[b-1]) :
  min_travel_time n a b c d p q y cities = 0 :=
sorry
-- </vc-theorems>