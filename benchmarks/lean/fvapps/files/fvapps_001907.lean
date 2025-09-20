-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_routes (locations : List Int) (start finish : Nat) (fuel : Nat) : Nat := sorry

def MOD := 1000000007
-- </vc-definitions>

-- <vc-theorems>
theorem count_routes_bounds 
  (locations : List Int)
  (start finish fuel : Nat)
  (h1 : ∀ x ∈ locations, 1 ≤ x ∧ x ≤ 1000)
  (h2 : 2 ≤ locations.length)
  (h3 : start < locations.length)
  (h4 : finish < locations.length)
  (h5 : fuel ≤ 200) :
  0 ≤ count_routes locations start finish fuel ∧ 
  count_routes locations start finish fuel < MOD := sorry

theorem zero_fuel_routes
  (locations : List Int)
  (start finish : Nat)
  (h1 : ∀ x ∈ locations, 1 ≤ x ∧ x ≤ 1000)
  (h2 : 2 ≤ locations.length)
  (h3 : start < locations.length)
  (h4 : finish < locations.length) :
  (count_routes locations start finish 0 > 0) ↔ (start = finish) := sorry

theorem self_routes_nonempty
  (locations : List Int)
  (fuel : Nat)
  (h1 : ∀ x ∈ locations, 1 ≤ x ∧ x ≤ 1000)
  (h2 : 2 ≤ locations.length) :
  count_routes locations 0 0 fuel ≥ 1 := sorry

theorem routes_symmetric
  (locations : List Int)
  (fuel : Nat)
  (h1 : ∀ x ∈ locations, 1 ≤ x ∧ x ≤ 1000)
  (h2 : 2 ≤ locations.length) :
  count_routes locations 0 1 fuel = count_routes locations 1 0 fuel := sorry

theorem more_fuel_more_routes
  (locations : List Int)
  (start finish : Nat)
  (fuel1 fuel2 : Nat)
  (h1 : ∀ x ∈ locations, 1 ≤ x ∧ x ≤ 1000)
  (h2 : 2 ≤ locations.length)
  (h3 : start < locations.length)
  (h4 : finish < locations.length)
  (h5 : fuel1 ≤ fuel2) :
  count_routes locations start finish fuel1 ≤ 
  count_routes locations start finish fuel2 := sorry
-- </vc-theorems>