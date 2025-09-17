-- <vc-preamble>
def numBusesToDestination (routes: List (List Nat)) (source: Nat) (target: Nat) : Int :=
  sorry

def findMaxInList (l: List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findMaxInRoutes (routes: List (List Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem impossible_path_property
  (routes: List (List Nat))
  (h: routes ≠ [])
  (h2: ∀ r ∈ routes, r ≠ []) : 
  let maxStop := findMaxInRoutes routes
  numBusesToDestination routes 0 (maxStop + 1) = -1 :=
sorry

theorem result_range_property
  (routes: List (List Nat))
  (h: routes ≠ [])
  (h2: ∀ r ∈ routes, r ≠ [])
  (start: Nat)
  (route: List Nat)
  (routeEnd: Nat)
  (h3: route ∈ routes)
  (h4: routeEnd ∈ route) :
  numBusesToDestination routes start routeEnd ≥ -1 := 
sorry

theorem empty_routes_property
  (routes: List (List Nat))
  (h: routes = [] ∨ routes = [[]]) :
  numBusesToDestination routes 1 2 = -1 := 
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval numBusesToDestination [[1, 2, 7], [3, 6, 7]] 1 6

/-
info: 2
-/
-- #guard_msgs in
-- #eval numBusesToDestination [[1, 2, 3], [3, 4, 5]] 1 5

/-
info: 3
-/
-- #guard_msgs in
-- #eval numBusesToDestination [[1, 2], [2, 3], [3, 4]] 1 4
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded