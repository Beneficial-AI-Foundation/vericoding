-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numBusesToDestination (routes: List (List Nat)) (source: Nat) (target: Nat) : Int :=
  sorry

def findMaxInList (l: List Nat) : Nat :=
  sorry

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
-- </vc-theorems>