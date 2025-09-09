-- <vc-helpers>
-- </vc-helpers>

def count_robots (strings : List String) : List String := sorry

def String.containsSubstr (s : String) (substr : String) : Bool := sorry

theorem count_robots_output_format (strings : List String) :
  let result := count_robots strings
  result.length = 2 ∧ 
  result[0]!.endsWith "robots functioning automatik" ∧
  result[1]!.endsWith "robots dancing mechanik" ∧
  (∀ r ∈ result, (r.splitOn " ")[0]?.isSome) :=
sorry

theorem count_robots_invalid_input (strings : List String) :
  count_robots strings = ["0 robots functioning automatik", "0 robots dancing mechanik"] :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible