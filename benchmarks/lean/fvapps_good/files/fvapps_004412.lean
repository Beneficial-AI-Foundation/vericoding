-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def conference_picker (visited offered : List String) : String := sorry

-- if result is not "No worthwhile conferences this year!", then:
-- 1. result must be in offered cities
-- 2. result must not be in visited cities
-- else all offered cities must be in visited cities
-- </vc-definitions>

-- <vc-theorems>
theorem result_validity (visited offered : List String) :
  let result := conference_picker visited offered
  match result with
  | "No worthwhile conferences this year!" => ∀ city, city ∈ offered → city ∈ visited
  | other => other ∈ offered ∧ other ∉ visited
  := sorry

-- if all cities in offered list are also in visited list, result is "No worthwhile conferences this year!"

theorem all_cities_visited_returns_no_conferences (cities : List String) : 
  conference_picker cities cities = "No worthwhile conferences this year!" := sorry

-- if there is exactly one new city offered that hasn't been visited,
-- that city will be returned

theorem single_new_city_is_returned (visited : List String) (new_city : String)
  (h : new_city ∉ visited) :
  conference_picker visited [new_city] = new_city := sorry
-- </vc-theorems>