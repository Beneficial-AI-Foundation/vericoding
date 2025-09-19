-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_visit_cities (n : Nat) (d : Nat) (cities : List Nat) : String := sorry

theorem can_visit_cities_returns_yes_or_no 
  (n : Nat)
  (d : Nat) 
  (cities : List Nat)
  (h1 : n ≥ 2)
  (h2 : n ≤ 100) : 
  can_visit_cities n d cities = "YES" ∨ can_visit_cities n d cities = "NO" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem adjacent_diff_exceeds_d_implies_no
  (n : Nat)
  (d : Nat)
  (cities : List Nat)
  (h1 : n ≥ 2)
  (h2 : n ≤ 100)
  (i : Nat)
  (h3 : i < cities.length - 1)
  (h4 : match (cities.get? i), (cities.get? (i+1)) with
        | some x, some y => y > x + d
        | _, _ => False) :
  can_visit_cities n d cities = "NO" := sorry

theorem identical_temps_implies_yes
  (n : Nat)
  (h1 : n ≥ 2)
  (h2 : n ≤ 100) :
  let cities := List.replicate n 1
  can_visit_cities n 0 cities = "YES" := sorry
-- </vc-theorems>