-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_subway_escape (grid : List String) (n k : Nat) : String := sorry

theorem check_subway_escape_returns_valid_output 
  (n k: Nat) 
  (h1: n ≥ 5) (h2: n ≤ 20) (h3: k ≥ 1) (h4: k ≤ 10) :
  let grid := [
    String.mk (List.replicate n '.'),
    String.mk ('s' :: List.replicate (n-1) '.'),
    String.mk (List.replicate n '.')
  ]
  let result := check_subway_escape grid n k
  result = "YES" ∨ result = "NO" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_path_possible
  (n: Nat)
  (h1: n ≥ 5) (h2: n ≤ 20) :
  let grid := [
    String.mk (List.replicate n '.'),
    String.mk ('s' :: List.replicate (n-1) '.'),
    String.mk (List.replicate n '.')
  ]
  check_subway_escape grid n 4 = "YES" := sorry

theorem blocked_path_impossible
  (n: Nat)
  (h1: n ≥ 5) (h2: n ≤ 20) :
  let grid := [
    String.mk (List.replicate n 'A'),
    String.mk ('s' :: List.replicate (n-1) 'A'),
    String.mk (List.replicate n 'A')
  ]
  check_subway_escape grid n 4 = "NO" := sorry

theorem minimal_grid_escape_possible :
  check_subway_escape ["...", "s..", "..."] 3 1 = "YES" := sorry
-- </vc-theorems>