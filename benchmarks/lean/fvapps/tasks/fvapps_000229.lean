-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def regions_by_slashes (grid: List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem regions_always_positive
  (grid: List String)
  : regions_by_slashes grid > 0 :=
  sorry 

theorem regions_bounded_by_size
  (grid: List String)
  (h: grid.length = n)
  : regions_by_slashes grid ≤ 4 * n * n :=
  sorry

theorem empty_grid_one_region
  (grid: List String)
  (h1: grid.length > 0)
  (h2: ∀ row ∈ grid, row = (String.mk $ List.replicate 10 ' '))
  : regions_by_slashes grid = 1 :=
  sorry

theorem quotes_irrelevant
  (grid: List String)
  (quoted: List String)
  (h: quoted = grid.map (fun row => "\"" ++ row ++ "\""))
  : regions_by_slashes grid = regions_by_slashes quoted :=
  sorry
-- </vc-theorems>