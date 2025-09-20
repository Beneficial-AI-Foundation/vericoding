-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def towerBuilder (n : Nat) (width height : Nat) : List String := sorry

theorem tower_builder_row_count
  {n width height : Nat}
  (h₁ : n > 0)
  (h₂ : width > 0)
  (h₃ : height > 0) :
  (towerBuilder n width height).length = n * height := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tower_builder_row_width
  {n width height : Nat}
  (h₁ : n > 0)
  (h₂ : width > 0)
  (h₃ : height > 0)
  (row : String)
  (h₄ : row ∈ towerBuilder n width height) :
  row.length = (2 * n - 1) * width := sorry

theorem tower_builder_asterisk_count
  {n width height : Nat}
  (h₁ : n > 0) 
  (h₂ : width > 0)
  (h₃ : height > 0)
  (floor : Nat)
  (h₄ : floor < n)
  (row : String)
  (h₅ : row ∈ List.drop (floor * height) (List.take ((floor + 1) * height) (towerBuilder n width height))) :
  (row.toList.filter (· = '*')).length = (2 * floor + 1) * width := sorry

theorem tower_builder_symmetry
  {n width height : Nat}
  (h₁ : n > 0)
  (h₂ : width > 0)
  (h₃ : height > 0)
  (row : String)
  (h₄ : row ∈ towerBuilder n width height) :
  row.toList = (row.toList.reverse) := sorry

theorem tower_builder_consistent_floor_rows
  {n width height : Nat}
  (h₁ : n > 0)
  (h₂ : width > 0)
  (h₃ : height > 0)
  (floor : Nat)
  (h₄ : floor < n)
  (row₁ row₂ : String)
  (h₅ : row₁ ∈ List.drop (floor * height) (List.take ((floor + 1) * height) (towerBuilder n width height)))
  (h₆ : row₂ ∈ List.drop (floor * height) (List.take ((floor + 1) * height) (towerBuilder n width height))) :
  row₁ = row₂ := sorry
-- </vc-theorems>