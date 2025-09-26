-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getValue (s : SubrectangleQueries) (i j : Nat) : Int := sorry

def updateSubrectangle (s : SubrectangleQueries) (row1 col1 row2 col2 : Nat) (newValue : Int) : Unit := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem initial_rectangle_values (rectangle : List (List Int)) (i j : Nat)
  (h1 : i < rectangle.length)
  (h2 : j < (rectangle.head!).length)
  (h3 : rectangle.length > 0)
  (h4 : (rectangle.head!).length > 0) :
  getValue { rectangle := rectangle } i j = (rectangle.get! i).get! j := sorry

theorem update_covers_entire_rectangle (rectangle : List (List Int)) (testVal : Int)
  (h1 : rectangle.length > 0)
  (h2 : (rectangle.head!).length > 0) :
  let s := { rectangle := rectangle }
  let rows := rectangle.length
  let cols := (rectangle.head!).length
  let _ := updateSubrectangle s 0 0 (rows - 1) (cols - 1) testVal
  ∀ i j, i < rows → j < cols →
    getValue s i j = testVal := sorry

theorem multiple_updates_overlap (rectangle : List (List Int))
  (h1 : rectangle.length > 0)
  (h2 : (rectangle.head!).length > 0) :
  let s := { rectangle := rectangle }
  let rows := rectangle.length
  let cols := (rectangle.head!).length
  let _ := updateSubrectangle s 0 0 (rows - 1) (cols - 1) 10
  let _ := updateSubrectangle s 0 0 (rows / 2) (cols / 2) 20
  let _ := updateSubrectangle s (rows / 2) (cols / 2) (rows - 1) (cols - 1) 30
  ∀ i j, i ≥ rows / 2 → i < rows → j ≥ cols / 2 → j < cols →
    getValue s i j = 30 := sorry

theorem sequential_same_region_updates (rectangle : List (List Int)) (updates : List Int)
  (h1 : rectangle.length > 0)
  (h2 : (rectangle.head!).length > 0)
  (h3 : updates.length > 0) :
  let s := { rectangle := rectangle }
  let rows := rectangle.length
  let cols := (rectangle.head!).length
  ∀ val ∈ updates, ∀ i j,
    let _ := updateSubrectangle s 0 0 (rows - 1) (cols - 1) val
    i < rows → j < cols →
      getValue s i j = val := sorry
-- </vc-theorems>