-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def search_matrix (matrix : List (List Int)) (target : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_matrix_search : ∀ (target : Int),
  search_matrix [] target = false := by sorry

theorem empty_row_matrix_search : ∀ (target : Int),
  search_matrix [[]] target = false := by sorry

theorem matrix_contains_base_element : ∀ (m n base : Int),
  m > 0 → n > 0 →
  let matrix := List.map (fun i => 
    List.map (fun j => base + i + (j : Int)) 
      (List.map Int.ofNat (List.range (Int.toNat n))))
    (List.map Int.ofNat (List.range (Int.toNat m)))
  search_matrix matrix base = true := by sorry

theorem matrix_lacks_below_base : ∀ (m n base : Int),
  m > 0 → n > 0 →
  let matrix := List.map (fun i => 
    List.map (fun j => base + i + (j : Int))
      (List.map Int.ofNat (List.range (Int.toNat n))))
    (List.map Int.ofNat (List.range (Int.toNat m)))
  search_matrix matrix (base - 1) = false := by sorry

theorem single_element_present :
  search_matrix [[1]] 1 = true := by sorry

theorem single_element_absent :
  search_matrix [[1]] 0 = false := by sorry

theorem single_row_search :
  search_matrix [[1,2,3]] 2 = true := by sorry

theorem single_column_search :
  search_matrix [[1],[2],[3]] 2 = true := by sorry
-- </vc-theorems>