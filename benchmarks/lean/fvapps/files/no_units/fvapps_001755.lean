-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rearrange_barcodes (barcodes: List Int) : List Int := sorry

def validate_solution (barcodes: List Int) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element {n : Int} : 
  rearrange_barcodes [n] = [n] := sorry

theorem unique_elements_length {xs : List Int} (h: xs.length ≥ 2) :
  (rearrange_barcodes xs).length = xs.length := sorry

theorem unique_elements_same_elements {xs ys : List Int} (h: xs.length ≥ 2) :
  (rearrange_barcodes xs = ys) → List.length xs = List.length ys ∧ 
  ∀ (x : Int), List.contains xs x = List.contains ys x := sorry

theorem unique_elements_valid {xs : List Int} (h: xs.length ≥ 2) :
  validate_solution (rearrange_barcodes xs) = true := sorry
-- </vc-theorems>