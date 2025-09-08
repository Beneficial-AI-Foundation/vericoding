/-
In a warehouse, there is a row of barcodes, where the i-th barcode is barcodes[i].
Rearrange the barcodes so that no two adjacent barcodes are equal.  You may return any answer, and it is guaranteed an answer exists.

Example 1:
Input: [1,1,1,2,2,2]
Output: [2,1,2,1,2,1]

Example 2:
Input: [1,1,1,1,2,2,3,3]
Output: [1,3,1,3,2,1,2,1]

Note:

1 <= barcodes.length <= 10000
1 <= barcodes[i] <= 10000
-/

-- <vc-helpers>
-- </vc-helpers>

def rearrange_barcodes (barcodes: List Int) : List Int := sorry

def validate_solution (barcodes: List Int) : Bool := sorry

theorem single_element {n : Int} : 
  rearrange_barcodes [n] = [n] := sorry

theorem unique_elements_length {xs : List Int} (h: xs.length ≥ 2) :
  (rearrange_barcodes xs).length = xs.length := sorry

theorem unique_elements_same_elements {xs ys : List Int} (h: xs.length ≥ 2) :
  (rearrange_barcodes xs = ys) → List.length xs = List.length ys ∧ 
  ∀ (x : Int), List.contains xs x = List.contains ys x := sorry

theorem unique_elements_valid {xs : List Int} (h: xs.length ≥ 2) :
  validate_solution (rearrange_barcodes xs) = true := sorry

-- Apps difficulty: interview
-- Assurance level: guarded