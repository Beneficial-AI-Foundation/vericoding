-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Matrix (α : Type) := List (List α)

def avg_diags (matrix : Matrix Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_format {matrix : Matrix Int} :
  let result := avg_diags matrix
  List.length result = 2 ∧ 
  (∀ x ∈ result, x ≥ -1) := by
  sorry

theorem diagonal_selection {matrix : Matrix Int} :
  let n := List.length matrix
  let pos_vals := List.filterMap (fun i => 
    if i % 2 = 1 ∧ (matrix.get! i).get! i ≥ 0 
    then some ((matrix.get! i).get! i)
    else none) (List.range n)
  let neg_vals := List.filterMap (fun i =>
    if i % 2 = 0 ∧ (matrix.get! (n-i-1)).get! i < 0
    then some ((matrix.get! (n-i-1)).get! i)
    else none) (List.range n)
  (List.isEmpty pos_vals → (avg_diags matrix).get! 0 = -1) ∧
  (List.isEmpty neg_vals → (avg_diags matrix).get! 1 = -1) := by
  sorry

theorem three_by_three {matrix : Matrix Int} (h1 : List.length matrix = 3)
    (h2 : ∀ (i : Nat), i < matrix.length → List.length (matrix.get! i) = 3) :
  let result := avg_diags matrix
  ((matrix.get! 1).get! 1 ≥ 0 → result.get! 0 = (matrix.get! 1).get! 1) ∧
  ((matrix.get! 1).get! 1 < 0 → result.get! 0 = -1) ∧
  (let neg_vals := List.filterMap (fun x => if x < 0 then some x else none) 
    [(matrix.get! 0).get! 2, (matrix.get! 2).get! 0]
   if ¬ List.isEmpty neg_vals then
     result.get! 1 = Int.natAbs (neg_vals.foldr (· + ·) 0) / neg_vals.length
   else
     result.get! 1 = -1) := by
  sorry
-- </vc-theorems>