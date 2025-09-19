-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def matrixBlockSum (matrix : List (List Int)) (k : Nat) : List (List Int) := sorry

def sumList (l : List Int) : Int := match l with
  | [] => 0
  | x :: xs => x + sumList xs
-- </vc-definitions>

-- <vc-theorems>
theorem output_dimensions 
  (matrix : List (List Int)) (k : Nat)
  (h1 : 0 < matrix.length) 
  (h2 : ∀ row ∈ matrix, row.length = matrix.head!.length) :
  let result := matrixBlockSum matrix k
  (result.length = matrix.length) ∧
  (∀ row ∈ result, row.length = matrix.head!.length) := sorry

theorem k_large_sums_similar 
  (matrix : List (List Int)) (k : Nat)
  (h1 : k ≥ matrix.length - 1)
  (h2 : k ≥ matrix.head!.length - 1)
  (h3 : 0 < matrix.length)
  (h4 : ∀ row ∈ matrix, row.length = matrix.head!.length) :
  let result := matrixBlockSum matrix k
  let firstVal := result.head!.head!
  let maxDiff := sumList (matrix.map (λ row => sumList (row.map (λ x => Int.natAbs x))))
  ∀ row ∈ result, ∀ x ∈ row, Int.natAbs (x - firstVal) ≤ maxDiff := sorry

theorem symmetry
  (matrix : List (List Int)) (k : Nat)
  (h1 : 0 < matrix.length)
  (h2 : ∀ row ∈ matrix, row.length = matrix.head!.length) :
  let result := matrixBlockSum matrix k
  let m := matrix.length
  let n := matrix.head!.length
  let totalAbsSum := sumList (matrix.map (λ row => sumList (row.map (λ x => Int.natAbs x))))
  ∀ i < m, ∀ j < n,
    let mirror_i := m - 1 - i
    let mirror_j := n - 1 - j
    (0 ≤ mirror_i ∧ mirror_i < m ∧ 0 ≤ mirror_j ∧ mirror_j < n) →
    Int.natAbs (result[i]![j]! - result[mirror_i]![mirror_j]!) ≤ totalAbsSum := sorry
-- </vc-theorems>