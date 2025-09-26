-- <vc-preamble>
def isValid (matrix : List (List String)) : Prop :=
  match matrix with
  | [] => True
  | h::t => ∀ row ∈ t, row.length = h.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maximalSquare (matrix : List (List String)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maximal_square_is_perfect_square (matrix : List (List String)) :
  ∃ n : Nat, maximalSquare matrix = n * n :=
sorry

theorem maximal_square_bounded (matrix : List (List String)) :
  match matrix with
  | [] => maximalSquare matrix = 0
  | h::t =>
    let result := maximalSquare matrix
    let maxDim := min matrix.length h.length
    0 ≤ result ∧ result ≤ maxDim * maxDim :=
sorry

theorem maximal_square_all_zeros (matrix : List (List String))
  (h₁ : matrix.length > 0)
  (h₂ : ∀ (i : Nat) (j : Nat), i < matrix.length →
        j < matrix.head!.length →
        (matrix.get! i).get! j = "0") :
  maximalSquare matrix = 0 :=
sorry

theorem maximal_square_all_ones (matrix : List (List String))
  (h₁ : matrix.length > 0)
  (h₂ : ∀ (i : Nat) (j : Nat), i < matrix.length →
        j < matrix.head!.length →
        (matrix.get! i).get! j = "1") :
  maximalSquare matrix = (min matrix.length matrix.head!.length) *
                        (min matrix.length matrix.head!.length) :=
sorry

theorem maximal_square_padding (matrix : List (List String))
  (h : matrix.length > 0) :
  let padRow := fun (row : List String) => "0" :: (row ++ ["0"])
  let paddedMatrix := (List.replicate (matrix.head!.length + 2) "0") ::
                      (matrix.map padRow) ++
                      [List.replicate (matrix.head!.length + 2) "0"]
  maximalSquare matrix = maximalSquare paddedMatrix :=
sorry
-- </vc-theorems>