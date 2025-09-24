-- <vc-preamble>
def sumList : List Nat → Nat
  | [] => 0
  | x::xs => x + sumList xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxSizeSlices (slices: List Nat) : Nat :=
sorry

def maxList : List Nat → Nat
  | [] => 0
  | [x] => x
  | x::xs => Nat.max x (maxList xs)

def sortList : List Nat → List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_size_bounds {slices : List Nat}
  (h1: slices.length ≥ 3)
  (h2: ∀ x ∈ slices, x ≥ 1 ∧ x ≤ 100) :
  let result := maxSizeSlices slices
  result > 0 ∧
  result ≤ sumList slices ∧
  result ≥ maxList slices :=
sorry

theorem max_size_elements {slices : List Nat}
  (h1: slices.length ≥ 3)
  (h2: ∀ x ∈ slices, x ≥ 1 ∧ x ≤ 100) :
  let n := slices.length
  maxSizeSlices slices ≤ sumList (List.take (n/3) (sortList slices)) :=
sorry

theorem min_case_three {slices : List Nat}
  (h1: slices.length = 3)
  (h2: ∀ x ∈ slices, x ≥ 1 ∧ x ≤ 100) :
  maxSizeSlices slices = maxList slices :=
sorry
-- </vc-theorems>