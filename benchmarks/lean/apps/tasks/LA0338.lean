-- <vc-preamble>

def ValidInput (n m d : Int) (matrix : List (List Int)) : Prop :=
  n > 0 ∧ m > 0 ∧ d > 0 ∧
  matrix.length = Int.natAbs n ∧
  (∀ i, 0 ≤ i ∧ i < n → (matrix[Int.natAbs i]!).length = Int.natAbs m) ∧
  (∀ i j, 0 ≤ i ∧ i < n ∧ 0 ≤ j ∧ j < m → (matrix[Int.natAbs i]!)[Int.natAbs j]! > 0)

def AllSameRemainder (matrix : List (List Int)) (d : Int) : Prop :=
  ValidInput matrix.length (if matrix.length > 0 then (matrix[0]!).length else 0) d matrix →
  ∀ i j k l, 0 ≤ i ∧ i < matrix.length ∧ 0 ≤ j ∧ j < (matrix[0]!).length ∧
             0 ≤ k ∧ k < matrix.length ∧ 0 ≤ l ∧ l < (matrix[0]!).length →
    (matrix[Int.natAbs i]!)[Int.natAbs j]! % d = (matrix[Int.natAbs k]!)[Int.natAbs l]! % d

def flatten : List (List Int) → List Int
  | [] => []
  | h :: t => h ++ flatten t

def divideSequenceByD : List Int → Int → List Int
  | [], _ => []
  | h :: t, d => [h / d] ++ divideSequenceByD t d

def sumAbsDifferencesFromTarget : List Int → Int → Int
  | [], _ => 0
  | h :: t, target => Int.natAbs (h - target) + sumAbsDifferencesFromTarget t target

def seqMin (s : List Int) : Int :=
  match s with
  | [] => 0
  | h :: _ => s.foldl min h

def seqMax (s : List Int) : Int :=
  match s with
  | [] => 0
  | h :: _ => s.foldl max h

def minOpsInRange (simplified : List Int) (minVal maxVal : Int) : Int :=
  let range := List.range (Int.natAbs (maxVal - minVal) + 1)
  let results := range.map (fun i => sumAbsDifferencesFromTarget simplified (minVal + Int.ofNat i))
  results.foldl min (sumAbsDifferencesFromTarget simplified minVal)

def minimumOperationsToMakeEqual (simplified : List Int) : Int :=
  if simplified.length > 0 then
    let minVal := seqMin simplified
    let maxVal := seqMax simplified
    minOpsInRange simplified minVal maxVal
  else 0

@[reducible, simp]
def solve_precond (n m d : Int) (matrix : List (List Int)) : Prop :=
  ValidInput n m d matrix
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m d : Int) (matrix : List (List Int)) (h_precond : solve_precond n m d matrix) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m d : Int) (matrix : List (List Int)) (result : Int) (h_precond : solve_precond n m d matrix) : Prop :=
  (result = -1 ↔ ¬AllSameRemainder matrix d) ∧
  (result ≥ 0 → AllSameRemainder matrix d) ∧
  (result ≥ 0 → 
    let flat := flatten matrix
    let simplified := divideSequenceByD flat d
    result = minimumOperationsToMakeEqual simplified)

theorem solve_spec_satisfied (n m d : Int) (matrix : List (List Int)) (h_precond : solve_precond n m d matrix) :
    solve_postcond n m d matrix (solve n m d matrix h_precond) h_precond := by
  sorry
-- </vc-theorems>