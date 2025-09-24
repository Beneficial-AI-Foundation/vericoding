-- <vc-preamble>
def ValidInput (n : Int) (x : Int) (edges : List (Int × Int)) : Prop :=
  n > 0 ∧ 1 ≤ x ∧ x ≤ n ∧ edges.length = Int.natAbs (n - 1) ∧
  ∀ e ∈ edges, 0 ≤ e.1 ∧ e.1 < n ∧ 0 ≤ e.2 ∧ e.2 < n

def ValidDistances (wayA : List Int) (wayB : List Int) (n : Int) (x : Int) : Prop :=
  wayA.length = Int.natAbs n ∧ wayB.length = Int.natAbs n ∧ n > 0 ∧ 1 ≤ x ∧ x ≤ n ∧
  (wayA.length > 0 → wayA[0]! = 0) ∧ 
  (wayB.length > Int.natAbs (x-1) ∧ Int.natAbs (x-1) < wayB.length → wayB[Int.natAbs (x-1)]! = 0) ∧
  ∀ i, 0 ≤ i ∧ i < n → (Int.natAbs i < wayA.length → wayA[Int.natAbs i]! ≥ 0) ∧ (Int.natAbs i < wayB.length → wayB[Int.natAbs i]! ≥ 0)

def IsLeafNode (i : Int) (edges : List (Int × Int)) (n : Int) : Prop := True

def NoDuplicates (leaves : List Int) : Prop := leaves.Nodup

def ValidLeaves (leaves : List Int) (edges : List (Int × Int)) (n : Int) : Prop :=
  ValidInput n 1 edges →
  (∀ i, 0 ≤ i ∧ Int.natAbs i < leaves.length → 0 ≤ leaves[Int.natAbs i]! ∧ leaves[Int.natAbs i]! < n) ∧
  (∀ i, 0 ≤ i ∧ Int.natAbs i < leaves.length → IsLeafNode (leaves[Int.natAbs i]!) edges n) ∧
  (∀ i, 0 ≤ i ∧ i < n → IsLeafNode i edges n → i ∈ leaves) ∧
  NoDuplicates leaves

def ComputeOptimalMoves (wayA : List Int) (wayB : List Int) (leaves : List Int) (x : Int) : Int := 0

def OptimalMoves (wayA : List Int) (wayB : List Int) (leaves : List Int) (x : Int) : Int :=
  2 * ComputeOptimalMoves wayA wayB leaves (x-1)

@[reducible, simp]
def solve_precond (n : Int) (x : Int) (edges : List (Int × Int)) (leaves : List Int) (wayA : List Int) (wayB : List Int) : Prop :=
  ValidInput n x edges ∧
  ValidDistances wayA wayB n x ∧
  ValidLeaves leaves edges n ∧
  ∀ i, 0 ≤ i ∧ Int.natAbs i < leaves.length → 0 ≤ leaves[Int.natAbs i]! ∧ Int.natAbs (leaves[Int.natAbs i]!) < wayA.length ∧ 0 ≤ leaves[Int.natAbs i]! ∧ Int.natAbs (leaves[Int.natAbs i]!) < wayB.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (x : Int) (edges : List (Int × Int)) (leaves : List Int) (wayA : List Int) (wayB : List Int) (h_precond : solve_precond n x edges leaves wayA wayB) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (x : Int) (edges : List (Int × Int)) (leaves : List Int) (wayA : List Int) (wayB : List Int) (result : Int) (h_precond : solve_precond n x edges leaves wayA wayB) : Prop :=
  result ≥ 0 ∧
  result = OptimalMoves wayA wayB leaves x ∧
  result % 2 = 0 ∧
  (Int.natAbs (x-1) < wayA.length → result ≥ 2 * wayA[Int.natAbs (x-1)]!)

theorem solve_spec_satisfied (n : Int) (x : Int) (edges : List (Int × Int)) (leaves : List Int) (wayA : List Int) (wayB : List Int) (h_precond : solve_precond n x edges leaves wayA wayB) :
    solve_postcond n x edges leaves wayA wayB (solve n x edges leaves wayA wayB h_precond) h_precond := by
  sorry
-- </vc-theorems>