-- <vc-preamble>

def myMax (x y : Int) : Int :=
  if x ≥ y then x else y

def canFit (r1 r2 : Int × Int) (a b : Int) : Bool :=
  (r1.1 + r2.1 ≤ a ∧ myMax r1.2 r2.2 ≤ b) ∨ (myMax r1.1 r2.1 ≤ a ∧ r1.2 + r2.2 ≤ b)

def checkPairFunc (seal1 seal2 : Int × Int) (a b : Int) : Int :=
  let orientations := [(seal1, seal2), (seal1, (seal2.2, seal2.1)), ((seal1.2, seal1.1), seal2), ((seal1.2, seal1.1), (seal2.2, seal2.1))]
  
  let area0 := if canFit orientations[0]!.1 orientations[0]!.2 a b then
      orientations[0]!.1.1 * orientations[0]!.1.2 + orientations[0]!.2.1 * orientations[0]!.2.2
    else
      0
  
  let area1 := if canFit orientations[1]!.1 orientations[1]!.2 a b then
      orientations[1]!.1.1 * orientations[1]!.1.2 + orientations[1]!.2.1 * orientations[1]!.2.2
    else
      0
  
  let area2 := if canFit orientations[2]!.1 orientations[2]!.2 a b then
      orientations[2]!.1.1 * orientations[2]!.1.2 + orientations[2]!.2.1 * orientations[2]!.2.2
    else
      0
  
  let area3 := if canFit orientations[3]!.1 orientations[3]!.2 a b then
      orientations[3]!.1.1 * orientations[3]!.1.2 + orientations[3]!.2.1 * orientations[3]!.2.2
    else
      0
  
  myMax (myMax area0 area1) (myMax area2 area3)

@[reducible, simp]
def solve_precond (n a b : Int) (seals : List (Int × Int)) : Prop :=
  n ≥ 0 ∧ a ≥ 1 ∧ b ≥ 1 ∧ seals.length = n.natAbs ∧ ∀ i, 0 ≤ i ∧ i < n → (seals[i.natAbs]!).1 ≥ 1 ∧ (seals[i.natAbs]!).2 ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n a b : Int) (seals : List (Int × Int)) (h_precond : solve_precond n a b seals) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n a b : Int) (seals : List (Int × Int)) (result : Int) (h_precond : solve_precond n a b seals) : Prop :=
  result ≥ 0 ∧ 
  (result = 0 → (∀ i j, 0 ≤ i ∧ i < n ∧ i < j ∧ j < n → checkPairFunc (seals[i.natAbs]!) (seals[j.natAbs]!) a b = 0)) ∧
  (result > 0 → (∃ i j, 0 ≤ i ∧ i < n ∧ i < j ∧ j < n ∧ checkPairFunc (seals[i.natAbs]!) (seals[j.natAbs]!) a b = result)) ∧
  (∀ i j, 0 ≤ i ∧ i < n ∧ i < j ∧ j < n → checkPairFunc (seals[i.natAbs]!) (seals[j.natAbs]!) a b ≤ result)

theorem solve_spec_satisfied (n a b : Int) (seals : List (Int × Int)) (h_precond : solve_precond n a b seals) :
    solve_postcond n a b seals (solve n a b seals h_precond) h_precond := by
  sorry
-- </vc-theorems>