-- <vc-preamble>
def isSorted (s: List Int) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < s.length → s[i]! ≤ s[j]!

def allDistancesEqual (positions: List Int) : Bool :=
  if positions.length ≤ 2 then true
  else
    let firstDist := positions[1]! - positions[0]!
    List.range (positions.length - 2) |>.all (fun i => 
      positions[i + 2]! - positions[i + 1]! = firstDist)

def countVisits (visits: List Int) (stop: Int) : Int := 
  (visits.filter (· = stop)).length

def computeCounts (n: Int) (visits: List Int) : List Int := 
  if n ≤ 0 then []
  else 
    let nNat := n.toNat
    let baseCounts := List.range nNat |>.map (fun i => countVisits visits (↑i + 1))
    List.range nNat |>.map (fun i => 
      if i = 0 ∨ i = nNat - 1 then baseCounts[i]! * 2 
      else baseCounts[i]!)

def maxVal (s: List Int) : Int := 
  s.foldl max 0

def computeMaxRounds (counts: List Int) : Int :=
  if counts.length > 0 then
    maxVal (counts.map (fun x => x / 2))
  else 0

def hasAmbiguousPath (n: Int) (positions: List Int) (visits: List Int) : Bool :=
  if n < 2 then false
  else
    let counts := computeCounts n visits
    let maxRounds := computeMaxRounds counts
    let remainingCounts := counts.map (fun x => x - maxRounds * 2)
    let allZero := remainingCounts.all (· = 0)
    allZero && n > 2 && !allDistancesEqual positions

def sum (s: List Int) : Int := s.foldl (· + ·) 0

def calculateTotalDistance (n: Int) (positions: List Int) (visits: List Int) : Int := 
  let counts := computeCounts n visits
  let maxRounds := computeMaxRounds counts
  let remainingCounts := counts.map (fun x => x - maxRounds * 2)
  let allZero := remainingCounts.all (· = 0)
  if allZero then
    if n = 2 then
      maxRounds * (positions[1]! - positions[0]!) * 2 - (positions[1]! - positions[0]!)
    else
      let firstDist := positions[1]! - positions[0]!
      maxRounds * firstDist * 2 * (n - 1) - firstDist
  else
    let nNat := n.toNat
    let edgeDistance := sum (List.range (nNat - 1) |>.map (fun i => 
      min (remainingCounts[i]!) (remainingCounts[i + 1]!) * (positions[i + 1]! - positions[i]!)))
    let totalEdgeLength := sum (List.range (nNat - 1) |>.map (fun i => 
      positions[i + 1]! - positions[i]!))
    edgeDistance + maxRounds * 2 * totalEdgeLength

@[reducible, simp]
def solve_precond (n: Int) (positions: List Int) (m: Int) (visits: List Int) : Prop :=
  n ≥ 2 ∧
  positions.length = n.toNat ∧
  m ≥ 1 ∧
  visits.length = m.toNat ∧
  (∀ i, 0 ≤ i ∧ i < visits.length → 1 ≤ visits[i]! ∧ visits[i]! ≤ n) ∧
  (∀ i, 0 ≤ i ∧ i < n.toNat - 1 → positions[i]! < positions[i + 1]!) ∧
  (∀ i, 0 ≤ i ∧ i < positions.length → positions[i]! ≥ 1) ∧
  isSorted visits
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n: Int) (positions: List Int) (m: Int) (visits: List Int) (h_precond : solve_precond n positions m visits) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n: Int) (positions: List Int) (m: Int) (visits: List Int) (result: Int) (h_precond : solve_precond n positions m visits) : Prop :=
  result ≥ -1 ∧
  (result = -1 ↔ hasAmbiguousPath n positions visits) ∧
  (result ≥ 0 → result = calculateTotalDistance n positions visits) ∧
  (result ≥ 0 → (∀ i, 0 ≤ i ∧ i < n.toNat - 1 → positions[i + 1]! - positions[i]! > 0))

theorem solve_spec_satisfied (n: Int) (positions: List Int) (m: Int) (visits: List Int) (h_precond : solve_precond n positions m visits) :
    solve_postcond n positions m visits (solve n positions m visits h_precond) h_precond := by
  sorry
-- </vc-theorems>