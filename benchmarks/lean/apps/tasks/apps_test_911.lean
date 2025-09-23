-- <vc-preamble>
def sum (l : List Int) : Int :=
  l.foldl (· + ·) 0

def ValidInput (n : Int) (c : Int) (P : List Int) (T : List Int) : Prop :=
  n > 0 ∧ c > 0 ∧ P.length = n.natAbs ∧ T.length = n.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < n → P[i.natAbs]! > 0) ∧
  (∀ i, 0 ≤ i ∧ i < n → T[i.natAbs]! > 0) ∧
  (∀ i, 0 ≤ i ∧ i < n-1 → P[i.natAbs]! < P[(i+1).natAbs]!) ∧
  (∀ i, 0 ≤ i ∧ i < n-1 → T[i.natAbs]! < T[(i+1).natAbs]!)

def calculateLimakScoreHelper (remaining : Int) (c : Int) (P : List Int) (T : List Int) (prevTime : Int) : Int :=
  if remaining ≥ 0 ∧ P.length = remaining.natAbs ∧ T.length = remaining.natAbs then
    if remaining = 0 then 0
    else 
      let cumulativeTime := prevTime + T[0]!
      let score := if P[0]! - c * cumulativeTime > 0 then P[0]! - c * cumulativeTime else 0
      score + calculateLimakScoreHelper (remaining-1) c (P.drop 1) (T.drop 1) cumulativeTime
  else 0
termination_by remaining.natAbs

def calculateLimakScore (n : Int) (c : Int) (P : List Int) (T : List Int) : Int :=
  if n > 0 ∧ P.length = n.natAbs ∧ T.length = n.natAbs then
    if n = 0 then 0
    else 
      let cumulativeTime := sum (T.take 1)
      let score := if P[0]! - c * cumulativeTime > 0 then P[0]! - c * cumulativeTime else 0
      score + calculateLimakScoreHelper (n-1) c (P.drop 1) (T.drop 1) cumulativeTime
  else 0

def calculateRadewooshScoreHelper (remaining : Int) (c : Int) (P : List Int) (T : List Int) (prevTime : Int) : Int :=
  if remaining ≥ 0 ∧ P.length ≥ remaining.natAbs ∧ T.length ≥ remaining.natAbs then
    if remaining = 0 then 0
    else 
      let idx := remaining - 1
      let cumulativeTime := prevTime + T[idx.natAbs]!
      let score := if P[idx.natAbs]! - c * cumulativeTime > 0 then P[idx.natAbs]! - c * cumulativeTime else 0
      score + calculateRadewooshScoreHelper (remaining-1) c P T cumulativeTime
  else 0
termination_by remaining.natAbs

def calculateRadewooshScore (n : Int) (c : Int) (P : List Int) (T : List Int) : Int :=
  if n > 0 ∧ P.length = n.natAbs ∧ T.length = n.natAbs then
    calculateRadewooshScoreHelper n c P T 0
  else 0

@[reducible, simp]
def solve_precond (n : Int) (c : Int) (P : List Int) (T : List Int) : Prop :=
  ValidInput n c P T
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (c : Int) (P : List Int) (T : List Int) (h_precond : solve_precond n c P T) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (c : Int) (P : List Int) (T : List Int) (result : String) (h_precond : solve_precond n c P T) : Prop :=
  (result = "Limak" ∨ result = "Radewoosh" ∨ result = "Tie") ∧
  (let limakScore := calculateLimakScore n c P T
   let radewooshScore := calculateRadewooshScore n c P T
   (result = "Limak" ↔ limakScore > radewooshScore) ∧
   (result = "Radewoosh" ↔ limakScore < radewooshScore) ∧
   (result = "Tie" ↔ limakScore = radewooshScore))

theorem solve_spec_satisfied (n : Int) (c : Int) (P : List Int) (T : List Int) (h_precond : solve_precond n c P T) :
    solve_postcond n c P T (solve n c P T h_precond) h_precond := by
  sorry
-- </vc-theorems>