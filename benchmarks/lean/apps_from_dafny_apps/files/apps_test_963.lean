-- <vc-preamble>
-- <vc-preamble>
@[reducible, simp]
def ValidInput (N K : Int) (segments : List (Int × Int)) : Prop :=
  N ≥ 2 ∧
  K ≥ 1 ∧
  segments.length = K.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < K → (segments[i.natAbs]!).1 ≥ 1 ∧ (segments[i.natAbs]!).2 ≤ N ∧ (segments[i.natAbs]!).1 ≤ (segments[i.natAbs]!).2) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < K → (segments[i.natAbs]!).2 < (segments[j.natAbs]!).1 ∨ (segments[j.natAbs]!).2 < (segments[i.natAbs]!).1)

def computeSegmentContributions (pos K : Int) (segments : List (Int × Int)) (prefixSum : Int → Int) (segIndex acc : Int) : Int := sorry

def computeWaysDPHelper (N K : Int) (segments : List (Int × Int)) (dp prefixSum : Int → Int) (pos : Int) : Int := sorry

def computeWaysDP (N K : Int) (segments : List (Int × Int)) : Int := sorry

@[reducible, simp]
def solve_precond (N K : Int) (segments : List (Int × Int)) : Prop :=
  ValidInput N K segments
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (N K : Int) (segments : List (Int × Int)) (h_precond : solve_precond N K segments) : Int :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N K : Int) (segments : List (Int × Int)) (result : Int) (h_precond : solve_precond N K segments) : Prop :=
  0 ≤ result ∧ result < 998244353 ∧ result = computeWaysDP N K segments

theorem solve_spec_satisfied (N K : Int) (segments : List (Int × Int)) (h_precond : solve_precond N K segments) :
    solve_postcond N K segments (solve N K segments h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>
