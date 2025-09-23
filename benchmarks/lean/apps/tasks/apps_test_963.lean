-- <vc-preamble>
@[reducible, simp]
def ValidInput (N : Int) (K : Int) (segments : List (Int × Int)) : Prop :=
  N ≥ 2 ∧
  K ≥ 1 ∧
  segments.length = K ∧
  (∀ i, 0 ≤ i ∧ i < K → (segments[i.natAbs]!).1 ≥ 1 ∧ (segments[i.natAbs]!).2 ≤ N ∧ (segments[i.natAbs]!).1 ≤ (segments[i.natAbs]!).2) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < K → (segments[i.natAbs]!).2 < (segments[j.natAbs]!).1 ∨ (segments[j.natAbs]!).2 < (segments[i.natAbs]!).1)

partial def computeSegmentContributions (pos : Int) (K : Int) (segments : List (Int × Int)) (prefixSum : Int → Int) (segIndex : Int) (acc : Int) : Int :=
  if segIndex ≥ K then 
    acc
  else
    let start := (segments[segIndex.natAbs]!).1
    let end_val := (segments[segIndex.natAbs]!).2
    let i_s := if pos - start ≥ 0 then pos - start else 0
    let i_e := if pos - end_val - 1 ≥ 0 then pos - end_val - 1 else 0
    let contribution := (prefixSum i_s - prefixSum i_e + 998244353) % 998244353
    let newAcc := (acc + contribution) % 998244353
    computeSegmentContributions pos K segments prefixSum (segIndex + 1) newAcc

partial def computeWaysDPHelper (N : Int) (K : Int) (segments : List (Int × Int)) (dp : Int → Int) (prefixSum : Int → Int) (pos : Int) : Int :=
  if pos > N then 
    dp N % 998244353
  else
    let newDpVal := computeSegmentContributions pos K segments prefixSum 0 0
    let newPrefixSumVal := (prefixSum (pos-1) + newDpVal) % 998244353
    let updatedDP := fun i => if i = pos then newDpVal else dp i
    let updatedPrefixSum := fun i => if i = pos then newPrefixSumVal else prefixSum i
    computeWaysDPHelper N K segments updatedDP updatedPrefixSum (pos + 1)

def computeWaysDP (N : Int) (K : Int) (segments : List (Int × Int)) : Int :=
  let dp := fun i => if i = 1 then 1 else 0
  let prefixSum := fun i => if i = 1 then 1 else 0
  computeWaysDPHelper N K segments dp prefixSum 2

@[reducible, simp]
def solve_precond (N : Int) (K : Int) (segments : List (Int × Int)) : Prop :=
  ValidInput N K segments
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (K : Int) (segments : List (Int × Int)) (h_precond : solve_precond N K segments) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (K : Int) (segments : List (Int × Int)) (result : Int) (h_precond : solve_precond N K segments) : Prop :=
  0 ≤ result ∧ result < 998244353 ∧ result = computeWaysDP N K segments

theorem solve_spec_satisfied (N : Int) (K : Int) (segments : List (Int × Int)) (h_precond : solve_precond N K segments) :
    solve_postcond N K segments (solve N K segments h_precond) h_precond := by
  sorry
-- </vc-theorems>