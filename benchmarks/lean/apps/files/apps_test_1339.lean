-- <vc-preamble>
def ValidInput (n : Int) (segments : List (Int × Int)) : Prop :=
  n ≥ 1 ∧ segments.length = Int.natAbs n ∧ 
  ∀ i, 0 ≤ i ∧ i < n → (segments[Int.natAbs i]!).1 ≤ (segments[Int.natAbs i]!).2

def CoversAll (segments : List (Int × Int)) (idx : Int) : Prop :=
  0 ≤ idx ∧ idx < segments.length ∧
  ∀ j, 0 ≤ j ∧ j < segments.length → 
      (segments[Int.natAbs idx]!).1 ≤ (segments[Int.natAbs j]!).1 ∧ (segments[Int.natAbs j]!).2 ≤ (segments[Int.natAbs idx]!).2

def HasMinLeftAndMaxRight (segments : List (Int × Int)) (idx : Int) : Prop :=
  0 ≤ idx ∧ idx < segments.length ∧
  (∀ j, 0 ≤ j ∧ j < segments.length → (segments[Int.natAbs idx]!).1 ≤ (segments[Int.natAbs j]!).1) ∧
  (∀ j, 0 ≤ j ∧ j < segments.length → (segments[Int.natAbs idx]!).2 ≥ (segments[Int.natAbs j]!).2)

def MinLeft (segments : List (Int × Int)) : Int :=
  if segments.length > 0 then
    segments.foldl (fun acc seg => min acc seg.1) (segments[0]!).1
  else 0

def MaxRight (segments : List (Int × Int)) : Int :=
  if segments.length > 0 then
    segments.foldl (fun acc seg => max acc seg.2) (segments[0]!).2
  else 0

@[reducible, simp]
def solve_precond (n : Int) (segments : List (Int × Int)) : Prop :=
  ValidInput n segments
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (segments : List (Int × Int)) (h_precond : solve_precond n segments) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (segments : List (Int × Int)) (result : Int) (h_precond : solve_precond n segments) : Prop :=
  (result = -1 ∨ (1 ≤ result ∧ result ≤ n)) ∧
  (result ≠ -1 → 
      (let idx := result - 1
       HasMinLeftAndMaxRight segments idx ∧
       CoversAll segments idx)) ∧
  (result = -1 → 
      ¬(∃ i, 0 ≤ i ∧ i < n ∧ HasMinLeftAndMaxRight segments i))

theorem solve_spec_satisfied (n : Int) (segments : List (Int × Int)) (h_precond : solve_precond n segments) :
    solve_postcond n segments (solve n segments h_precond) h_precond := by
  sorry
-- </vc-theorems>