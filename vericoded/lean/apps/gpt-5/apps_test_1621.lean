import Mathlib
-- <vc-preamble>
partial def stringValue (s : String) (w : List Int) : Int :=
  if s.length = 0 then 0
  else
    let charIndex := (s.data.getLast!).toNat - 'a'.toNat
    stringValue (s.dropRight 1) w + Int.ofNat s.length * w[charIndex]!

partial def appendValue (startPos : Int) (count : Int) (maxVal : Int) : Int :=
  if count = 0 then 0
  else (startPos + count) * maxVal + appendValue startPos (count - 1) maxVal

partial def maxValue (w : List Int) : Int :=
  if w.length = 1 then w[0]!
  else if w[0]! ≥ maxValue w.tail then w[0]!
  else maxValue w.tail

def ValidInput (s : String) (k : Int) (w : List Int) : Prop :=
  w.length = 26 ∧ 
  k ≥ 0 ∧ 
  Int.ofNat s.length ≤ 1000 ∧ 
  k ≤ 1000 ∧ 
  (∀ i, 0 ≤ i ∧ i < w.length → 0 ≤ w[i]! ∧ w[i]! ≤ 1000) ∧
  (∀ i, 0 ≤ i ∧ i < Int.ofNat s.length → 'a' ≤ s.data[i.natAbs]! ∧ s.data[i.natAbs]! ≤ 'z')

@[reducible, simp]
def solve_precond (s : String) (k : Int) (w : List Int) : Prop :=
  ValidInput s k w
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (k : Int) (w : List Int) (h_precond : solve_precond s k w) : Int :=
  stringValue s w + appendValue (Int.ofNat s.length) k (maxValue w)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (k : Int) (w : List Int) (result : Int) (h_precond : solve_precond s k w) : Prop :=
  result = stringValue s w + appendValue (Int.ofNat s.length) k (maxValue w)

theorem solve_spec_satisfied (s : String) (k : Int) (w : List Int) (h_precond : solve_precond s k w) :
    solve_postcond s k w (solve s k w h_precond) h_precond := by
  simp [solve_postcond, solve]
-- </vc-theorems>
