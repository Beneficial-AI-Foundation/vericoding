-- <vc-preamble>
def stringValue (s : String) (w : List Int) : Int := sorry

def appendValue (startPos count : Int) (maxVal : Int) : Int := sorry

def maxValue (w : List Int) : Int := sorry

def ValidInput (s : String) (k : Int) (w : List Int) : Prop :=
  w.length = 26 ∧ 
  k ≥ 0 ∧ 
  s.length ≤ 1000 ∧ 
  k ≤ 1000 ∧ 
  (∀ i, 0 ≤ i ∧ i < w.length → 0 ≤ w[i]! ∧ w[i]! ≤ 1000) ∧
  (∀ i, 0 ≤ i ∧ i < s.length → 'a' ≤ s.data[i]! ∧ s.data[i]! ≤ 'z')

@[reducible, simp]
def solve_precond (s : String) (k : Int) (w : List Int) : Prop :=
  ValidInput s k w
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (k : Int) (w : List Int) (h_precond : solve_precond s k w) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (k : Int) (w : List Int) (result: Int) (h_precond : solve_precond s k w) : Prop :=
  result = stringValue s w + appendValue s.length k (maxValue w)

theorem solve_spec_satisfied (s : String) (k : Int) (w : List Int) (h_precond : solve_precond s k w) :
    solve_postcond s k w (solve s k w h_precond) h_precond := by
  sorry
-- </vc-theorems>
