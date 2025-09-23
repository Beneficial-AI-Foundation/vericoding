-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) : Bool :=
sorry

def stringReverse (s : String) : String :=
sorry

def getMismatches (s : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_distance_property (s : String)
    (h : s.length > 0)
    (h2 : ∀ c ∈ s.data, c = 'a' ∨ c = 'b' ∨ c = 'c') :
  let mismatches := getMismatches s
  solve s = (mismatches = 1 ∨ (mismatches = 0 ∧ s.length % 2 = 1)) :=
sorry

theorem solve_symmetry_property (s : String) (h : s.length > 0) :
  solve s = solve (stringReverse s) :=
sorry
-- </vc-theorems>