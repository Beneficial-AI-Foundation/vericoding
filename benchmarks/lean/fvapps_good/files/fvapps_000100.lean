-- <vc-preamble>
def abs (x : Int) : Int :=
  if x ≥ 0 then x else -x

def maximum (x y : Int) : Int :=
  if x ≥ y then x else y
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def time_without_coverage (a b c r : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem time_without_coverage_nonneg 
  (a b c : Int) (r : Nat) :
  time_without_coverage a b c r ≥ 0 := 
  sorry

theorem time_without_coverage_symmetric
  (a b c : Int) (r : Nat) :
  time_without_coverage a b c r = time_without_coverage b a c r :=
  sorry
-- </vc-theorems>