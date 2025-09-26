import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Extract hundreds digit
def hundreds_digit (n : Int) : Int := n / 100

-- LLM HELPER: Extract tens digit
def tens_digit (n : Int) : Int := (n / 10) % 10

-- LLM HELPER: Extract units digit  
def units_digit (n : Int) : Int := n % 10

-- LLM HELPER: Cube function
def cube (x : Int) : Int := x * x * x
-- </vc-helpers>

-- <vc-definitions>
def IsArmstrong (n : Int) : Bool :=
decide (n = (n / 100) * (n / 100) * (n / 100) +
            ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) +
            (n % 10) * (n % 10) * (n % 10))
-- </vc-definitions>

-- <vc-theorems>
theorem IsArmstrong_spec (n : Int) :
100 ≤ n ∧ n < 1000 →
IsArmstrong n = (n = ((n / 100) * (n / 100) * (n / 100) +
((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) +
(n % 10) * (n % 10) * (n % 10))) :=
fun h => by simp [IsArmstrong]
-- </vc-theorems>
