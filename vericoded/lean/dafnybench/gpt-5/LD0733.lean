import Mathlib
-- <vc-preamble>
def IsUpperCase (c : Char) : Bool :=
65 ≤ c.toNat ∧ c.toNat ≤ 90
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No additional helpers are required for this development.
-- </vc-helpers>

-- <vc-definitions>
def CountUppercase (s : String) : Int :=
Int.ofNat ((s.toList.filterMap (fun c => if IsUpperCase c then some c else none)).length)
-- </vc-definitions>

-- <vc-theorems>
theorem CountUppercase_spec (s : String) :
let count := CountUppercase s
count ≥ 0 ∧
count = (s.toList.filterMap (fun c => if IsUpperCase c then some c else none)).length
:=
by
  constructor
  · simpa [CountUppercase] using Int.ofNat_nonneg ((s.toList.filterMap (fun c => if IsUpperCase c then some c else none)).length)
  · simp [CountUppercase]
-- </vc-theorems>
